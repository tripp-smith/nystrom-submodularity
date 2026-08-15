import NystromSubmodularity.PrincipalSubmatrix
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Star
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Stieltjes matrices

Colbrook Theorem 4, first half: Stieltjes matrices have entrywise-nonnegative
inverses (block induction), and an SDDM matrix plus a positive shift is
Stieltjes. The four-point inverse-trace argument lives in `InverseTrace.lean`.
-/

namespace NystromSubmodularity

open Finset
open scoped Matrix

/-! ## Principal submatrices of Stieltjes matrices -/

theorem IsStieltjes.submatrix {ι κ : Type*} [Fintype ι] {M : Matrix ι ι ℝ}
    (hM : IsStieltjes M) {e : κ → ι} (he : Function.Injective e) :
    IsStieltjes (M.submatrix e e) :=
  ⟨hM.posDef.submatrix he, fun _ _ hij => hM.offDiag_nonpos (he.ne hij)⟩

-- `open Matrix` is delayed until after the quadratic-form lemmas: Finset sum
-- lemmas share a type parameter `M` that otherwise collides with a matrix.

theorem IsStieltjes.principal {ι : Type*} [Fintype ι] {M : Matrix ι ι ℝ}
    (hM : IsStieltjes M) (T : Finset ι) :
    IsStieltjes (principalSubmatrix M T) :=
  hM.submatrix Subtype.val_injective

theorem IsStieltjes.reindex {ι κ : Type*} [Fintype ι] [Fintype κ] {M : Matrix ι ι ℝ}
    (hM : IsStieltjes M) (e : κ ≃ ι) :
    IsStieltjes (M.reindex e.symm e.symm) :=
  hM.submatrix e.injective

theorem IsStieltjes.toBlocks₁₁ {m n : Type*} [Fintype m] [Fintype n]
    {M : Matrix (m ⊕ n) (m ⊕ n) ℝ} (hM : IsStieltjes M) :
    IsStieltjes M.toBlocks₁₁ :=
  hM.submatrix Sum.inl_injective

theorem IsStieltjes.toBlocks₂₂ {m n : Type*} [Fintype m] [Fintype n]
    {M : Matrix (m ⊕ n) (m ⊕ n) ℝ} (hM : IsStieltjes M) :
    IsStieltjes M.toBlocks₂₂ :=
  hM.submatrix Sum.inr_injective

theorem IsStieltjes.toBlocks₁₂_nonpos {m n : Type*}
    {M : Matrix (m ⊕ n) (m ⊕ n) ℝ} (hM : IsStieltjes M) (i : m) (j : n) :
    M.toBlocks₁₂ i j ≤ 0 :=
  hM.offDiag_nonpos (by simp)

theorem IsStieltjes.of_posDef_subsingleton {ι : Type*} [Subsingleton ι]
    {M : Matrix ι ι ℝ} (hM : M.PosDef) : IsStieltjes M :=
  ⟨hM, fun i j hij => (hij (Subsingleton.elim i j)).elim⟩

theorem posDef_submatrix_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    {M : Matrix ι ι ℝ} (e : κ ≃ ι) :
    (M.submatrix e e).PosDef ↔ M.PosDef :=
  ⟨fun h => by simpa using h.submatrix e.symm.injective,
    fun h => h.submatrix e.injective⟩

/-! ## SDDM + positive shift is Stieltjes -/

theorem star_eq_self {ι : Type*} (x : ι → ℝ) : star x = x :=
  funext fun _ => star_trivial _

theorem dotProduct_mulVec_doubleSum {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (x : ι → ℝ) :
    x ⬝ᵥ (M *ᵥ x) = ∑ i, ∑ j, x i * M i j * x j := by
  simp [dotProduct, Matrix.mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem IsSDDM.abs_offDiag {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : IsSDDM M) {i j : ι} (hij : i ≠ j) :
    |M i j| = -(M i j) :=
  abs_of_nonpos (hM.offDiag_nonpos hij)

/-- Split a double sum into the diagonal plus the complementary `ite`. -/
lemma sum_split_diag {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → ι → ℝ) :
    (∑ i : ι, ∑ j : ι, g i j) =
      (∑ i : ι, g i i) +
        (∑ i : ι, ∑ j : ι, (if j = i then (0 : ℝ) else g i j)) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun (i : ι) _ => ?_
  have hsplit :
      (∑ j : ι, g i j) =
        (∑ j : ι, (if j = i then g i j else (0 : ℝ))) +
          (∑ j : ι, (if j = i then (0 : ℝ) else g i j)) := by
    rw [← Finset.sum_add_distrib (s := (univ : Finset ι))
      (f := fun j : ι => if j = i then g i j else (0 : ℝ))
      (g := fun j : ι => if j = i then (0 : ℝ) else g i j)]
    refine Finset.sum_congr rfl fun (j : ι) _ => ?_
    split_ifs <;> ring
  have hdiag : (∑ j : ι, (if j = i then g i j else (0 : ℝ))) = g i i := by
    simp [Finset.sum_ite_eq', mem_univ]
  rw [hsplit, hdiag]

lemma offDiag_sq_symm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ι → ℝ) (hw : ∀ a b, w a b = w b a) (x : ι → ℝ) :
    ∑ i, ∑ j, (if i = j then (0 : ℝ) else w i j * (x j * x j)) =
      ∑ i, ∑ j, (if i = j then (0 : ℝ) else w i j * (x i * x i)) := by
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : a = b
  · simp [h]
  · have h' : b ≠ a := Ne.symm h
    simp [h, h', hw a b]

/-- Nonnegativity of the SDDM quadratic form, via diagonal dominance and
`2xy ≤ x² + y²`. -/
theorem IsSDDM.quad_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Lsd : Matrix ι ι ℝ} (hL : IsSDDM Lsd) (x : ι → ℝ) :
    0 ≤ star x ⬝ᵥ (Lsd *ᵥ x) := by
  rw [star_eq_self, dotProduct_mulVec_doubleSum]
  have hsplit := sum_split_diag (fun i j => x i * Lsd i j * x j)
  rw [hsplit]
  have hdiag :
      (∑ i : ι, x i * Lsd i i * x i) = ∑ i : ι, Lsd i i * (x i * x i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hdiag]
  have hterm (i j : ι) :
      (if j = i then (0 : ℝ) else x i * Lsd i j * x j) =
        -(if j = i then (0 : ℝ) else |Lsd i j| * (x i * x j)) := by
    by_cases hij : j = i
    · simp [hij]
    · have hji : i ≠ j := Ne.symm hij
      have habs : |Lsd i j| = -(Lsd i j) := hL.abs_offDiag hji
      simp [hij, habs]
      ring
  simp_rw [hterm]
  simp only [Finset.sum_neg_distrib]
  have hxy : ∀ a b : ι, x a * x b ≤ (x a * x a + x b * x b) / 2 := by
    intro a b
    nlinarith [sq_nonneg (x a - x b)]
  have hsym : ∀ a b : ι, |Lsd a b| = |Lsd b a| := fun a b => by
    rw [hL.isSymm.apply a b]
  have hle :
      (∑ i : ι, ∑ j : ι, (if j = i then (0 : ℝ) else |Lsd i j| * (x i * x j))) ≤
        ∑ i : ι, ∑ j : ι, (if j = i then (0 : ℝ) else |Lsd i j| * ((x i * x i + x j * x j) / 2)) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
      by_cases hij : j = i
      · simp [hij]
      · simp [hij]
        exact mul_le_mul_of_nonneg_left (hxy i j) (abs_nonneg _)
  have hlin (y : ι → ℝ) :
      (∑ i : ι, ∑ j : ι, (if j = i then (0 : ℝ) else |Lsd i j| * ((y i * y i + y j * y j) / 2))) =
        (1 / 2) * ∑ i : ι, ∑ j : ι, (if j = i then (0 : ℝ) else |Lsd i j| * (y i * y i)) +
          (1 / 2) * ∑ i : ι, ∑ j : ι, (if j = i then (0 : ℝ) else |Lsd i j| * (y j * y j)) := by
    have hsummand (i j : ι) :
        (if j = i then (0 : ℝ) else |Lsd i j| * ((y i * y i + y j * y j) / 2)) =
          (1 / 2) * (if j = i then (0 : ℝ) else |Lsd i j| * (y i * y i)) +
            (1 / 2) * (if j = i then (0 : ℝ) else |Lsd i j| * (y j * y j)) := by
      split_ifs <;> ring
    simp_rw [hsummand, Finset.sum_add_distrib, Finset.mul_sum]
  have hjj :
      (∑ i : ι, ∑ j : ι, (if j = i then (0 : ℝ) else |Lsd i j| * (x j * x j))) =
        ∑ i : ι, ∑ j : ι, (if j = i then (0 : ℝ) else |Lsd i j| * (x i * x i)) := by
    have hflip (p q : ι) :
        (if q = p then (0 : ℝ) else |Lsd p q| * (x q * x q)) =
          if p = q then (0 : ℝ) else |Lsd p q| * (x q * x q) := by
      simp [eq_comm]
    have hflip' (p q : ι) :
        (if q = p then (0 : ℝ) else |Lsd p q| * (x p * x p)) =
          if p = q then (0 : ℝ) else |Lsd p q| * (x p * x p) := by
      simp [eq_comm]
    simp_rw [hflip, hflip', offDiag_sq_symm (fun a b => |Lsd a b|) hsym x]
  have hmul :
      (∑ i : ι, ∑ j : ι, (if j = i then (0 : ℝ) else |Lsd i j| * (x i * x i))) =
        ∑ i : ι, (∑ j : ι, (if j = i then (0 : ℝ) else |Lsd i j|)) * (x i * x i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hfactor (j : ι) :
        (if j = i then (0 : ℝ) else |Lsd i j| * (x i * x i)) =
          (if j = i then (0 : ℝ) else |Lsd i j|) * (x i * x i) := by
      split_ifs <;> ring
    simp_rw [hfactor]
    rw [Finset.sum_mul]
  have hexp :
      (∑ i : ι, ∑ j : ι, (if j = i then (0 : ℝ) else |Lsd i j| * ((x i * x i + x j * x j) / 2))) =
        ∑ i : ι, (∑ j : ι, (if j = i then (0 : ℝ) else |Lsd i j|)) * (x i * x i) := by
    rw [hlin x, hjj, hmul]
    ring
  have hdom :
      (∑ i : ι, (∑ j : ι, (if j = i then (0 : ℝ) else |Lsd i j|)) * (x i * x i)) ≤
        ∑ i : ι, Lsd i i * (x i * x i) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have hrow :
        (∑ j : ι, (if j = i then (0 : ℝ) else |Lsd i j|)) =
          ∑ j ∈ univ.erase i, |Lsd i j| := by
      have h0 : (fun j : ι => if j = i then (0 : ℝ) else |Lsd i j|) i = 0 := if_pos rfl
      rw [← Finset.sum_erase (s := (univ : Finset ι))
        (f := fun j : ι => if j = i then (0 : ℝ) else |Lsd i j|) h0]
      refine Finset.sum_congr rfl fun j hj => ?_
      have : j ≠ i := (mem_erase.mp hj).1
      simp [this]
    rw [hrow]
    exact mul_le_mul_of_nonneg_right (hL.isDiagDominant i) (mul_self_nonneg (x i))
  have hgoal :
      0 ≤ ∑ i : ι, Lsd i i * (x i * x i) -
        ∑ i : ι, ∑ j : ι, (if j = i then (0 : ℝ) else |Lsd i j| * (x i * x j)) := by
    nlinarith [hle, hexp, hdom]
  simpa [sub_eq_add_neg] using hgoal

theorem IsSDDM.posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Matrix ι ι ℝ} (hL : IsSDDM L) : L.PosSemidef :=
  Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((Matrix.isHermitian_iff_isSymm).mpr hL.isSymm) hL.quad_nonneg

theorem IsSDDM.add_pos_smul_one_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Matrix ι ι ℝ} (hL : IsSDDM L) {γ : ℝ} (hγ : 0 < γ) :
    (L + γ • (1 : Matrix ι ι ℝ)).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · rw [Matrix.isHermitian_iff_isSymm]
    exact hL.isSymm.add (Matrix.isSymm_one.smul γ)
  · intro x hx
    have hsum :
        star x ⬝ᵥ ((L + γ • 1) *ᵥ x) =
          star x ⬝ᵥ (L *ᵥ x) + γ * (star x ⬝ᵥ x) := by
      simp [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_add, dotProduct_smul]
    have hLterm : 0 ≤ star x ⬝ᵥ (L *ᵥ x) := hL.quad_nonneg x
    have hnorm : 0 < star x ⬝ᵥ x := by
      rw [star_eq_self]
      have : x ⬝ᵥ x = 0 ↔ x = 0 := dotProduct_self_eq_zero
      have hne : x ⬝ᵥ x ≠ 0 := this.not.mpr hx
      have hnn : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
      exact lt_of_le_of_ne hnn hne.symm
    rw [hsum]
    nlinarith

theorem IsSDDM.add_pos_smul_one_isStieltjes {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Matrix ι ι ℝ} (hL : IsSDDM L) {γ : ℝ} (hγ : 0 < γ) :
    IsStieltjes (L + γ • (1 : Matrix ι ι ℝ)) := by
  refine ⟨hL.add_pos_smul_one_posDef hγ, ?_⟩
  intro i j hij
  simp [Matrix.add_apply, Matrix.smul_apply, hij]
  exact hL.offDiag_nonpos hij

/-! ## Entrywise sign lemmas -/

open Matrix

theorem mul_entry_nonneg {l m n : Type*} [Fintype m]
    {A : Matrix l m ℝ} {B : Matrix m n ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) (i : l) (j : n) :
    0 ≤ (A * B) i j :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hA i k) (hB k j)

theorem mul_entry_nonpos_of_nonneg_nonpos {l m n : Type*} [Fintype m]
    {A : Matrix l m ℝ} {B : Matrix m n ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, B i j ≤ 0) (i : l) (j : n) :
    (A * B) i j ≤ 0 :=
  Finset.sum_nonpos fun k _ => mul_nonpos_of_nonneg_of_nonpos (hA i k) (hB k j)

theorem mul_entry_nonpos_of_nonpos_nonneg {l m n : Type*} [Fintype m]
    {A : Matrix l m ℝ} {B : Matrix m n ℝ}
    (hA : ∀ i j, A i j ≤ 0) (hB : ∀ i j, 0 ≤ B i j) (i : l) (j : n) :
    (A * B) i j ≤ 0 :=
  Finset.sum_nonpos fun k _ => mul_nonpos_of_nonpos_of_nonneg (hA i k) (hB k j)

theorem mul_entry_nonneg_of_nonpos {l m n : Type*} [Fintype m]
    {A : Matrix l m ℝ} {B : Matrix m n ℝ}
    (hA : ∀ i j, A i j ≤ 0) (hB : ∀ i j, B i j ≤ 0) (i : l) (j : n) :
    0 ≤ (A * B) i j :=
  Finset.sum_nonneg fun k _ => mul_nonneg_of_nonpos_of_nonpos (hA i k) (hB k j)

theorem add_entry_nonneg {l m : Type*} {A B : Matrix l m ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) (i : l) (j : m) :
    0 ≤ (A + B) i j :=
  add_nonneg (hA i j) (hB i j)

theorem neg_entry_nonneg_of_nonpos {l m : Type*} {A : Matrix l m ℝ}
    (hA : ∀ i j, A i j ≤ 0) (i : l) (j : m) :
    0 ≤ (-A) i j := by
  simpa using neg_nonneg.mpr (hA i j)

/-- The Schur complement of a positive-definite block matrix is positive definite. -/
theorem schurComplement_posDef {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    {A : Matrix m m ℝ} {B : Matrix m n ℝ} {D : Matrix n n ℝ}
    (hA : A.PosDef) (hM : (fromBlocks A B Bᴴ D).PosDef) :
    (D - Bᴴ * A⁻¹ * B).PosDef := by
  have := hA.isUnit.invertible
  have hHer : (D - Bᴴ * A⁻¹ * B).IsHermitian :=
    (IsHermitian.fromBlocks₁₁ B D hA.isHermitian).mp hM.isHermitian
  refine PosDef.of_dotProduct_mulVec_pos hHer ?_
  intro y hy
  have hx : Sum.elim (-((A⁻¹ * B) *ᵥ y)) y ≠ 0 := by
    intro h
    apply hy
    funext k
    simpa using congrArg (fun w => w (Sum.inr k)) h
  have hquad := hM.dotProduct_mulVec_pos hx
  rw [dotProduct_mulVec, schur_complement_eq₁₁ B D _ _ hA.isHermitian, neg_add_cancel,
    dotProduct_zero, zero_add, ← dotProduct_mulVec] at hquad
  exact hquad

/-! ## Inverse nonnegativity by block induction -/

theorem inv_fin_one_apply (S : Matrix (Fin 1) (Fin 1) ℝ) :
    S⁻¹ 0 0 = (S 0 0)⁻¹ := by
  rw [inv_subsingleton]
  simp [diagonal]

theorem inv_fin_one_nonneg {S : Matrix (Fin 1) (Fin 1) ℝ} (hS : S.PosDef)
    (i j : Fin 1) : 0 ≤ S⁻¹ i j := by
  have hi : i = 0 := Subsingleton.elim i 0
  have hj : j = 0 := Subsingleton.elim j 0
  subst hi; subst hj
  have hdiag : 0 < S 0 0 := hS.diag_pos
  rw [inv_fin_one_apply]
  exact inv_nonneg.mpr hdiag.le

theorem inv_fromBlocks₁₁_eq {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n m ℝ) (D : Matrix n n ℝ)
    (hA : IsUnit A) (hS : IsUnit (D - C * A⁻¹ * B))
    (hBlk : IsUnit (fromBlocks A B C D)) :
    (fromBlocks A B C D)⁻¹ =
      fromBlocks (A⁻¹ + A⁻¹ * B * (D - C * A⁻¹ * B)⁻¹ * C * A⁻¹)
        (-(A⁻¹ * B * (D - C * A⁻¹ * B)⁻¹))
        (-((D - C * A⁻¹ * B)⁻¹ * C * A⁻¹))
        (D - C * A⁻¹ * B)⁻¹ := by
  obtain ⟨_⟩ := hA.nonempty_invertible
  have hcongr : D - C * ⅟A * B = D - C * A⁻¹ * B := by
    simp [invOf_eq_nonsing_inv]
  have hS' : IsUnit (D - C * ⅟A * B) := by
    rwa [hcongr]
  obtain ⟨_⟩ := hS'.nonempty_invertible
  obtain ⟨_⟩ := hBlk.nonempty_invertible
  rw [← invOf_eq_nonsing_inv, invOf_fromBlocks₁₁_eq]
  simp [invOf_eq_nonsing_inv]

theorem inv_fromBlocks₂₂_eq {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n m ℝ) (D : Matrix n n ℝ)
    (hD : IsUnit D) (hS : IsUnit (A - B * D⁻¹ * C))
    (hBlk : IsUnit (fromBlocks A B C D)) :
    (fromBlocks A B C D)⁻¹ =
      fromBlocks (A - B * D⁻¹ * C)⁻¹
        (-((A - B * D⁻¹ * C)⁻¹ * B * D⁻¹))
        (-(D⁻¹ * C * (A - B * D⁻¹ * C)⁻¹))
        (D⁻¹ + D⁻¹ * C * (A - B * D⁻¹ * C)⁻¹ * B * D⁻¹) := by
  obtain ⟨_⟩ := hD.nonempty_invertible
  have hcongr : A - B * ⅟D * C = A - B * D⁻¹ * C := by
    simp [invOf_eq_nonsing_inv]
  have hS' : IsUnit (A - B * ⅟D * C) := by
    rwa [hcongr]
  obtain ⟨_⟩ := hS'.nonempty_invertible
  obtain ⟨_⟩ := hBlk.nonempty_invertible
  rw [← invOf_eq_nonsing_inv, invOf_fromBlocks₂₂_eq]
  simp [invOf_eq_nonsing_inv]

/-- Schur complement of the lower-right block of a positive-definite block matrix. -/
theorem schurComplement₂₂_posDef {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {A : Matrix m m ℝ} {B : Matrix m n ℝ} {D : Matrix n n ℝ}
    (hD : D.PosDef) (hM : (fromBlocks A B Bᴴ D).PosDef) :
    (A - B * D⁻¹ * Bᴴ).PosDef := by
  have hswap : (fromBlocks D Bᴴ B A).PosDef := by
    have hsub :
        fromBlocks D Bᴴ B A =
          (fromBlocks A B Bᴴ D).submatrix (Equiv.sumComm n m) (Equiv.sumComm n m) := by
      ext i j
      cases i <;> cases j <;> rfl
    rw [hsub]
    exact (posDef_submatrix_equiv (Equiv.sumComm n m)).mpr hM
  have := schurComplement_posDef (A := D) (B := Bᴴ) (D := A) hD hswap
  simpa [conjTranspose_conjTranspose] using this

theorem IsStieltjes.inv_nonneg_fin :
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
      IsStieltjes A → ∀ i j, 0 ≤ A⁻¹ i j := by
  intro n
  induction n with
  | zero =>
    intro _ _ i
    exact i.elim0
  | succ n ih =>
    intro A hA i j
    let e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv
    let Ab : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ := A.reindex e.symm e.symm
    have hAb : IsStieltjes Ab := hA.reindex e
    let A11 := Ab.toBlocks₁₁
    let B := Ab.toBlocks₁₂
    let C := Ab.toBlocks₂₁
    let D := Ab.toBlocks₂₂
    have hA11 : IsStieltjes A11 := hAb.toBlocks₁₁
    have hB : ∀ p q, B p q ≤ 0 := fun p q => hAb.toBlocks₁₂_nonpos p q
    have hCeq : Bᴴ = C := by
      ext p k
      exact hAb.isHermitian.apply (Sum.inr p) (Sum.inl k)
    have hC : ∀ p q, C p q ≤ 0 := by
      intro p q
      rw [← hCeq]
      simpa [conjTranspose_apply, star_trivial] using hB q p
    have hfrom : Ab = fromBlocks A11 B C D := (fromBlocks_toBlocks Ab).symm
    have hBlk : (fromBlocks A11 B C D).PosDef := hfrom ▸ hAb.posDef
    have hA11inv : ∀ p q, 0 ≤ A11⁻¹ p q := ih A11 hA11
    let S := D - C * A11⁻¹ * B
    have hBlkHerm : (fromBlocks A11 B Bᴴ D).PosDef := by
      rw [hCeq]
      exact hBlk
    have hS : S.PosDef := by
      change (D - C * A11⁻¹ * B).PosDef
      rw [← hCeq]
      exact schurComplement_posDef hA11.posDef hBlkHerm
    have hSinv : ∀ p q, 0 ≤ S⁻¹ p q := inv_fin_one_nonneg hS
    have hinv := inv_fromBlocks₁₁_eq A11 B C D hA11.posDef.isUnit hS.isUnit hBlk.isUnit
    have hAbinv : ∀ u v, 0 ≤ Ab⁻¹ u v := by
      intro u v
      rw [hfrom, hinv]
      cases u with
      | inl p =>
        cases v with
        | inl q =>
          rw [fromBlocks_apply₁₁]
          refine add_entry_nonneg hA11inv ?_ p q
          intro a b
          refine mul_entry_nonneg ?_ hA11inv a b
          intro a1 b1
          refine mul_entry_nonneg_of_nonpos ?_ hC a1 b1
          intro a2 b2
          refine mul_entry_nonpos_of_nonpos_nonneg ?_ hSinv a2 b2
          intro a3 b3
          exact mul_entry_nonpos_of_nonneg_nonpos hA11inv hB a3 b3
        | inr q =>
          rw [fromBlocks_apply₁₂]
          refine neg_entry_nonneg_of_nonpos ?_ p q
          intro a b
          refine mul_entry_nonpos_of_nonpos_nonneg ?_ hSinv a b
          intro a' b'
          exact mul_entry_nonpos_of_nonneg_nonpos hA11inv hB a' b'
      | inr p =>
        cases v with
        | inl q =>
          rw [fromBlocks_apply₂₁]
          refine neg_entry_nonneg_of_nonpos ?_ p q
          intro a b
          refine mul_entry_nonpos_of_nonpos_nonneg ?_ hA11inv a b
          intro a' b'
          exact mul_entry_nonpos_of_nonneg_nonpos hSinv hC a' b'
        | inr q =>
          rw [fromBlocks_apply₂₂]
          exact hSinv p q
    have hre : Ab⁻¹ = A⁻¹.reindex e.symm e.symm := inv_reindex e.symm e.symm A
    have heq : A⁻¹ i j = Ab⁻¹ (e.symm i) (e.symm j) := by
      rw [hre]
      simp [reindex_apply, submatrix_apply]
    rw [heq]
    exact hAbinv _ _

/-- Stieltjes matrices are inverse-nonnegative (symmetric M-matrices). -/
theorem IsStieltjes.inv_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : IsStieltjes A) (i j : ι) : 0 ≤ A⁻¹ i j := by
  let e := Fintype.equivFin ι
  let Afin := A.reindex e e
  have hAfin : IsStieltjes Afin := hA.submatrix e.symm.injective
  have h := IsStieltjes.inv_nonneg_fin (Fintype.card ι) Afin hAfin (e i) (e j)
  have heq : A⁻¹ i j = Afin⁻¹ (e i) (e j) := by
    change A⁻¹ i j = (A.reindex e e)⁻¹ (e i) (e j)
    rw [inv_reindex]
    simp [reindex_apply, submatrix_apply]
  rw [heq]
  exact h

end NystromSubmodularity
