import NystromSubmodularity.Stieltjes
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.VecNotation

/-!
# Inverse-trace supermodularity on Stieltjes matrices

Atamtürk–Gómez four-point identity: for a Stieltjes matrix `A` and
`F(T)=tr(A[T]⁻¹)`, the defect on `{i,j}` relative to a base set `S`
splits as a sum of two nonnegative `2×2` expressions in the Schur
complement `Q` and Gram `H = Cᵀ A[S]⁻² C`. Colbrook Lemma 2.2
(`exact_marginal`) and strict decrease of \(\mathcal{E}\) hold for
every positive-definite precision matrix, not only Stieltjes matrices.
-/

namespace NystromSubmodularity

open Matrix
open scoped Matrix

set_option linter.unusedSectionVars false

/-! ## `2×2` inverse formulas -/

lemma inv_fin_two_00 (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    Q⁻¹ 0 0 = Q.det⁻¹ * Q 1 1 := by
  rw [Matrix.inv_def, Matrix.smul_apply, adjugate_fin_two]
  simp

lemma inv_fin_two_11 (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    Q⁻¹ 1 1 = Q.det⁻¹ * Q 0 0 := by
  rw [Matrix.inv_def, Matrix.smul_apply, adjugate_fin_two]
  simp

lemma inv_fin_two_01 (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    Q⁻¹ 0 1 = Q.det⁻¹ * (-Q 0 1) := by
  rw [Matrix.inv_def, Matrix.smul_apply, adjugate_fin_two]
  simp

lemma inv_fin_two_10 (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    Q⁻¹ 1 0 = Q.det⁻¹ * (-Q 1 0) := by
  rw [Matrix.inv_def, Matrix.smul_apply, adjugate_fin_two]
  simp

lemma inv_fin_two_00_div (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    Q⁻¹ 0 0 = Q 1 1 / Q.det := by
  rw [inv_fin_two_00, div_eq_inv_mul]

lemma inv_fin_two_11_div (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    Q⁻¹ 1 1 = Q 0 0 / Q.det := by
  rw [inv_fin_two_11, div_eq_inv_mul]

lemma mul_fin_one (P Q : Matrix (Fin 1) (Fin 1) ℝ) :
    (P * Q) 0 0 = P 0 0 * Q 0 0 := by
  simp [Matrix.mul_apply]

lemma posDef_det_pos_fin_two {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.PosDef) :
    0 < Q.det := by
  have h11 : 0 < Q 1 1 := hQ.diag_pos
  have hinv : 0 < Q⁻¹ 0 0 := hQ.inv.diag_pos
  have hdiv : 0 < Q 1 1 / Q.det := by
    rwa [← inv_fin_two_00_div]
  rcases (div_pos_iff.mp hdiv) with (⟨_, hdet⟩ | ⟨hneg, _⟩)
  · exact hdet
  · exact (lt_irrefl _ (hneg.trans h11)).elim

lemma posDef_det_le_diag_prod {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.PosDef) :
    Q.det ≤ Q 0 0 * Q 1 1 := by
  have hsym : Q.IsSymm := (isHermitian_iff_isSymm (α := ℝ)).mp hQ.isHermitian
  rw [det_fin_two, hsym.apply 0 1]
  nlinarith [sq_nonneg (Q 0 1)]

/-! ## Schur complement and Gram of a two-index border -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `2×2` Schur complement of `{i,j}` relative to `S`. -/
noncomputable def schurPair (A : Matrix ι ι ℝ) (S : Finset ι) (i j : ι) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  pairDiagBlock A i j -
    (pairOffBlock A S i j).conjTranspose * (principalSubmatrix A S)⁻¹ *
      pairOffBlock A S i j

/-- Gram `H = Cᵀ N⁻² C` of the off-diagonal block. -/
noncomputable def gramPair (A : Matrix ι ι ℝ) (S : Finset ι) (i j : ι) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  (pairOffBlock A S i j).conjTranspose *
    ((principalSubmatrix A S)⁻¹ * (principalSubmatrix A S)⁻¹) *
    pairOffBlock A S i j

/-- `1×1` Schur complement of `{i}` relative to `S`. -/
noncomputable def schurOne (A : Matrix ι ι ℝ) (S : Finset ι) (i : ι) :
    Matrix (Fin 1) (Fin 1) ℝ :=
  scalarBlock A i -
    (colBlock A S i).conjTranspose * (principalSubmatrix A S)⁻¹ * colBlock A S i

noncomputable def gramOne (A : Matrix ι ι ℝ) (S : Finset ι) (i : ι) :
    Matrix (Fin 1) (Fin 1) ℝ :=
  (colBlock A S i).conjTranspose *
    ((principalSubmatrix A S)⁻¹ * (principalSubmatrix A S)⁻¹) *
    colBlock A S i

lemma matrix_sub_apply {l m : Type*} (X Y : Matrix l m ℝ) (p : l) (q : m) :
    (X - Y) p q = X p q - Y p q :=
  rfl

lemma scalarBlock_apply {κ R : Type*} (A : Matrix κ κ R) (i : κ) (k l : Fin 1) :
    scalarBlock A i k l = A i i :=
  rfl

/-- Cyclic identity `tr(N⁻¹ B S⁻¹ Bᴴ N⁻¹) = tr(S⁻¹ Bᴴ N⁻² B)`. -/
lemma trace_inv_schur_gram {m n : Type*} [Fintype m] [Fintype n]
    (Ninv : Matrix m m ℝ) (B : Matrix m n ℝ) (Sinv : Matrix n n ℝ) :
    (Ninv * B * Sinv * B.conjTranspose * Ninv).trace =
      (Sinv * (B.conjTranspose * (Ninv * Ninv) * B)).trace := by
  have hassoc :
      Ninv * B * Sinv * B.conjTranspose * Ninv =
        Ninv * B * Sinv * (B.conjTranspose * Ninv) :=
    Matrix.mul_assoc (Ninv * B * Sinv) B.conjTranspose Ninv
  rw [hassoc, Matrix.trace_mul_cycle (Ninv * B) Sinv (B.conjTranspose * Ninv)]
  have hmid : B.conjTranspose * Ninv * (Ninv * B) =
      B.conjTranspose * (Ninv * Ninv) * B := by
    rw [← Matrix.mul_assoc (B.conjTranspose * Ninv) Ninv B,
      Matrix.mul_assoc B.conjTranspose Ninv Ninv]
  rw [hmid, Matrix.trace_mul_comm (B.conjTranspose * (Ninv * Ninv) * B) Sinv]

lemma trace_inv_fromBlocks {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (N : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n m ℝ) (D : Matrix n n ℝ)
    (hN : IsUnit N) (hS : IsUnit (D - C * N⁻¹ * B))
    (hBlk : IsUnit (fromBlocks N B C D)) :
    (fromBlocks N B C D)⁻¹.trace =
      N⁻¹.trace + (N⁻¹ * B * (D - C * N⁻¹ * B)⁻¹ * C * N⁻¹).trace +
        (D - C * N⁻¹ * B)⁻¹.trace := by
  rw [inv_fromBlocks₁₁_eq N B C D hN hS hBlk, trace_fromBlocks, trace_add]

lemma traceInv_insert₁ {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    {S : Finset ι} {i : ι} (hi : i ∉ S) :
    traceInv A (insert i S) =
      (fromBlocks (principalSubmatrix A S) (colBlock A S i)
          (colBlock A S i).conjTranspose (scalarBlock A i))⁻¹.trace := by
  rw [traceInv, principalSubmatrix_insert₁ A hA hi, inv_reindex, trace_reindex]

lemma traceInv_insert₂ {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    {S : Finset ι} {i j : ι} (hi : i ∉ S) (hj : j ∉ S) (hij : i ≠ j) :
    traceInv A (insert j (insert i S)) =
      (fromBlocks (principalSubmatrix A S) (pairOffBlock A S i j)
          (pairOffBlock A S i j).conjTranspose (pairDiagBlock A i j))⁻¹.trace := by
  rw [traceInv, principalSubmatrix_insert₂ A hA hi hj hij, inv_reindex, trace_reindex]

lemma fromBlocks_insert₁_posDef_of_posDef {A : Matrix ι ι ℝ} (hA : A.PosDef)
    {S : Finset ι} {i : ι} (hi : i ∉ S) :
    (fromBlocks (principalSubmatrix A S) (colBlock A S i)
        (colBlock A S i).conjTranspose (scalarBlock A i)).PosDef := by
  have hP : (principalSubmatrix A (insert i S)).PosDef :=
    hA.submatrix Subtype.val_injective
  have heq := principalSubmatrix_insert₁ A hA.isHermitian hi
  have hre : ((fromBlocks (principalSubmatrix A S) (colBlock A S i)
        (colBlock A S i).conjTranspose (scalarBlock A i)).reindex
      (insert₁Equiv hi) (insert₁Equiv hi)).PosDef := heq ▸ hP
  have hsub :
      ((fromBlocks (principalSubmatrix A S) (colBlock A S i)
          (colBlock A S i).conjTranspose (scalarBlock A i)).submatrix
        (insert₁Equiv hi).symm (insert₁Equiv hi).symm).PosDef := by
    simpa [reindex_apply] using hre
  exact (posDef_submatrix_equiv (insert₁Equiv hi).symm).1 hsub

lemma fromBlocks_insert₁_posDef {A : Matrix ι ι ℝ} (hA : IsStieltjes A)
    {S : Finset ι} {i : ι} (hi : i ∉ S) :
    (fromBlocks (principalSubmatrix A S) (colBlock A S i)
        (colBlock A S i).conjTranspose (scalarBlock A i)).PosDef :=
  fromBlocks_insert₁_posDef_of_posDef hA.posDef hi

lemma fromBlocks_insert₂_posDef {A : Matrix ι ι ℝ} (hA : IsStieltjes A)
    {S : Finset ι} {i j : ι} (hi : i ∉ S) (hj : j ∉ S) (hij : i ≠ j) :
    (fromBlocks (principalSubmatrix A S) (pairOffBlock A S i j)
        (pairOffBlock A S i j).conjTranspose (pairDiagBlock A i j)).PosDef := by
  have hP : (principalSubmatrix A (insert j (insert i S))).PosDef :=
    (hA.principal _).posDef
  have heq := principalSubmatrix_insert₂ A hA.isHermitian hi hj hij
  have hre :
      ((fromBlocks (principalSubmatrix A S) (pairOffBlock A S i j)
          (pairOffBlock A S i j).conjTranspose (pairDiagBlock A i j)).reindex
        (insert₂Equiv hi hj hij) (insert₂Equiv hi hj hij)).PosDef := heq ▸ hP
  have hsub :
      ((fromBlocks (principalSubmatrix A S) (pairOffBlock A S i j)
          (pairOffBlock A S i j).conjTranspose (pairDiagBlock A i j)).submatrix
        (insert₂Equiv hi hj hij).symm (insert₂Equiv hi hj hij).symm).PosDef := by
    simpa [reindex_apply] using hre
  exact (posDef_submatrix_equiv (insert₂Equiv hi hj hij).symm).1 hsub

lemma schurOne_posDef_of_posDef {A : Matrix ι ι ℝ} (hA : A.PosDef)
    {S : Finset ι} {i : ι} (hi : i ∉ S) :
    (schurOne A S i).PosDef := by
  have hN : (principalSubmatrix A S).PosDef := hA.submatrix Subtype.val_injective
  have hBlk := fromBlocks_insert₁_posDef_of_posDef hA hi
  simpa [schurOne] using schurComplement_posDef hN hBlk

lemma schurOne_posDef {A : Matrix ι ι ℝ} (hA : IsStieltjes A)
    {S : Finset ι} {i : ι} (hi : i ∉ S) :
    (schurOne A S i).PosDef :=
  schurOne_posDef_of_posDef hA.posDef hi

lemma schurPair_posDef {A : Matrix ι ι ℝ} (hA : IsStieltjes A)
    {S : Finset ι} {i j : ι} (hi : i ∉ S) (hj : j ∉ S) (hij : i ≠ j) :
    (schurPair A S i j).PosDef := by
  have hN : (principalSubmatrix A S).PosDef := (hA.principal S).posDef
  have hBlk := fromBlocks_insert₂_posDef hA hi hj hij
  simpa [schurPair] using schurComplement_posDef hN hBlk

/-- Colbrook Lemma 2.2: the exact one-index inverse-trace increment for any
positive-definite precision matrix. -/
theorem exact_marginal {A : Matrix ι ι ℝ} (hA : A.PosDef)
    {S : Finset ι} {i : ι} (hi : i ∉ S) :
    traceInv A (insert i S) - traceInv A S =
      (1 + gramOne A S i 0 0) / schurOne A S i 0 0 := by
  have hHer := hA.isHermitian
  have hN : (principalSubmatrix A S).PosDef := hA.submatrix Subtype.val_injective
  have hBlk := fromBlocks_insert₁_posDef_of_posDef hA hi
  have hS : (schurOne A S i).PosDef := schurOne_posDef_of_posDef hA hi
  have hs00 : (schurOne A S i)⁻¹ 0 0 = (schurOne A S i 0 0)⁻¹ :=
    inv_fin_one_apply (schurOne A S i)
  have hpos : schurOne A S i 0 0 ≠ 0 := hS.diag_pos.ne'
  have hgram :=
    trace_inv_schur_gram (principalSubmatrix A S)⁻¹ (colBlock A S i) (schurOne A S i)⁻¹
  have hsum :
      traceInv A (insert i S) =
        traceInv A S + (1 + gramOne A S i 0 0) / schurOne A S i 0 0 := by
    rw [traceInv_insert₁ hHer hi,
      trace_inv_fromBlocks (principalSubmatrix A S) (colBlock A S i)
        (colBlock A S i).conjTranspose (scalarBlock A i) hN.isUnit hS.isUnit hBlk.isUnit]
    change (principalSubmatrix A S)⁻¹.trace +
        ((principalSubmatrix A S)⁻¹ * colBlock A S i * (schurOne A S i)⁻¹ *
          (colBlock A S i).conjTranspose * (principalSubmatrix A S)⁻¹).trace +
        (schurOne A S i)⁻¹.trace =
      traceInv A S + (1 + gramOne A S i 0 0) / schurOne A S i 0 0
    have htrG : ((schurOne A S i)⁻¹ * gramOne A S i).trace =
        (schurOne A S i 0 0)⁻¹ * gramOne A S i 0 0 := by
      rw [trace_fin_one, mul_fin_one, hs00]
    have htrS : (schurOne A S i)⁻¹.trace = (schurOne A S i 0 0)⁻¹ := by
      rw [trace_fin_one, hs00]
    have hgrameq :
        ((principalSubmatrix A S)⁻¹ * colBlock A S i * (schurOne A S i)⁻¹ *
            (colBlock A S i).conjTranspose * (principalSubmatrix A S)⁻¹).trace =
          ((schurOne A S i)⁻¹ * gramOne A S i).trace := by
      simpa [gramOne] using hgram
    rw [hgrameq, htrG, htrS, show traceInv A S = (principalSubmatrix A S)⁻¹.trace from rfl]
    field_simp [hpos]
    ring
  linarith [hsum]

lemma exact_marginal_one {A : Matrix ι ι ℝ} (hA : IsStieltjes A)
    {S : Finset ι} {i : ι} (hi : i ∉ S) :
    traceInv A (insert i S) =
      traceInv A S + (1 + gramOne A S i 0 0) / schurOne A S i 0 0 := by
  linarith [exact_marginal hA.posDef hi]

lemma gramOne_nonneg {A : Matrix ι ι ℝ} (hA : A.PosDef)
    {S : Finset ι} {i : ι} : 0 ≤ gramOne A S i 0 0 := by
  have hN : (principalSubmatrix A S).PosDef := hA.submatrix Subtype.val_injective
  have hHer : ((principalSubmatrix A S)⁻¹).IsHermitian := hN.inv.isHermitian
  have hgram :
      gramOne A S i =
        ((principalSubmatrix A S)⁻¹ * colBlock A S i).conjTranspose *
          ((principalSubmatrix A S)⁻¹ * colBlock A S i) := by
    unfold gramOne
    simp [Matrix.mul_assoc]
    rw [(isHermitian_iff_isSymm (α := ℝ)).mp hHer]
  rw [hgram, Matrix.mul_apply]
  refine Finset.sum_nonneg fun p _ => ?_
  simp [conjTranspose_apply, star_trivial]
  exact mul_self_nonneg _

lemma exact_marginal_pos {A : Matrix ι ι ℝ} (hA : A.PosDef)
    {S : Finset ι} {i : ι} (hi : i ∉ S) :
    0 < traceInv A (insert i S) - traceInv A S := by
  have hS : (schurOne A S i).PosDef := schurOne_posDef_of_posDef hA hi
  have hσ : 0 < schurOne A S i 0 0 := hS.diag_pos
  have hnum : 0 < 1 + gramOne A S i 0 0 := by
    nlinarith [gramOne_nonneg hA (S := S) (i := i)]
  rw [exact_marginal hA hi]
  exact div_pos hnum hσ

lemma traceInv_mono {A : Matrix ι ι ℝ} (hA : A.PosDef)
    {U V : Finset ι} (hUV : U ⊆ V) : traceInv A U ≤ traceInv A V := by
  have : ∀ D : Finset ι, Disjoint U D → traceInv A U ≤ traceInv A (U ∪ D) := by
    intro D
    refine Finset.induction_on D ?e ?i
    · intro _; simp
    · intro a D ha ih hdis
      have haU : a ∉ U := fun h =>
        Finset.disjoint_left.mp hdis h (Finset.mem_insert_self a D)
      have hdis' : Disjoint U D := hdis.mono_right (Finset.subset_insert a D)
      have hle := ih hdis'
      have hunion : U ∪ insert a D = insert a (U ∪ D) := by rw [Finset.union_insert]
      rw [hunion]
      have haUD : a ∉ U ∪ D := by
        simp [Finset.mem_union, haU, ha]
      linarith [exact_marginal_pos hA haUD]
  have hV : V = U ∪ (V \ U) := (Finset.union_sdiff_of_subset hUV).symm
  rw [hV]
  exact this (V \ U) Finset.disjoint_sdiff

lemma traceInv_strict_mono {A : Matrix ι ι ℝ} (hA : A.PosDef)
    {U V : Finset ι} (hUV : U ⊂ V) :
    traceInv A U < traceInv A V := by
  obtain ⟨hsubset, hne⟩ := ssubset_iff_subset_ne.mp hUV
  have hneD : V \ U ≠ ∅ := by
    intro h
    exact hne (Finset.Subset.antisymm hsubset (Finset.sdiff_eq_empty_iff_subset.mp h))
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hneD
  have hiV : i ∈ V := (Finset.mem_sdiff.mp hi).1
  have hiU : i ∉ U := (Finset.mem_sdiff.mp hi).2
  have hrest : insert i U ⊆ V := by
    intro x hx
    rcases Finset.mem_insert.mp hx with (rfl | hx)
    · exact hiV
    · exact hsubset hx
  linarith [exact_marginal_pos hA hiU, traceInv_mono hA hrest]

/-- Nyström error is strictly decreasing along proper inclusions, for every
positive-definite precision matrix. -/
theorem nystromError_strict_anti_monotone {A : Matrix ι ι ℝ} (hA : A.PosDef)
    {S T : Finset ι} (hST : S ⊂ T) :
    nystromError A T < nystromError A S := by
  have hcompl : compl T ⊂ compl S := by
    obtain ⟨hsubset, hne⟩ := ssubset_iff_subset_ne.mp hST
    refine ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro x hx
      exact mem_compl.mpr (fun hxS => (mem_compl.mp hx) (hsubset hxS))
    · intro h
      exact hne (by rw [← compl_compl S, ← compl_compl T, h])
  simpa [nystromError] using traceInv_strict_mono hA hcompl

lemma exact_marginal_two {A : Matrix ι ι ℝ} (hA : IsStieltjes A)
    {S : Finset ι} {i j : ι} (hi : i ∉ S) (hj : j ∉ S) (hij : i ≠ j) :
    traceInv A (insert j (insert i S)) =
      traceInv A S + (schurPair A S i j)⁻¹.trace +
        ((schurPair A S i j)⁻¹ * gramPair A S i j).trace := by
  have hHer := hA.isHermitian
  have hN : (principalSubmatrix A S).PosDef := (hA.principal S).posDef
  have hBlk := fromBlocks_insert₂_posDef hA hi hj hij
  have hQ : (schurPair A S i j).PosDef := schurPair_posDef hA hi hj hij
  have hgram :=
    trace_inv_schur_gram (principalSubmatrix A S)⁻¹ (pairOffBlock A S i j)
      (schurPair A S i j)⁻¹
  rw [traceInv_insert₂ hHer hi hj hij,
    trace_inv_fromBlocks (principalSubmatrix A S) (pairOffBlock A S i j)
      (pairOffBlock A S i j).conjTranspose (pairDiagBlock A i j)
      hN.isUnit hQ.isUnit hBlk.isUnit]
  change (principalSubmatrix A S)⁻¹.trace +
      ((principalSubmatrix A S)⁻¹ * pairOffBlock A S i j * (schurPair A S i j)⁻¹ *
        (pairOffBlock A S i j).conjTranspose * (principalSubmatrix A S)⁻¹).trace +
      (schurPair A S i j)⁻¹.trace =
    traceInv A S + (schurPair A S i j)⁻¹.trace +
      ((schurPair A S i j)⁻¹ * gramPair A S i j).trace
  have hgrameq :
      ((principalSubmatrix A S)⁻¹ * pairOffBlock A S i j * (schurPair A S i j)⁻¹ *
          (pairOffBlock A S i j).conjTranspose * (principalSubmatrix A S)⁻¹).trace =
        ((schurPair A S i j)⁻¹ * gramPair A S i j).trace := by
    simpa [gramPair] using hgram
  rw [hgrameq, show traceInv A S = (principalSubmatrix A S)⁻¹.trace from rfl]
  ac_rfl

/-! ## Relating one-step Schur/Gram to the `2×2` blocks -/

lemma pairOff_mul_diag (A : Matrix ι ι ℝ) (S : Finset ι) (i j : ι)
    (N : Matrix (PrincipalIndex S) (PrincipalIndex S) ℝ) (k : Fin 2) :
    (((pairOffBlock A S i j).conjTranspose * N * pairOffBlock A S i j) k k) =
      (((if k = 0 then colBlock A S i else colBlock A S j).conjTranspose * N *
          (if k = 0 then colBlock A S i else colBlock A S j)) 0 0) := by
  fin_cases k <;>
    simp [Matrix.mul_apply, pairOffBlock, colBlock]

lemma colBlock_if (A : Matrix ι ι ℝ) (S : Finset ι) (i j : ι) (k : Fin 2) :
    (if k = 0 then colBlock A S i else colBlock A S j) =
      colBlock A S (if k = 0 then i else j) := by
  split_ifs <;> rfl

lemma schurPair_diag (A : Matrix ι ι ℝ) (S : Finset ι) (i j : ι) (k : Fin 2) :
    schurPair A S i j k k =
      schurOne A S (if k = 0 then i else j) 0 0 := by
  rw [schurPair, schurOne, matrix_sub_apply, matrix_sub_apply]
  congr 1
  · rw [pairDiagBlock_apply, scalarBlock_apply]
    split_ifs <;> simp
  · simpa [colBlock_if A S i j k] using
      pairOff_mul_diag A S i j (principalSubmatrix A S)⁻¹ k

lemma schurPair_00 {A : Matrix ι ι ℝ} (S : Finset ι) (i j : ι) :
    schurPair A S i j 0 0 = schurOne A S i 0 0 :=
  (schurPair_diag A S i j 0).trans (by simp)

lemma schurPair_11 {A : Matrix ι ι ℝ} (S : Finset ι) (i j : ι) :
    schurPair A S i j 1 1 = schurOne A S j 0 0 :=
  (schurPair_diag A S i j 1).trans (by simp)

lemma gramPair_diag (A : Matrix ι ι ℝ) (S : Finset ι) (i j : ι) (k : Fin 2) :
    gramPair A S i j k k =
      gramOne A S (if k = 0 then i else j) 0 0 := by
  simpa [gramPair, gramOne, colBlock_if A S i j k] using
    pairOff_mul_diag A S i j ((principalSubmatrix A S)⁻¹ * (principalSubmatrix A S)⁻¹) k

lemma gramPair_00 {A : Matrix ι ι ℝ} (S : Finset ι) (i j : ι) :
    gramPair A S i j 0 0 = gramOne A S i 0 0 :=
  (gramPair_diag A S i j 0).trans (by simp)

lemma gramPair_11 {A : Matrix ι ι ℝ} (S : Finset ι) (i j : ι) :
    gramPair A S i j 1 1 = gramOne A S j 0 0 :=
  (gramPair_diag A S i j 1).trans (by simp)

/-! ## Sign lemmas -/

lemma pairOffBlock_nonpos {A : Matrix ι ι ℝ} (hA : IsStieltjes A)
    {S : Finset ι} {i j : ι} (hi : i ∉ S) (hj : j ∉ S)
    (a : PrincipalIndex S) (k : Fin 2) :
    pairOffBlock A S i j a k ≤ 0 := by
  simp [pairOffBlock]
  split_ifs with hk
  · exact hA.offDiag_nonpos (fun h => hi (h ▸ a.2))
  · exact hA.offDiag_nonpos (fun h => hj (h ▸ a.2))

lemma pairOffBlock_conjTranspose_nonpos {A : Matrix ι ι ℝ} (hA : IsStieltjes A)
    {S : Finset ι} {i j : ι} (hi : i ∉ S) (hj : j ∉ S)
    (k : Fin 2) (a : PrincipalIndex S) :
    (pairOffBlock A S i j).conjTranspose k a ≤ 0 := by
  simp [conjTranspose_apply, star_trivial]
  exact pairOffBlock_nonpos hA hi hj a k

lemma principal_inv_nonneg {A : Matrix ι ι ℝ} (hA : IsStieltjes A) (S : Finset ι)
    (p q : PrincipalIndex S) :
    0 ≤ (principalSubmatrix A S)⁻¹ p q :=
  (hA.principal S).inv_nonneg p q

lemma gramPair_nonneg {A : Matrix ι ι ℝ} (hA : IsStieltjes A)
    {S : Finset ι} {i j : ι} (hi : i ∉ S) (hj : j ∉ S) (k l : Fin 2) :
    0 ≤ gramPair A S i j k l := by
  have hB : ∀ a t, pairOffBlock A S i j a t ≤ 0 := fun a t =>
    pairOffBlock_nonpos hA hi hj a t
  have hBt : ∀ t a, (pairOffBlock A S i j).conjTranspose t a ≤ 0 := fun t a =>
    pairOffBlock_conjTranspose_nonpos hA hi hj t a
  have hN : ∀ p q, 0 ≤ (principalSubmatrix A S)⁻¹ p q :=
    principal_inv_nonneg hA S
  have hN2 : ∀ p q,
      0 ≤ ((principalSubmatrix A S)⁻¹ * (principalSubmatrix A S)⁻¹) p q :=
    fun p q => mul_entry_nonneg hN hN p q
  have hLeft : ∀ t a,
      ((pairOffBlock A S i j).conjTranspose *
        ((principalSubmatrix A S)⁻¹ * (principalSubmatrix A S)⁻¹)) t a ≤ 0 :=
    fun t a => mul_entry_nonpos_of_nonpos_nonneg hBt hN2 t a
  exact mul_entry_nonneg_of_nonpos hLeft hB k l

lemma schurPair_offDiag_nonpos {A : Matrix ι ι ℝ} (hA : IsStieltjes A)
    {S : Finset ι} {i j : ι} (hi : i ∉ S) (hj : j ∉ S) (hij : i ≠ j) :
    schurPair A S i j 0 1 ≤ 0 := by
  have hD : pairDiagBlock A i j 0 1 ≤ 0 := by
    simp [pairDiagBlock]
    exact hA.offDiag_nonpos hij
  have hB : ∀ a t, pairOffBlock A S i j a t ≤ 0 := fun a t =>
    pairOffBlock_nonpos hA hi hj a t
  have hBt : ∀ t a, (pairOffBlock A S i j).conjTranspose t a ≤ 0 := fun t a =>
    pairOffBlock_conjTranspose_nonpos hA hi hj t a
  have hN : ∀ p q, 0 ≤ (principalSubmatrix A S)⁻¹ p q :=
    principal_inv_nonneg hA S
  have h1 : ∀ t a,
      ((pairOffBlock A S i j).conjTranspose * (principalSubmatrix A S)⁻¹) t a ≤ 0 :=
    fun t a => mul_entry_nonpos_of_nonpos_nonneg hBt hN t a
  have hprod :
      0 ≤ ((pairOffBlock A S i j).conjTranspose * (principalSubmatrix A S)⁻¹ *
        pairOffBlock A S i j) 0 1 :=
    mul_entry_nonneg_of_nonpos h1 hB 0 1
  rw [schurPair, matrix_sub_apply]
  linarith [hD, hprod]

/-! ## Four-point defect -/

lemma four_point_defect_eq {A : Matrix ι ι ℝ} (hA : IsStieltjes A)
    {S : Finset ι} {i j : ι} (hi : i ∉ S) (hj : j ∉ S) (hij : i ≠ j) :
    traceInv A S + traceInv A (insert j (insert i S)) -
        traceInv A (insert i S) - traceInv A (insert j S) =
      ((schurPair A S i j)⁻¹.trace - (schurPair A S i j 0 0)⁻¹ -
          (schurPair A S i j 1 1)⁻¹) +
        (((schurPair A S i j)⁻¹ * gramPair A S i j).trace -
          gramPair A S i j 0 0 / schurPair A S i j 0 0 -
          gramPair A S i j 1 1 / schurPair A S i j 1 1) := by
  have h1 := exact_marginal_one hA hi
  have h2 := exact_marginal_one hA hj
  have h12 := exact_marginal_two hA hi hj hij
  have h00 : schurPair A S i j 0 0 = schurOne A S i 0 0 := schurPair_00 S i j
  have h11 : schurPair A S i j 1 1 = schurOne A S j 0 0 := schurPair_11 S i j
  have hg00 : gramPair A S i j 0 0 = gramOne A S i 0 0 := gramPair_00 S i j
  have hg11 : gramPair A S i j 1 1 = gramOne A S j 0 0 := gramPair_11 S i j
  have hQi : schurOne A S i 0 0 ≠ 0 := (schurOne_posDef hA hi).diag_pos.ne'
  have hQj : schurOne A S j 0 0 ≠ 0 := (schurOne_posDef hA hj).diag_pos.ne'
  rw [h1, h2, h12, h00, h11, hg00, hg11]
  field_simp [hQi, hQj]
  ring

lemma two_by_two_inv_trace_defect {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.PosDef) :
    0 ≤ Q⁻¹.trace - (Q 0 0)⁻¹ - (Q 1 1)⁻¹ := by
  have h00 : 0 < Q 0 0 := hQ.diag_pos
  have h11 : 0 < Q 1 1 := hQ.diag_pos
  have hdet : 0 < Q.det := posDef_det_pos_fin_two hQ
  have hle : Q.det ≤ Q 0 0 * Q 1 1 := posDef_det_le_diag_prod hQ
  have htr : Q⁻¹.trace = (Q 0 0 + Q 1 1) * Q.det⁻¹ := by
    rw [trace_fin_two, inv_fin_two_00, inv_fin_two_11]
    ring
  rw [htr]
  have hsum : (Q 0 0)⁻¹ + (Q 1 1)⁻¹ = (Q 0 0 + Q 1 1) * (Q 0 0 * Q 1 1)⁻¹ := by
    field_simp [h00.ne', h11.ne']
    ring
  have heq :
      (Q 0 0 + Q 1 1) * Q.det⁻¹ - (Q 0 0)⁻¹ - (Q 1 1)⁻¹ =
        (Q 0 0 + Q 1 1) * (Q.det⁻¹ - (Q 0 0 * Q 1 1)⁻¹) := by
    rw [sub_sub, hsum]
    ring
  rw [heq]
  refine mul_nonneg (add_nonneg h00.le h11.le) ?_
  rw [sub_nonneg]
  simpa [one_div] using one_div_le_one_div_of_le hdet hle

lemma two_by_two_gram_defect {Q H : Matrix (Fin 2) (Fin 2) ℝ}
    (hQ : Q.PosDef) (hQ01 : Q 0 1 ≤ 0)
    (hH00 : 0 ≤ H 0 0) (hH11 : 0 ≤ H 1 1) (hH01 : 0 ≤ H 0 1)
    (hHsym : H 0 1 = H 1 0) (hQsym : Q 0 1 = Q 1 0) :
    0 ≤ (Q⁻¹ * H).trace - H 0 0 / Q 0 0 - H 1 1 / Q 1 1 := by
  have h00 : 0 < Q 0 0 := hQ.diag_pos
  have h11 : 0 < Q 1 1 := hQ.diag_pos
  have hdet : 0 < Q.det := posDef_det_pos_fin_two hQ
  have htr : (Q⁻¹ * H).trace =
      Q⁻¹ 0 0 * H 0 0 + Q⁻¹ 0 1 * H 1 0 + Q⁻¹ 1 0 * H 0 1 + Q⁻¹ 1 1 * H 1 1 := by
    simp [trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have hd00 : 0 ≤ Q.det⁻¹ * Q 1 1 - (Q 0 0)⁻¹ := by
    have hex :
        Q.det⁻¹ * Q 1 1 - (Q 0 0)⁻¹ =
          (Q 0 0 * Q 1 1 - Q.det) * (Q.det⁻¹ * (Q 0 0)⁻¹) := by
      field_simp [hdet.ne', h00.ne']
      try ring
    rw [hex]
    refine mul_nonneg ?_ (mul_nonneg (inv_nonneg.mpr hdet.le) (inv_nonneg.mpr h00.le))
    rw [sub_nonneg, det_fin_two, hQsym]
    nlinarith [sq_nonneg (Q 0 1)]
  have hd11 : 0 ≤ Q.det⁻¹ * Q 0 0 - (Q 1 1)⁻¹ := by
    have hex :
        Q.det⁻¹ * Q 0 0 - (Q 1 1)⁻¹ =
          (Q 0 0 * Q 1 1 - Q.det) * (Q.det⁻¹ * (Q 1 1)⁻¹) := by
      field_simp [hdet.ne', h11.ne']
      try ring
    rw [hex]
    refine mul_nonneg ?_ (mul_nonneg (inv_nonneg.mpr hdet.le) (inv_nonneg.mpr h11.le))
    rw [sub_nonneg, det_fin_two, hQsym]
    nlinarith [sq_nonneg (Q 0 1)]
  have hcr : 0 ≤ Q.det⁻¹ * (-Q 0 1) :=
    mul_nonneg (inv_nonneg.mpr hdet.le) (neg_nonneg.mpr hQ01)
  have hexpand :
      Q⁻¹ 0 0 * H 0 0 + Q⁻¹ 0 1 * H 1 0 + Q⁻¹ 1 0 * H 0 1 + Q⁻¹ 1 1 * H 1 1 -
          H 0 0 / Q 0 0 - H 1 1 / Q 1 1 =
        H 0 0 * (Q.det⁻¹ * Q 1 1 - (Q 0 0)⁻¹) +
          H 1 1 * (Q.det⁻¹ * Q 0 0 - (Q 1 1)⁻¹) +
            2 * H 0 1 * (Q.det⁻¹ * (-Q 0 1)) := by
    simp only [inv_fin_two_00, inv_fin_two_11, inv_fin_two_01, inv_fin_two_10, hHsym, hQsym,
      div_eq_mul_inv]
    ring
  rw [htr, hexpand]
  exact add_nonneg (add_nonneg (mul_nonneg hH00 hd00) (mul_nonneg hH11 hd11))
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hH01) hcr)

lemma four_point_defect_nonneg {A : Matrix ι ι ℝ} (hA : IsStieltjes A)
    {S : Finset ι} {i j : ι} (hi : i ∉ S) (hj : j ∉ S) (hij : i ≠ j) :
    0 ≤ traceInv A S + traceInv A (insert j (insert i S)) -
      traceInv A (insert i S) - traceInv A (insert j S) := by
  have hQ : (schurPair A S i j).PosDef := schurPair_posDef hA hi hj hij
  have hQ01 : schurPair A S i j 0 1 ≤ 0 := schurPair_offDiag_nonpos hA hi hj hij
  have hH00 : 0 ≤ gramPair A S i j 0 0 := gramPair_nonneg hA hi hj 0 0
  have hH11 : 0 ≤ gramPair A S i j 1 1 := gramPair_nonneg hA hi hj 1 1
  have hH01 : 0 ≤ gramPair A S i j 0 1 := gramPair_nonneg hA hi hj 0 1
  have hQsym : schurPair A S i j 0 1 = schurPair A S i j 1 0 :=
    isHermitian_apply_real hQ.isHermitian 0 1
  have hHsym : gramPair A S i j 0 1 = gramPair A S i j 1 0 := by
    have hN : (principalSubmatrix A S).PosDef := (hA.principal S).posDef
    have hNinv : ((principalSubmatrix A S)⁻¹).IsHermitian := hN.inv.isHermitian
    have hN2 : ((principalSubmatrix A S)⁻¹ * (principalSubmatrix A S)⁻¹).IsHermitian := by
      rw [IsHermitian, conjTranspose_mul, hNinv.eq]
    have hH : (gramPair A S i j).IsHermitian :=
      isHermitian_conjTranspose_mul_mul (pairOffBlock A S i j) hN2
    exact isHermitian_apply_real hH 0 1
  rw [four_point_defect_eq hA hi hj hij]
  have h1 := two_by_two_inv_trace_defect hQ
  have h2 := two_by_two_gram_defect hQ hQ01 hH00 hH11 hH01 hHsym hQsym
  linarith

/-- Inverse-trace is four-point supermodular on Stieltjes matrices. -/
theorem traceInv_fourPointSupermodular_of_isStieltjes {A : Matrix ι ι ℝ}
    (hA : IsStieltjes A) : FourPointSupermodular (traceInv A) := by
  intro S i j hij hi hj
  have := four_point_defect_nonneg hA hi hj hij
  linarith

theorem traceInv_supermodular_of_isStieltjes {A : Matrix ι ι ℝ} (hA : IsStieltjes A) :
    Supermodular (traceInv A) :=
  supermodular_of_fourPointSupermodular (traceInv_fourPointSupermodular_of_isStieltjes hA)

end NystromSubmodularity
