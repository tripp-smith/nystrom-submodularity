import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Basic

/-!
# Core definitions for Problem 4.6

This file collects the combinatorial and matrix-class predicates used throughout
the project.

## Sign convention

Problem 4.6 (Simons workshop) asks whether the nuclear-norm Nyström *error*
\(\mathcal{E}(S)=\|K-\mathcal{N}_S(K)\|_*\) has diminishing returns
\(\Delta_{\mathcal{E}}(A;i,j)\ge 0\). In standard combinatorics that is
**supermodularity** of \(\mathcal{E}\) (equivalently, submodularity of the gain
\(G(S)=\mathcal{E}(\emptyset)-\mathcal{E}(S)\)). The workshop report calls the
same inequality “submodularity of the error”.

We keep the Wikipedia names: `Submodular` is the \(\ge\) four-set inequality
and `Supermodular` is the \(\le\) inequality. The theorems of Phase 2 are
stated for `Supermodular` of the Nyström error.

References: Colbrook, *Nyström Error Beyond M-Matrices* (arXiv:2607.19282);
Fornace–Lindsey (arXiv:2407.01698), Theorem 5.
-/

namespace NystromSubmodularity

open Matrix Finset

/-- A real-valued set function `f` is *submodular* when for all sets `A`, `B`
we have `f A + f B ≥ f (A ∪ B) + f (A ∩ B)`. -/
def Submodular {α : Type*} [DecidableEq α] (f : Finset α → ℝ) : Prop :=
  ∀ A B : Finset α, f A + f B ≥ f (A ∪ B) + f (A ∩ B)

/-- A real-valued set function `f` is *supermodular* when for all sets `A`, `B`
we have `f A + f B ≤ f (A ∪ B) + f (A ∩ B)`. -/
def Supermodular {α : Type*} [DecidableEq α] (f : Finset α → ℝ) : Prop :=
  ∀ A B : Finset α, f A + f B ≤ f (A ∪ B) + f (A ∩ B)

theorem submodular_iff_neg_supermodular {α : Type*} [DecidableEq α] (f : Finset α → ℝ) :
    Submodular f ↔ Supermodular (fun s => -f s) := by
  constructor <;> intro h A B <;> have := h A B <;> linarith

theorem supermodular_iff_neg_submodular {α : Type*} [DecidableEq α] (f : Finset α → ℝ) :
    Supermodular f ↔ Submodular (fun s => -f s) := by
  constructor <;> intro h A B <;> have := h A B <;> linarith

/-- The normalised gain of a decreasing error; submodular iff the error is
supermodular. -/
def gain {α : Type*} [DecidableEq α] (E : Finset α → ℝ) : Finset α → ℝ :=
  fun S => E ∅ - E S

theorem supermodular_iff_gain_submodular {α : Type*} [DecidableEq α] (E : Finset α → ℝ) :
    Supermodular E ↔ Submodular (gain E) := by
  constructor <;> intro h A B <;> have := h A B <;>
    simp [gain] at * <;> linarith

/-- Constant set functions are (trivially) submodular. -/
theorem submodular_const {α : Type*} [DecidableEq α] (c : ℝ) :
    Submodular (fun _ : Finset α => c) := by
  intro A B
  simp

/-- Constant set functions are (trivially) supermodular. -/
theorem supermodular_const {α : Type*} [DecidableEq α] (c : ℝ) :
    Supermodular (fun _ : Finset α => c) := by
  intro A B
  simp

/-- Four-point form of supermodularity (the Colbrook \(\Delta\ge 0\) inequality). -/
def FourPointSupermodular {α : Type*} [DecidableEq α] (f : Finset α → ℝ) : Prop :=
  ∀ (A : Finset α) (i j : α), i ≠ j → i ∉ A → j ∉ A →
    f A + f (insert j (insert i A)) ≥ f (insert i A) + f (insert j A)

theorem fourPointSupermodular_of_supermodular {α : Type*} [DecidableEq α]
    {f : Finset α → ℝ} (hf : Supermodular f) : FourPointSupermodular f := by
  intro A i j hij hi hj
  have h := hf (insert i A) (insert j A)
  have hunion : insert i A ∪ insert j A = insert j (insert i A) := by
    ext x; simp [or_left_comm]
  have hinter : insert i A ∩ insert j A = A := by
    ext x
    simp only [mem_inter, mem_insert]
    constructor
    · rintro ⟨(rfl | hx), (rfl | hy)⟩
      · exact (hij rfl).elim
      · exact hy
      · exact hx
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, Or.inr hx⟩
  rw [hunion, hinter] at h
  linarith

/-- Adding one extra element to a larger set cannot decrease the increment. -/
theorem fourPointSupermodular_increasing {α : Type*} [DecidableEq α] {f : Finset α → ℝ}
    (hf : FourPointSupermodular f) {A B : Finset α} (hAB : A ⊆ B) {i : α}
    (hiA : i ∉ A) (hiB : i ∉ B) :
    f (insert i A) - f A ≤ f (insert i B) - f B := by
  classical
  generalize hcard : (B \ A).card = n
  induction n using Nat.strongRecOn generalizing A B with
  | ind n ih =>
    if hEq : B \ A = ∅ then
      have hAB' : B ⊆ A := by
        intro x hx
        by_contra hxA
        exact notMem_empty x (hEq ▸ mem_sdiff.2 ⟨hx, hxA⟩)
      have : A = B := Subset.antisymm hAB hAB'
      subst this
      simp
    else
      obtain ⟨j, hj⟩ := nonempty_of_ne_empty hEq
      have hjB : j ∈ B := (mem_sdiff.mp hj).1
      have hjA : j ∉ A := (mem_sdiff.mp hj).2
      have hji : j ≠ i := fun h => hiB (h ▸ hjB)
      set C := B.erase j
      have hAC : A ⊆ C := by
        intro x hx
        exact mem_erase.2 ⟨fun h => hjA (h ▸ hx), hAB hx⟩
      have hjC : j ∉ C := notMem_erase j B
      have hiC : i ∉ C := fun h => hiB (mem_of_mem_erase h)
      have hCcard : (C \ A).card < n := by
        have hset : C \ A = (B \ A).erase j := by
          ext x
          simp only [C, mem_sdiff, mem_erase]
          constructor
          · rintro ⟨⟨hxne, hxB⟩, hxA⟩
            exact ⟨hxne, hxB, hxA⟩
          · rintro ⟨hxne, hxB, hxA⟩
            exact ⟨⟨hxne, hxB⟩, hxA⟩
        rw [hset, ← hcard]
        exact card_erase_lt_of_mem hj
      have hinc₁ : f (insert i A) - f A ≤ f (insert i C) - f C :=
        ih _ hCcard hAC hiA hiC rfl
      have hfp := hf C i j hji.symm hiC hjC
      have hins : insert j (insert i C) = insert i B := by
        ext x
        simp only [C, mem_insert, mem_erase]
        constructor
        · rintro (rfl | rfl | ⟨_, hxB⟩)
          · exact Or.inr hjB
          · exact Or.inl rfl
          · exact Or.inr hxB
        · rintro (rfl | hxB)
          · exact Or.inr (Or.inl rfl)
          · by_cases hxj : x = j
            · subst hxj; exact Or.inl rfl
            · exact Or.inr (Or.inr ⟨hxj, hxB⟩)
      have hCj : insert j C = B := insert_erase hjB
      have hinc₂ : f (insert i C) - f C ≤ f (insert i B) - f B := by
        rw [hins, hCj] at hfp
        linarith
      linarith

/-- The increment of a disjoint block `U` is larger on a larger base set. -/
theorem fourPointSupermodular_block_increasing {α : Type*} [DecidableEq α]
    {f : Finset α → ℝ} (hf : FourPointSupermodular f) {S T U : Finset α}
    (hST : S ⊆ T) (hSU : Disjoint U S) (hTU : Disjoint U T) :
    f (S ∪ U) - f S ≤ f (T ∪ U) - f T := by
  classical
  generalize hcard : U.card = n
  induction n using Nat.strongRecOn generalizing U with
  | ind n ih =>
    if hU : U = ∅ then
      subst hU
      simp
    else
      obtain ⟨i, hiU⟩ := nonempty_of_ne_empty hU
      set U' := U.erase i
      have hU'card : U'.card < n := by
        rw [← hcard]
        exact card_erase_lt_of_mem hiU
      have hSU' : Disjoint U' S :=
        Disjoint.mono_left (erase_subset i U) hSU
      have hTU' : Disjoint U' T :=
        Disjoint.mono_left (erase_subset i U) hTU
      have hiS : i ∉ S := fun h => disjoint_left.1 hSU hiU h
      have hiT : i ∉ T := fun h => disjoint_left.1 hTU hiU h
      have hiSU' : i ∉ S ∪ U' := by
        simp only [mem_union, not_or, U']
        exact ⟨hiS, notMem_erase i U⟩
      have hiTU' : i ∉ T ∪ U' := by
        simp only [mem_union, not_or, U']
        exact ⟨hiT, notMem_erase i U⟩
      have hST' : S ∪ U' ⊆ T ∪ U' :=
        union_subset_union_left (t := U') hST
      have hincU' : f (S ∪ U') - f S ≤ f (T ∪ U') - f T :=
        ih _ hU'card hSU' hTU' rfl
      have hincI :
          f (insert i (S ∪ U')) - f (S ∪ U') ≤ f (insert i (T ∪ U')) - f (T ∪ U') :=
        fourPointSupermodular_increasing hf hST' hiSU' hiTU'
      have hSU : insert i (S ∪ U') = S ∪ U := by
        ext x
        simp only [U', mem_insert, mem_union, mem_erase]
        constructor
        · rintro (rfl | hxS | ⟨_, hxU⟩)
          · exact Or.inr hiU
          · exact Or.inl hxS
          · exact Or.inr hxU
        · rintro (hxS | hxU)
          · exact Or.inr (Or.inl hxS)
          · by_cases hxi : x = i
            · subst hxi; exact Or.inl rfl
            · exact Or.inr (Or.inr ⟨hxi, hxU⟩)
      have hTU : insert i (T ∪ U') = T ∪ U := by
        ext x
        simp only [U', mem_insert, mem_union, mem_erase]
        constructor
        · rintro (rfl | hxT | ⟨_, hxU⟩)
          · exact Or.inr hiU
          · exact Or.inl hxT
          · exact Or.inr hxU
        · rintro (hxT | hxU)
          · exact Or.inr (Or.inl hxT)
          · by_cases hxi : x = i
            · subst hxi; exact Or.inl rfl
            · exact Or.inr (Or.inr ⟨hxi, hxU⟩)
      rw [← hSU, ← hTU]
      linarith

theorem supermodular_of_fourPointSupermodular {α : Type*} [DecidableEq α]
    {f : Finset α → ℝ} (hf : FourPointSupermodular f) : Supermodular f := by
  classical
  intro A B
  have hdisjAS : Disjoint (A \ B) (A ∩ B) := disjoint_sdiff_inter A B
  have hdisjAB : Disjoint (A \ B) B := sdiff_disjoint
  have hinc :=
    fourPointSupermodular_block_increasing hf (inter_subset_right (s₁ := A) (s₂ := B))
      hdisjAS hdisjAB
  have hAU : (A ∩ B) ∪ (A \ B) = A := by
    rw [union_comm, sdiff_union_inter]
  have hBU : B ∪ (A \ B) = A ∪ B := by
    rw [union_comm, sdiff_union_self_eq_union]
  rw [hAU, hBU] at hinc
  linarith

theorem supermodular_iff_fourPointSupermodular {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) : Supermodular f ↔ FourPointSupermodular f :=
  ⟨fourPointSupermodular_of_supermodular, supermodular_of_fourPointSupermodular⟩

/-- Complement in a finite ground set. Defined here so combinatorial lemmas do
not depend on `PrincipalSubmatrix`. -/
def compl {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Finset ι) : Finset ι :=
  univ \ T

@[simp]
theorem compl_compl {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Finset ι) :
    compl (compl T) = T := by
  simp [compl]

@[simp]
theorem compl_empty {ι : Type*} [Fintype ι] [DecidableEq ι] :
    compl (∅ : Finset ι) = univ := by
  simp [compl]

@[simp]
theorem compl_univ {ι : Type*} [Fintype ι] [DecidableEq ι] :
    compl (univ : Finset ι) = ∅ := by
  simp [compl]

theorem mem_compl {ι : Type*} [Fintype ι] [DecidableEq ι] {T : Finset ι} {i : ι} :
    i ∈ compl T ↔ i ∉ T := by
  simp [compl]

theorem compl_union {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Finset ι) :
    compl (A ∪ B) = compl A ∩ compl B := by
  ext x
  simp [compl, mem_union, mem_inter, not_or]

theorem compl_inter {ι : Type*} [Fintype ι] [DecidableEq ι] (A B : Finset ι) :
    compl (A ∩ B) = compl A ∪ compl B := by
  ext x
  simp [compl, mem_union, mem_inter]
  tauto

/-- Taking complements preserves supermodularity (unions and intersections swap). -/
theorem supermodular_compl {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : Finset ι → ℝ} (hf : Supermodular f) :
    Supermodular (fun S => f (compl S)) := by
  intro A B
  have h := hf (compl A) (compl B)
  simp only
  rw [compl_union, compl_inter]
  linarith

/-- Row-wise (weak) diagonal dominance with a nonnegative diagonal:
each diagonal entry dominates the ℓ¹ mass of the rest of its row. -/
def IsDiagDominant {ι : Type*} {R : Type*} [Fintype ι] [DecidableEq ι]
    [Ring R] [LinearOrder R] [IsOrderedRing R] (M : Matrix ι ι R) : Prop :=
  ∀ i, ∑ j ∈ univ.erase i, |M i j| ≤ M i i

/-- Symmetric diagonally dominant matrix (SDD). -/
def IsSDD {ι : Type*} {R : Type*} [Fintype ι] [DecidableEq ι]
    [Ring R] [LinearOrder R] [IsOrderedRing R] (M : Matrix ι ι R) : Prop :=
  M.IsSymm ∧ IsDiagDominant M

/-- Symmetric diagonally dominant M-matrix (SDDM): an SDD matrix with strictly
positive diagonal and non-positive off-diagonal entries. -/
def IsSDDM {ι : Type*} {R : Type*} [Fintype ι] [DecidableEq ι]
    [Ring R] [LinearOrder R] [IsOrderedRing R] (M : Matrix ι ι R) : Prop :=
  IsSDD M ∧ (∀ i, 0 < M i i) ∧ (∀ i j, i ≠ j → M i j ≤ 0)

theorem IsSDDM.isSDD {ι : Type*} {R : Type*} [Fintype ι] [DecidableEq ι]
    [Ring R] [LinearOrder R] [IsOrderedRing R] {M : Matrix ι ι R} (h : IsSDDM M) :
    IsSDD M :=
  h.1

theorem IsSDDM.isSymm {ι : Type*} {R : Type*} [Fintype ι] [DecidableEq ι]
    [Ring R] [LinearOrder R] [IsOrderedRing R] {M : Matrix ι ι R} (h : IsSDDM M) :
    M.IsSymm :=
  h.1.1

theorem IsSDDM.isDiagDominant {ι : Type*} {R : Type*} [Fintype ι] [DecidableEq ι]
    [Ring R] [LinearOrder R] [IsOrderedRing R] {M : Matrix ι ι R} (h : IsSDDM M) :
    IsDiagDominant M :=
  h.1.2

theorem IsSDDM.diag_pos {ι : Type*} {R : Type*} [Fintype ι] [DecidableEq ι]
    [Ring R] [LinearOrder R] [IsOrderedRing R] {M : Matrix ι ι R} (h : IsSDDM M) (i : ι) :
    0 < M i i :=
  h.2.1 i

theorem IsSDDM.offDiag_nonpos {ι : Type*} {R : Type*} [Fintype ι] [DecidableEq ι]
    [Ring R] [LinearOrder R] [IsOrderedRing R] {M : Matrix ι ι R} (h : IsSDDM M)
    {i j : ι} (hij : i ≠ j) : M i j ≤ 0 :=
  h.2.2 i j hij

/-- A Stieltjes matrix: symmetric positive definite with nonpositive
off-diagonal entries. Equivalent to a symmetric nonsingular M-matrix. -/
def IsStieltjes {ι : Type*} (M : Matrix ι ι ℝ) : Prop :=
  M.PosDef ∧ ∀ i j, i ≠ j → M i j ≤ 0

theorem IsStieltjes.posDef {ι : Type*} {M : Matrix ι ι ℝ} (h : IsStieltjes M) :
    M.PosDef :=
  h.1

theorem IsStieltjes.offDiag_nonpos {ι : Type*} {M : Matrix ι ι ℝ} (h : IsStieltjes M)
    {i j : ι} (hij : i ≠ j) : M i j ≤ 0 :=
  h.2 i j hij

theorem IsStieltjes.isHermitian {ι : Type*} {M : Matrix ι ι ℝ} (h : IsStieltjes M) :
    M.IsHermitian :=
  h.1.isHermitian

/-- The resolvent \(K=(L+\gamma\cdot I)^{-1}\). -/
noncomputable def resolvent {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Matrix ι ι ℝ) (γ : ℝ) : Matrix ι ι ℝ :=
  (L + γ • (1 : Matrix ι ι ℝ))⁻¹

end NystromSubmodularity
