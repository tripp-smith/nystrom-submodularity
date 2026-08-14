import NystromSubmodularity.InverseTrace
import NystromSubmodularity.Computable
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

/-!
# Minimality of the SDD obstruction

Colbrook Proposition 5.5: if the unselected set has two indices, the
four-point defect of the Nyström error is nonnegative for every
positive-definite precision matrix. Consequently dimension three is
minimal for an empty-base SDD failure, and a nonempty-base failure
requires dimension at least four.
-/

namespace NystromSubmodularity

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false

/-- Colbrook (27): the terminal \(2\times 2\) four-point defect. -/
theorem two_by_two_nystrom_defect {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.PosDef) :
    0 ≤ Q⁻¹.trace - (Q 0 0)⁻¹ - (Q 1 1)⁻¹ :=
  two_by_two_inv_trace_defect hQ

lemma nystromError_of_compl_pair {M : Matrix ι ι ℝ} {A : Finset ι} {i j : ι}
    (hA : compl A = {i, j}) :
    nystromError M A = traceInv M {i, j} := by
  simp [nystromError, hA]

lemma nystromError_insert_of_compl_pair {M : Matrix ι ι ℝ} {A : Finset ι} {i j : ι}
    (_hi : i ∉ A) (hij : i ≠ j) (hA : compl A = {i, j}) :
    nystromError M (insert i A) = traceInv M {j} := by
  have : compl (insert i A) = {j} := by
    rw [compl_insert, hA, erase_pair_left hij]
  simp [nystromError, this]

/-- If \(A^{\mathsf{c}}=\{i,j\}\), the four-point defect is nonnegative
(Colbrook Proposition 5.5). -/
theorem nystromError_fourPoint_of_compl_pair {M : Matrix ι ι ℝ} (hM : M.PosDef)
    {A : Finset ι} {i j : ι} (hi : i ∉ A) (_hj : j ∉ A) (hij : i ≠ j)
    (hA : compl A = {i, j}) :
    nystromError M (insert i A) + nystromError M (insert j A) ≤
      nystromError M A + nystromError M (insert j (insert i A)) := by
  have hAi := nystromError_insert_of_compl_pair (M := M) hi hij hA
  have hAj : nystromError M (insert j A) = traceInv M {i} := by
    have : compl (insert j A) = {i} := by
      rw [compl_insert, hA, erase_pair_right hij]
    simp [nystromError, this]
  have hAij : nystromError M (insert j (insert i A)) = 0 := by
    have : insert j (insert i A) = univ := by
      ext x
      constructor
      · intro; exact mem_univ _
      · intro _
        have hx : x ∈ compl A ∨ x ∈ A := by
          by_cases h : x ∈ A
          · exact Or.inr h
          · exact Or.inl (mem_compl.mpr h)
        rcases hx with hx | hx
        · rw [hA] at hx
          rcases (mem_insert.mp hx) with rfl | hx'
          · simp
          · simp [mem_singleton.mp hx']
        · simp [hx]
    rw [nystromError, this, compl_univ, traceInv_empty]
  rw [nystromError_of_compl_pair hA, hAi, hAj, hAij, traceInv_pair M hij,
    traceInv_singleton M i, traceInv_singleton M j]
  have hQ : (pairDiagBlock M i j).PosDef := pairDiagBlock_posDef hM hij
  have hdef := two_by_two_inv_trace_defect hQ
  have h00 : pairDiagBlock M i j 0 0 = M i i := rfl
  have h11 : pairDiagBlock M i j 1 1 = M j j := rfl
  rw [h00, h11] at hdef
  linarith [hdef]

lemma pair_of_card_two {A : Finset ι} {i j : ι} (hij : i ≠ j)
    (hi : i ∈ A) (hj : j ∈ A) (hcard : A.card = 2) : A = {i, j} := by
  have hsub : ({i, j} : Finset ι) ⊆ A := by
    intro y hy
    simp at hy
    rcases hy with rfl | rfl <;> assumption
  have hcard' : ({i, j} : Finset ι).card = 2 := by simp [hij]
  exact (Finset.eq_of_subset_of_card_le hsub (by simp [hcard, hcard'])).symm

lemma compl_eq_pair_of_not_mem {A : Finset ι} {i j : ι}
    (hi : i ∉ A) (hj : j ∉ A) (hij : i ≠ j)
    (hcard : (compl A).card = 2) : compl A = {i, j} := by
  apply pair_of_card_two hij
  · exact mem_compl.mpr hi
  · exact mem_compl.mpr hj
  · exact hcard

/-- On two (or fewer) indices, every positive-definite precision matrix has
supermodular Nyström error. Dimension three is therefore minimal for an
SDD obstruction. -/
theorem nystromError_supermodular_of_card_le_two {M : Matrix ι ι ℝ}
    (hM : M.PosDef) (hcard : Fintype.card ι ≤ 2) :
    Supermodular (nystromError M) := by
  refine supermodular_of_fourPointSupermodular ?_
  intro A i j hij hi hj
  have hsubset : ({i, j} : Finset ι) ⊆ compl A := by
    intro x hx
    simp at hx
    rcases hx with rfl | rfl
    · exact mem_compl.mpr hi
    · exact mem_compl.mpr hj
  have hpair : ({i, j} : Finset ι).card = 2 := by simp [hij]
  have hle : 2 ≤ (compl A).card := hpair ▸ card_le_card hsubset
  have hcompl_le : (compl A).card ≤ Fintype.card ι := card_le_univ _
  have : (compl A).card = 2 := le_antisymm (hcompl_le.trans hcard) hle
  have hA : compl A = {i, j} := compl_eq_pair_of_not_mem hi hj hij this
  have := nystromError_fourPoint_of_compl_pair hM hi hj hij hA
  linarith

/-- A nonempty base on at most three indices cannot produce a negative
four-point defect (the complement then has size at most two). -/
theorem nystromError_fourPoint_nonempty_of_card_le_three {M : Matrix ι ι ℝ}
    (hM : M.PosDef) (hcard : Fintype.card ι ≤ 3) {A : Finset ι} {i j : ι}
    (hAne : A.Nonempty) (hij : i ≠ j) (hi : i ∉ A) (hj : j ∉ A) :
    nystromError M (insert i A) + nystromError M (insert j A) ≤
      nystromError M A + nystromError M (insert j (insert i A)) := by
  have hsubset : ({i, j} : Finset ι) ⊆ compl A := by
    intro x hx
    simp at hx
    rcases hx with rfl | rfl
    · exact mem_compl.mpr hi
    · exact mem_compl.mpr hj
  have hpair : ({i, j} : Finset ι).card = 2 := by simp [hij]
  have hge : 2 ≤ (compl A).card := hpair ▸ card_le_card hsubset
  have hApos : 1 ≤ A.card := Nat.succ_le_of_lt (Nonempty.card_pos hAne)
  have hsum : A.card + (compl A).card = Fintype.card ι := by
    rw [compl, add_comm, card_sdiff_add_card_eq_card (subset_univ A), card_univ]
  have hle : (compl A).card ≤ 2 := by
    have : A.card + (compl A).card ≤ 3 := hsum ▸ hcard
    linarith [hApos]
  have h2 : (compl A).card = 2 := le_antisymm hle hge
  have hApair : compl A = {i, j} := compl_eq_pair_of_not_mem hi hj hij h2
  exact nystromError_fourPoint_of_compl_pair hM hi hj hij hApair

end NystromSubmodularity
