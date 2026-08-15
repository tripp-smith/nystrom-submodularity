import NystromSubmodularity.Stieltjes
import NystromSubmodularity.Definitions
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Neumann / closed-walk rewrite

Colbrook Proof 3.2 expands principal inverses of a Stieltjes matrix as a
Neumann series of the splitting \(B=sI-M\). This file formalizes the
splitting and the walk interpretation of the first two powers: the
length-1 traces are modular, and the length-2 closed-walk trace is
supermodular when \(B\) is entrywise nonnegative. The existing
`IsStieltjes.inv_nonneg` remains the kernel proof of inverse-nonnegativity;
the infinite series identity is not claimed.
-/

namespace NystromSubmodularity

open Matrix Finset

/-- Splitting matrix \(B=sI-M\). -/
def neumannSplit {ι : Type*} [DecidableEq ι] (s : ℝ) (M : Matrix ι ι ℝ) :
    Matrix ι ι ℝ :=
  s • (1 : Matrix ι ι ℝ) - M

/-- For a Stieltjes matrix, any \(s\) at least the largest diagonal entry
makes the splitting entrywise nonnegative. -/
theorem neumannSplit_nonneg {ι : Type*} [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : IsStieltjes M) {s : ℝ}
    (hs : ∀ i : ι, M i i ≤ s) (i j : ι) :
    0 ≤ neumannSplit s M i j := by
  unfold neumannSplit
  by_cases hij : i = j
  · subst hij
    simp
    linarith [hs i]
  · have h1 : (1 : Matrix ι ι ℝ) i j = 0 := Matrix.one_apply_ne hij
    simp [h1, Matrix.sub_apply, Matrix.smul_apply]
    exact hM.offDiag_nonpos hij

/-- Length-1 closed-walk trace \(\operatorname{tr}(B[T])=\sum_{i\in T}B_{ii}\). -/
def walkTraceOne {ι : Type*} (B : Matrix ι ι ℝ) (T : Finset ι) : ℝ :=
  ∑ i ∈ T, B i i

/-- Length-2 closed-walk trace \(\sum_{i,j\in T}B_{ij}B_{ji}\). -/
def walkTraceTwo {ι : Type*} (B : Matrix ι ι ℝ) (T : Finset ι) : ℝ :=
  ∑ i ∈ T, ∑ j ∈ T, B i j * B j i

theorem walkTraceOne_eq_trace {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ)
    (T : Finset ι) :
    walkTraceOne B T = (principalSubmatrix B T).trace := by
  simp [walkTraceOne, Matrix.trace, principalSubmatrix, Matrix.diag]
  exact (Finset.sum_attach T (fun i => B i i)).symm

theorem walkTraceOne_modular {ι : Type*} [DecidableEq ι] (B : Matrix ι ι ℝ) :
    Supermodular (walkTraceOne B) ∧ Submodular (walkTraceOne B) := by
  constructor
  · intro A C
    simp [walkTraceOne, sum_union_inter]
  · intro A C
    simp [walkTraceOne, sum_union_inter]

theorem indicator_mem_pair_supermodular {ι : Type*} [DecidableEq ι] (i j : ι) :
    Supermodular (fun T : Finset ι => if i ∈ T ∧ j ∈ T then (1 : ℝ) else 0) := by
  intro A C
  by_cases hiA : i ∈ A <;> by_cases hjA : j ∈ A <;>
    by_cases hiC : i ∈ C <;> by_cases hjC : j ∈ C <;>
      simp [hiA, hjA, hiC, hjC, mem_union, mem_inter]

lemma walkTraceTwo_as_ite {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (T : Finset ι) :
    walkTraceTwo B T =
      ∑ i : ι, ∑ j : ι,
        B i j * B j i * (if i ∈ T ∧ j ∈ T then (1 : ℝ) else 0) := by
  unfold walkTraceTwo
  have hT : T = (univ : Finset ι).filter (· ∈ T) := by
    ext x; simp
  conv_lhs => rw [hT]
  simp [ite_and, mul_ite, mul_zero, mul_one]

theorem walkTraceTwo_supermodular {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : ∀ i j : ι, 0 ≤ B i j) :
    Supermodular (walkTraceTwo B) := by
  intro A C
  have hw (i j : ι) : 0 ≤ B i j * B j i := mul_nonneg (hB i j) (hB j i)
  have hcoeff (i j : ι) :
      B i j * B j i *
          ((if i ∈ A ∧ j ∈ A then (1 : ℝ) else 0) +
            (if i ∈ C ∧ j ∈ C then (1 : ℝ) else 0)) ≤
        B i j * B j i *
          ((if i ∈ A ∪ C ∧ j ∈ A ∪ C then (1 : ℝ) else 0) +
            (if i ∈ A ∩ C ∧ j ∈ A ∩ C then (1 : ℝ) else 0)) := by
    have hsm := indicator_mem_pair_supermodular (i := i) (j := j) A C
    nlinarith [hw i j, hsm]
  rw [walkTraceTwo_as_ite, walkTraceTwo_as_ite, walkTraceTwo_as_ite,
    walkTraceTwo_as_ite]
  simp_rw [← Finset.sum_add_distrib, ← mul_add]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hcoeff i j

/-- Partial Neumann sum of walk traces, as in Colbrook (12) before the
limit. Each finite sum is supermodular when the splitting is nonnegative. -/
noncomputable def neumannPartial {ι : Type*} (s : ℝ) (B : Matrix ι ι ℝ) (N : ℕ)
    (T : Finset ι) : ℝ :=
  (T.card : ℝ) / s +
    walkTraceOne B T / s ^ 2 +
      (if N = 0 then 0 else walkTraceTwo B T / s ^ 3)

theorem neumannPartial_supermodular {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℝ) (hs : 0 < s) (B : Matrix ι ι ℝ) (hB : ∀ i j : ι, 0 ≤ B i j)
    (N : ℕ) :
    Supermodular (neumannPartial s B N) := by
  intro A C
  have hcard : ((A ∪ C).card : ℝ) / s + ((A ∩ C).card : ℝ) / s =
      (A.card : ℝ) / s + (C.card : ℝ) / s := by
    have := congrArg (fun n : ℕ => (n : ℝ) / s) (card_union_add_card_inter A C)
    simpa [add_div] using this
  have h1 := (walkTraceOne_modular B).1 A C
  have h2 := walkTraceTwo_supermodular B hB A C
  have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
  have hs3 : 0 < s ^ 3 := pow_pos hs 3
  have h1d : walkTraceOne B A / s ^ 2 + walkTraceOne B C / s ^ 2 ≤
      walkTraceOne B (A ∪ C) / s ^ 2 + walkTraceOne B (A ∩ C) / s ^ 2 := by
    simpa [add_div] using div_le_div_of_nonneg_right h1 hs2.le
  have h2d : walkTraceTwo B A / s ^ 3 + walkTraceTwo B C / s ^ 3 ≤
      walkTraceTwo B (A ∪ C) / s ^ 3 + walkTraceTwo B (A ∩ C) / s ^ 3 := by
    simpa [add_div] using div_le_div_of_nonneg_right h2 hs3.le
  simp only [neumannPartial]
  split_ifs
  · linarith
  · linarith

end NystromSubmodularity
