import NystromSubmodularity.Counterexamples.Greedy
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Data.Rat.Cast.Order

/-!
# Column-pivoted QR first-column selection

Golub–Businger CPQR on a matrix \(A\) selects, as its first column, an
index maximising the Euclidean column norm. Exact greedy for nuclear
Nyström error instead maximises \(\|K_{:,j}\|_2^2/K_{jj}\).

On Colbrook’s \(M_0\), those rules agree: both pick index \(2\), which
lies in no optimal pair. This is a machine-checked CPQR counterexample
(Milestone E). It is not a polynomial approximation theorem.
-/

namespace NystromSubmodularity
namespace Counterexamples

open Matrix Finset

/-- Squared Euclidean norm of column `j`. -/
def columnNormSq {ι : Type*} [Fintype ι] {R : Type*} [Semiring R]
    (A : Matrix ι ι R) (j : ι) : R :=
  ∑ i, A i j * A i j

/-- First Golub–Businger CPQR column: a maximiser of `columnNormSq`. -/
def IsCPQRFirst {ι : Type*} [Fintype ι] {R : Type*} [Semiring R] [LE R]
    (A : Matrix ι ι R) (j : ι) : Prop :=
  ∀ k, columnNormSq A k ≤ columnNormSq A j

lemma M0_adjugate_00 : M0.adjugate (0 : Fin 3) 0 = 16 := by
  rw [adjugate_fin_three]
  simp [M0]
  norm_num

lemma M0_adjugate_10 : M0.adjugate (1 : Fin 3) 0 = -1 := by
  rw [adjugate_fin_three]
  simp [M0]
  norm_num

lemma M0_adjugate_20 : M0.adjugate (2 : Fin 3) 0 = 6 := by
  rw [adjugate_fin_three]
  simp [M0]
  norm_num

lemma M0_adjugate_01 : M0.adjugate (0 : Fin 3) 1 = -1 := by
  rw [adjugate_fin_three]
  simp [M0]
  norm_num

lemma M0_adjugate_11 : M0.adjugate (1 : Fin 3) 1 = 16 := by
  rw [adjugate_fin_three]
  simp [M0]
  norm_num

lemma M0_adjugate_21 : M0.adjugate (2 : Fin 3) 1 = 6 := by
  rw [adjugate_fin_three]
  simp [M0]
  norm_num

lemma M0_adjugate_02 : M0.adjugate (0 : Fin 3) 2 = 6 := by
  rw [adjugate_fin_three]
  simp [M0]
  norm_num

lemma M0_adjugate_12 : M0.adjugate (1 : Fin 3) 2 = 6 := by
  rw [adjugate_fin_three]
  simp [M0]
  norm_num

lemma M0_adjugate_22 : M0.adjugate (2 : Fin 3) 2 = 15 := by
  rw [adjugate_fin_three]
  simp [M0]
  norm_num

lemma M0_cramerInv_00 : cramerInv M0 (0 : Fin 3) 0 = 16 / 51 := by
  simp [cramerInv, M0_det, M0_adjugate_00]
  norm_num

lemma M0_cramerInv_10 : cramerInv M0 (1 : Fin 3) 0 = -1 / 51 := by
  simp [cramerInv, M0_det, M0_adjugate_10]
  norm_num

lemma M0_cramerInv_20 : cramerInv M0 (2 : Fin 3) 0 = 6 / 51 := by
  simp [cramerInv, M0_det, M0_adjugate_20]
  norm_num

lemma M0_cramerInv_01 : cramerInv M0 (0 : Fin 3) 1 = -1 / 51 := by
  simp [cramerInv, M0_det, M0_adjugate_01]
  norm_num

lemma M0_cramerInv_11 : cramerInv M0 (1 : Fin 3) 1 = 16 / 51 := by
  simp [cramerInv, M0_det, M0_adjugate_11]
  norm_num

lemma M0_cramerInv_21 : cramerInv M0 (2 : Fin 3) 1 = 6 / 51 := by
  simp [cramerInv, M0_det, M0_adjugate_21]
  norm_num

lemma M0_cramerInv_02 : cramerInv M0 (0 : Fin 3) 2 = 6 / 51 := by
  simp [cramerInv, M0_det, M0_adjugate_02]
  norm_num

lemma M0_cramerInv_12 : cramerInv M0 (1 : Fin 3) 2 = 6 / 51 := by
  simp [cramerInv, M0_det, M0_adjugate_12]
  norm_num

lemma M0_cramerInv_22 : cramerInv M0 (2 : Fin 3) 2 = 15 / 51 := by
  simp [cramerInv, M0_det, M0_adjugate_22]
  norm_num

theorem M0_cramerInv_columnNormSq_zero :
    columnNormSq (cramerInv M0) (0 : Fin 3) = 293 / 2601 := by
  simp [columnNormSq, Fin.sum_univ_three, M0_cramerInv_00, M0_cramerInv_10,
    M0_cramerInv_20]
  norm_num

theorem M0_cramerInv_columnNormSq_one :
    columnNormSq (cramerInv M0) (1 : Fin 3) = 293 / 2601 := by
  simp [columnNormSq, Fin.sum_univ_three, M0_cramerInv_01, M0_cramerInv_11,
    M0_cramerInv_21]
  norm_num

theorem M0_cramerInv_columnNormSq_two :
    columnNormSq (cramerInv M0) (2 : Fin 3) = 297 / 2601 := by
  simp [columnNormSq, Fin.sum_univ_three, M0_cramerInv_02, M0_cramerInv_12,
    M0_cramerInv_22]
  norm_num

lemma fin3_eq_zero_one_two (k : Fin 3) : k = 0 ∨ k = 1 ∨ k = 2 := by
  revert k
  decide

theorem M0_cpqr_first_is_two : IsCPQRFirst (cramerInv M0) (2 : Fin 3) := by
  intro k
  rcases fin3_eq_zero_one_two k with rfl | rfl | rfl
  · rw [M0_cramerInv_columnNormSq_zero, M0_cramerInv_columnNormSq_two]
    norm_num
  · rw [M0_cramerInv_columnNormSq_one, M0_cramerInv_columnNormSq_two]
    norm_num
  · rw [M0_cramerInv_columnNormSq_two]

theorem M0_cpqr_first_unique {j : Fin 3} (hj : IsCPQRFirst (cramerInv M0) j) :
    j = 2 := by
  have h2 := hj 2
  rw [M0_cramerInv_columnNormSq_two] at h2
  rcases fin3_eq_zero_one_two j with rfl | rfl | rfl
  · rw [M0_cramerInv_columnNormSq_zero] at h2
    have hcontra : ¬ ((297 : ℚ) / 2601 ≤ 293 / 2601) := by norm_num
    exact (hcontra h2).elim
  · rw [M0_cramerInv_columnNormSq_one] at h2
    have hcontra : ¬ ((297 : ℚ) / 2601 ≤ 293 / 2601) := by norm_num
    exact (hcontra h2).elim
  · rfl

theorem M0_cramer_zero_two :
    cramerNystromError M0 ({0, 2} : Finset (Fin 3)) = 1 / 4 := by
  have hc : compl ({0, 2} : Finset (Fin 3)) = {1} := by decide
  rw [cramerNystromError, hc, cramerTraceInv_singleton]
  simp [M0]

theorem M0_cramer_one_two :
    cramerNystromError M0 ({1, 2} : Finset (Fin 3)) = 1 / 4 := by
  have hc : compl ({1, 2} : Finset (Fin 3)) = {0} := by decide
  rw [cramerNystromError, hc, cramerTraceInv_singleton]
  simp [M0]

/-- Milestone E counterexample: CPQR’s first column on \(M_0^{-1}\) is
index \(2\), which lies in no optimal pair. The pair residual ratio is
the certified \(5/4\). -/
theorem M0_cpqr_misses_optimal_pair :
    IsCPQRFirst (cramerInv M0) (2 : Fin 3) ∧
      (∀ s : Finset (Fin 3), s.card = 2 → s ≠ {0, 1} →
        cramerNystromError M0 ({0, 1} : Finset (Fin 3)) <
          cramerNystromError M0 s) ∧
      cramerNystromError M0 ({0, 2} : Finset (Fin 3)) /
          cramerNystromError M0 ({0, 1} : Finset (Fin 3)) = 5 / 4 := by
  refine ⟨M0_cpqr_first_is_two, ?_, ?_⟩
  · intro s hs hne
    rcases fin3_card_two hs with rfl | rfl | rfl
    · exact (hne rfl).elim
    · rw [M0_cramer_zero_one, M0_cramer_zero_two]
      norm_num
    · rw [M0_cramer_zero_one, M0_cramer_one_two]
      norm_num
  · rw [M0_cramer_zero_two, M0_cramer_zero_one]
    norm_num

end Counterexamples
end NystromSubmodularity
