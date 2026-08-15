import NystromSubmodularity.Computable
import NystromSubmodularity.Counterexamples.SDDDim3
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt

/-!
# Other Nyström losses on the \(M_0\) witness

Nuclear error is not the only leftover that fails diminishing returns on
Colbrook’s signed triangle. The squared Frobenius residual
\(\|M[S^{\mathsf{c}}]^{-1}\|_F^2\) and the all-ones residual quadratic
(a prediction-risk surrogate) both have a negative empty-base
\((0,1)\) four-point defect. On a singleton complement the three
Schatten comparisons collapse to the same scalar.
-/

namespace NystromSubmodularity
namespace Counterexamples

open Matrix Finset

/-- Squared Frobenius norm of a Cramer inverse. -/
def cramerFrobeniusSqInv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ) : ℚ :=
  (cramerInv M * cramerInv M).trace

/-- Squared Frobenius Nyström error, via the complementary principal inverse. -/
def cramerFrobeniusNystromSq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ) (S : Finset ι) : ℚ :=
  cramerFrobeniusSqInv (principalSubmatrix M (compl S))

/-- Sum of all entries of a Cramer inverse (all-ones quadratic form when
the matrix is symmetric). -/
def cramerInvSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ) : ℚ :=
  ∑ i : ι, ∑ j : ι, cramerInv M i j

/-- Residual quadratic form of the all-ones vector, via Theorem 2. -/
def cramerPredictionNystrom {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ) (S : Finset ι) : ℚ :=
  cramerInvSum (principalSubmatrix M (compl S))

theorem M0_frobeniusSq_empty :
    cramerFrobeniusNystromSq M0 (∅ : Finset (Fin 3)) = 883 / 2601 := by
  native_decide

theorem M0_frobeniusSq_zero :
    cramerFrobeniusNystromSq M0 ({0} : Finset (Fin 3)) = 49 / 256 := by
  native_decide

theorem M0_frobeniusSq_one :
    cramerFrobeniusNystromSq M0 ({1} : Finset (Fin 3)) = 49 / 256 := by
  native_decide

theorem M0_frobeniusSq_zero_one :
    cramerFrobeniusNystromSq M0 ({0, 1} : Finset (Fin 3)) = 1 / 25 := by
  native_decide

/-- The Frobenius norms themselves already violate diminishing returns. -/
theorem M0_frobenius_fourPoint_neg :
    Real.sqrt (883 / 2601 : ℝ) + (1 / 5 : ℝ) <
      (7 / 16 : ℝ) + (7 / 16 : ℝ) := by
  have hsq : (883 / 2601 : ℝ) < (27 / 40 : ℝ) ^ 2 := by
    norm_num
  have hsqrt : Real.sqrt (883 / 2601 : ℝ) < (27 / 40 : ℝ) :=
    (Real.sqrt_lt' (by norm_num)).mpr hsq
  linarith

theorem not_frobenius_fourPoint_of_M0 :
    cramerFrobeniusNystromSq M0 (∅ : Finset (Fin 3)) +
        cramerFrobeniusNystromSq M0 ({0, 1} : Finset (Fin 3)) <
      cramerFrobeniusNystromSq M0 ({0} : Finset (Fin 3)) +
        cramerFrobeniusNystromSq M0 ({1} : Finset (Fin 3)) := by
  rw [M0_frobeniusSq_empty, M0_frobeniusSq_zero_one, M0_frobeniusSq_zero,
    M0_frobeniusSq_one]
  norm_num

theorem M0_prediction_empty :
    cramerPredictionNystrom M0 (∅ : Finset (Fin 3)) = 23 / 17 := by
  native_decide

theorem M0_prediction_zero :
    cramerPredictionNystrom M0 ({0} : Finset (Fin 3)) = 13 / 16 := by
  native_decide

theorem M0_prediction_one :
    cramerPredictionNystrom M0 ({1} : Finset (Fin 3)) = 13 / 16 := by
  native_decide

theorem M0_prediction_zero_one :
    cramerPredictionNystrom M0 ({0, 1} : Finset (Fin 3)) = 1 / 5 := by
  native_decide

theorem M0_prediction_fourPoint_neg :
    cramerPredictionNystrom M0 (∅ : Finset (Fin 3)) +
        cramerPredictionNystrom M0 ({0, 1} : Finset (Fin 3)) <
      cramerPredictionNystrom M0 ({0} : Finset (Fin 3)) +
        cramerPredictionNystrom M0 ({1} : Finset (Fin 3)) := by
  rw [M0_prediction_empty, M0_prediction_zero_one, M0_prediction_zero,
    M0_prediction_one]
  norm_num

theorem M0_prediction_delta :
    cramerPredictionNystrom M0 (∅ : Finset (Fin 3)) +
        cramerPredictionNystrom M0 ({0, 1} : Finset (Fin 3)) -
      cramerPredictionNystrom M0 ({0} : Finset (Fin 3)) -
        cramerPredictionNystrom M0 ({1} : Finset (Fin 3)) = -49 / 680 := by
  rw [M0_prediction_empty, M0_prediction_zero_one, M0_prediction_zero,
    M0_prediction_one]
  norm_num

/-- On a singleton complement the nuclear, Frobenius, and operator
errors coincide. -/
theorem M0_singleton_losses_agree :
    cramerNystromError M0 ({0, 1} : Finset (Fin 3)) = 1 / 5 ∧
      cramerFrobeniusNystromSq M0 ({0, 1} : Finset (Fin 3)) = 1 / 25 ∧
        cramerPredictionNystrom M0 ({0, 1} : Finset (Fin 3)) = 1 / 5 :=
  ⟨M0_cramer_zero_one, M0_frobeniusSq_zero_one, M0_prediction_zero_one⟩

end Counterexamples
end NystromSubmodularity
