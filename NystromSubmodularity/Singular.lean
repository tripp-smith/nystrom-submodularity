import NystromSubmodularity.Stieltjes
import NystromSubmodularity.InverseTrace
import NystromSubmodularity.SmallInstanceChecks
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

/-!
# Unshifted SDDM matrices and the singular path Laplacian

Every SDDM matrix is positive semidefinite (`IsSDDM.quad_nonneg`). An
unshifted graph Laplacian may be singular, so the empty-set Nyström
error (inverse-trace of the whole matrix) is undefined. On every
*proper* complement the principal block of the path Laplacian is
invertible, and the nonempty-base four-point defect stays nonnegative
— matching Colbrook Proposition 5.5 at \(\gamma=0\).
-/

namespace NystromSubmodularity

open Matrix Finset SmallInstance

/-- The 3-path Laplacian annihilates the constants. -/
theorem pathLap3_mulVec_one :
    toReal pathLap3 *ᵥ (fun _ : Fin 3 => (1 : ℝ)) = 0 := by
  ext i
  fin_cases i
  all_goals
    simp [pathLap3, toReal, mulVec, dotProduct, Fin.sum_univ_three]
    try norm_num

theorem pathLap3_det_zero : pathLap3.det = 0 := by
  native_decide

/-- Nyström error of a possibly singular matrix, defined whenever the
complement is a proper (hence, for the path, invertible) principal
block. The empty complement is the empty-matrix convention `0`. -/
def singularNystromError {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Matrix ι ι ℚ) (S : Finset ι) : ℚ :=
  cramerNystromError L S

theorem pathLap3_error_zero :
    singularNystromError pathLap3 ({0} : Finset (Fin 3)) = 3 := by
  native_decide

theorem pathLap3_error_one :
    singularNystromError pathLap3 ({1} : Finset (Fin 3)) = 2 := by
  native_decide

theorem pathLap3_error_two :
    singularNystromError pathLap3 ({2} : Finset (Fin 3)) = 3 := by
  native_decide

theorem pathLap3_error_zero_one :
    singularNystromError pathLap3 ({0, 1} : Finset (Fin 3)) = 1 := by
  native_decide

theorem pathLap3_error_zero_two :
    singularNystromError pathLap3 ({0, 2} : Finset (Fin 3)) = 1 / 2 := by
  native_decide

theorem pathLap3_error_one_two :
    singularNystromError pathLap3 ({1, 2} : Finset (Fin 3)) = 1 := by
  native_decide

theorem pathLap3_error_univ :
    singularNystromError pathLap3 (univ : Finset (Fin 3)) = 0 := by
  native_decide

/-- Nonempty-base four-point defect on the unshifted path is positive. -/
theorem pathLap3_nonempty_fourPoint_pos :
    singularNystromError pathLap3 ({2} : Finset (Fin 3)) +
        singularNystromError pathLap3 (univ : Finset (Fin 3)) >
      singularNystromError pathLap3 ({0, 2} : Finset (Fin 3)) +
        singularNystromError pathLap3 ({1, 2} : Finset (Fin 3)) := by
  rw [pathLap3_error_two, pathLap3_error_univ, pathLap3_error_zero_two,
    pathLap3_error_one_two]
  norm_num

/-- The shifted path remains supermodular for every positive ridge,
including arbitrarily small \(\gamma>0\). -/
theorem pathLap3_shift_supermodular {γ : ℝ} (hγ : 0 < γ) :
    Supermodular (nystromError (toReal pathLap3 + γ • (1 : Matrix (Fin 3) (Fin 3) ℝ))) :=
  supermodular_compl
    (traceInv_supermodular_of_isStieltjes
      ((toReal_isSDDM pathLap3_isSDDM).add_pos_smul_one_isStieltjes hγ))

end NystromSubmodularity
