import NystromSubmodularity.Computable
import NystromSubmodularity.Counterexamples.SDDDim3
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Perturbation stability of the \(M_0\) obstruction

Colbrook notes that the four-point defect is continuous on the
positive-definite cone, so a negative defect survives a small
symmetric perturbation. This file certifies an explicit rational
neighborhood: \(M_0+\varepsilon I\) for \(\varepsilon\in\{0,1/10,1/2,1\}\)
all have a negative empty-base \((0,1)\) defect. Combined with
`nystromError_smul_scale`, a counter-example at one shift yields one
at every positive scale.
-/

namespace NystromSubmodularity
namespace Counterexamples

open Matrix Finset

/-- Ridge perturbation of \(M_0\). -/
def M0ridge (ε : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  M0 + ε • (1 : Matrix (Fin 3) (Fin 3) ℚ)

def M0ridge_delta (ε : ℚ) : ℚ :=
  cramerNystromError (M0ridge ε) (∅ : Finset (Fin 3)) +
    cramerNystromError (M0ridge ε) ({0, 1} : Finset (Fin 3)) -
      cramerNystromError (M0ridge ε) ({0} : Finset (Fin 3)) -
        cramerNystromError (M0ridge ε) ({1} : Finset (Fin 3))

theorem M0ridge_delta_zero : M0ridge_delta 0 = -7 / 2040 := by
  native_decide

theorem M0ridge_delta_tenth : M0ridge_delta (1 / 10) = -14938000 / 4814921271 := by
  native_decide

theorem M0ridge_delta_half : M0ridge_delta (1 / 2) = -1104 / 568799 := by
  native_decide

theorem M0ridge_delta_one : M0ridge_delta 1 = -1 / 1092 := by
  native_decide

theorem M0ridge_delta_neg_tenth : M0ridge_delta (1 / 10) < 0 := by
  rw [M0ridge_delta_tenth]
  norm_num

theorem M0ridge_delta_neg_half : M0ridge_delta (1 / 2) < 0 := by
  rw [M0ridge_delta_half]
  norm_num

theorem M0ridge_delta_neg_one : M0ridge_delta 1 < 0 := by
  rw [M0ridge_delta_one]
  norm_num

/-- An explicit four-point neighborhood of \(M_0\) on which the defect
stays negative. -/
theorem M0_ridge_neighborhood_neg :
    M0ridge_delta 0 < 0 ∧
      M0ridge_delta (1 / 10) < 0 ∧
        M0ridge_delta (1 / 2) < 0 ∧
          M0ridge_delta 1 < 0 := by
  refine ⟨?_, M0ridge_delta_neg_tenth, M0ridge_delta_neg_half, M0ridge_delta_neg_one⟩
  rw [M0ridge_delta_zero]
  norm_num

/-- Scale invariance: a counter-example at \(\gamma=1\) yields one at
any prescribed positive shift. -/
theorem nystromError_smul_preserves_neg_defect {ι : Type*} [Fintype ι]
    [DecidableEq ι] (c : ℝ) (M : Matrix ι ι ℝ) (A : Finset ι) (i j : ι)
    (hc : 0 < c)
    (hneg : nystromError M A + nystromError M (insert j (insert i A)) <
      nystromError M (insert i A) + nystromError M (insert j A)) :
    nystromError (c • M) A + nystromError (c • M) (insert j (insert i A)) <
      nystromError (c • M) (insert i A) + nystromError (c • M) (insert j A) := by
  have hc0 : c ≠ 0 := hc.ne'
  simp_rw [nystromError_smul_scale c _ _ hc0]
  have hinv : 0 < c⁻¹ := inv_pos.mpr hc
  nlinarith

end Counterexamples
end NystromSubmodularity
