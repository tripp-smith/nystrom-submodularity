import NystromSubmodularity.Computable
import NystromSubmodularity.Definitions
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.Rat.Cast.Order

/-!
# A minimal 3×3 SDD obstruction

Colbrook (arXiv:2607.19282), equations (20)–(22): the signed-triangle family
at the rational parameter \(t=2\), together with a strictly diagonally
dominant perturbation.

Living numbers (γ = 1):
* \(\mathcal{E}(\emptyset)=47/51\), \(\mathcal{E}(\{0\})=\mathcal{E}(\{1\})=9/16\),
  \(\mathcal{E}(\{0,1\})=1/5\), hence \(\Delta=-7/2040<0\).
-/

namespace NystromSubmodularity
namespace Counterexamples

open Matrix Finset

/-- Colbrook's rational SDD matrix \(L(2)\). -/
def L0 : Matrix (Fin 3) (Fin 3) ℚ :=
  !![3, 1, -2; 1, 3, -2; -2, -2, 4]

/-- Precision matrix \(M=L_0+I\). -/
def M0 : Matrix (Fin 3) (Fin 3) ℚ :=
  !![4, 1, -2; 1, 4, -2; -2, -2, 5]

/-- Strictly SDD perturbation \(L^\sharp\). -/
def Lsharp : Matrix (Fin 3) (Fin 3) ℚ :=
  !![4, 1, -2; 1, 4, -2; -2, -2, 5]

/-- Precision matrix \(M^\sharp=L^\sharp+I\). -/
def Msharp : Matrix (Fin 3) (Fin 3) ℚ :=
  !![5, 1, -2; 1, 5, -2; -2, -2, 6]

theorem L0_eq_M0_sub_one : M0 = L0 + 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [L0, M0] <;> norm_num

theorem Lsharp_eq_Msharp_sub_one : Msharp = Lsharp + 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lsharp, Msharp] <;> norm_num

theorem L0_isSymm : L0.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [L0]

theorem L0_isDiagDominant : IsDiagDominant L0 := by
  intro i
  fin_cases i <;> native_decide

theorem L0_isSDD : IsSDD L0 :=
  ⟨L0_isSymm, L0_isDiagDominant⟩

theorem Lsharp_isSymm : Lsharp.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lsharp]

theorem Lsharp_isDiagDominant : IsDiagDominant Lsharp := by
  intro i
  fin_cases i <;> native_decide

theorem Lsharp_isSDD : IsSDD Lsharp :=
  ⟨Lsharp_isSymm, Lsharp_isDiagDominant⟩

theorem L0_toReal_isSDD : IsSDD (toReal L0) :=
  toReal_isSDD L0_isSDD

theorem Lsharp_toReal_isSDD : IsSDD (toReal Lsharp) :=
  toReal_isSDD Lsharp_isSDD

/-- Explicit quadratic form of `toReal L0`: a sum of squares. -/
theorem L0_quadratic (x : Fin 3 → ℝ) :
    star x ⬝ᵥ (toReal L0 *ᵥ x) =
      2 * (x 0 - x 2) ^ 2 + 2 * (x 1 - x 2) ^ 2 + (x 0 + x 1) ^ 2 := by
  simp [dotProduct, mulVec, toReal, L0, Fin.sum_univ_three, Pi.star_apply]
  ring

theorem L0_posDef : (toReal L0).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · rw [isHermitian_iff_isSymm]
    exact toReal_isSymm L0_isSymm
  · intro x hx
    have hform := L0_quadratic x
    have hsq : 0 ≤ 2 * (x 0 - x 2) ^ 2 + 2 * (x 1 - x 2) ^ 2 + (x 0 + x 1) ^ 2 := by
      nlinarith [sq_nonneg (x 0 - x 2), sq_nonneg (x 1 - x 2), sq_nonneg (x 0 + x 1)]
    have hpos :
        0 < 2 * (x 0 - x 2) ^ 2 + 2 * (x 1 - x 2) ^ 2 + (x 0 + x 1) ^ 2 := by
      by_contra h
      have hz :
          2 * (x 0 - x 2) ^ 2 + 2 * (x 1 - x 2) ^ 2 + (x 0 + x 1) ^ 2 = 0 :=
        le_antisymm (le_of_not_gt h) hsq
      have h0 : x 0 - x 2 = 0 := by
        nlinarith [sq_nonneg (x 0 - x 2), sq_nonneg (x 1 - x 2), sq_nonneg (x 0 + x 1)]
      have h1 : x 1 - x 2 = 0 := by
        nlinarith [sq_nonneg (x 0 - x 2), sq_nonneg (x 1 - x 2), sq_nonneg (x 0 + x 1)]
      have h2 : x 0 + x 1 = 0 := by
        nlinarith [sq_nonneg (x 0 - x 2), sq_nonneg (x 1 - x 2), sq_nonneg (x 0 + x 1)]
      have hx0 : x 0 = 0 := by linarith
      have hx1 : x 1 = 0 := by linarith
      have hx2 : x 2 = 0 := by linarith
      apply hx
      funext k
      fin_cases k <;> assumption
    rw [hform]
    exact hpos

theorem M0_toReal_eq : toReal M0 = toReal L0 + 1 := by
  rw [L0_eq_M0_sub_one, toReal_add, toReal_one]

theorem M0_isSymm : M0.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [M0]

theorem M0_posDef : (toReal M0).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · rw [isHermitian_iff_isSymm]
    exact toReal_isSymm M0_isSymm
  · intro x hx
    have hM : star x ⬝ᵥ (toReal M0 *ᵥ x) =
        star x ⬝ᵥ (toReal L0 *ᵥ x) + star x ⬝ᵥ x := by
      rw [M0_toReal_eq, add_mulVec, dotProduct_add, one_mulVec]
    have hL : 0 ≤ star x ⬝ᵥ (toReal L0 *ᵥ x) := by
      rw [L0_quadratic]
      nlinarith [sq_nonneg (x 0 - x 2), sq_nonneg (x 1 - x 2), sq_nonneg (x 0 + x 1)]
    have hnorm : 0 < star x ⬝ᵥ x := by
      have hstar : star x = x := funext fun i => star_trivial (x i)
      rw [hstar]
      have : x ⬝ᵥ x = 0 ↔ x = 0 := dotProduct_self_eq_zero
      have hne : x ⬝ᵥ x ≠ 0 := this.not.mpr hx
      have hnn : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
      exact lt_of_le_of_ne hnn hne.symm
    rw [hM]
    linarith

/-- Certified Colbrook values of the Nyström error of `M0`. -/
theorem M0_cramer_empty : cramerNystromError M0 (∅ : Finset (Fin 3)) = 47 / 51 := by
  native_decide

theorem M0_cramer_zero : cramerNystromError M0 ({0} : Finset (Fin 3)) = 9 / 16 := by
  native_decide

theorem M0_cramer_one : cramerNystromError M0 ({1} : Finset (Fin 3)) = 9 / 16 := by
  native_decide

theorem M0_cramer_zero_one :
    cramerNystromError M0 ({0, 1} : Finset (Fin 3)) = 1 / 5 := by
  native_decide

/-- The four-point defect at \(A=\emptyset\), \(i=0\), \(j=1\). -/
theorem M0_delta :
    cramerNystromSupermodularDiff M0 ({0} : Finset (Fin 3)) {1} = -7 / 2040 := by
  native_decide

theorem M0_delta_neg :
    cramerNystromError M0 (∅ : Finset (Fin 3)) +
        cramerNystromError M0 ({0, 1} : Finset (Fin 3)) <
      cramerNystromError M0 ({0} : Finset (Fin 3)) +
        cramerNystromError M0 ({1} : Finset (Fin 3)) := by
  native_decide

theorem Msharp_delta_neg :
    cramerNystromError Msharp (∅ : Finset (Fin 3)) +
        cramerNystromError Msharp ({0, 1} : Finset (Fin 3)) <
      cramerNystromError Msharp ({0} : Finset (Fin 3)) +
        cramerNystromError Msharp ({1} : Finset (Fin 3)) := by
  native_decide

theorem not_supermodular_cramerNystromError_M0 :
    ¬ ∀ A B : Finset (Fin 3),
        cramerNystromError M0 A + cramerNystromError M0 B ≤
          cramerNystromError M0 (A ∪ B) + cramerNystromError M0 (A ∩ B) := by
  intro h
  have h01 := h ({0} : Finset (Fin 3)) ({1} : Finset (Fin 3))
  have hunion : ({0} : Finset (Fin 3)) ∪ {1} = {0, 1} := by simp
  have hinter : ({0} : Finset (Fin 3)) ∩ {1} = ∅ := by simp
  rw [hunion, hinter, M0_cramer_zero, M0_cramer_one, M0_cramer_zero_one, M0_cramer_empty] at h01
  norm_num at h01

/-- The Nyström error of `toReal M0` fails supermodularity. -/
theorem not_supermodular_nystromError_M0 :
    ¬ Supermodular (nystromError (toReal M0)) := by
  intro hf
  have h := hf ({0} : Finset (Fin 3)) ({1} : Finset (Fin 3))
  have hunion : ({0} : Finset (Fin 3)) ∪ {1} = {0, 1} := by simp
  have hinter : ({0} : Finset (Fin 3)) ∩ {1} = ∅ := by simp
  rw [hunion, hinter] at h
  have h0 : nystromError (toReal M0) ({0} : Finset (Fin 3)) = ((9 / 16 : ℚ) : ℝ) := by
    rw [← toReal_nystromError, M0_cramer_zero]
  have h1 : nystromError (toReal M0) ({1} : Finset (Fin 3)) = ((9 / 16 : ℚ) : ℝ) := by
    rw [← toReal_nystromError, M0_cramer_one]
  have h01 : nystromError (toReal M0) ({0, 1} : Finset (Fin 3)) = ((1 / 5 : ℚ) : ℝ) := by
    rw [← toReal_nystromError, M0_cramer_zero_one]
  have hemp : nystromError (toReal M0) (∅ : Finset (Fin 3)) = ((47 / 51 : ℚ) : ℝ) := by
    rw [← toReal_nystromError, M0_cramer_empty]
  rw [h0, h1, h01, hemp] at h
  -- 9/16 + 9/16 ≤ 1/5 + 47/51 is false
  norm_num at h

end Counterexamples
end NystromSubmodularity
