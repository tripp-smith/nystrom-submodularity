import NystromSubmodularity.Computable
import NystromSubmodularity.Definitions
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
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

lemma sum_erase_fin3_zero (f : Fin 3 → ℚ) :
    ∑ j ∈ univ.erase (0 : Fin 3), f j = f 1 + f 2 := by
  have h : univ.erase (0 : Fin 3) = ({1, 2} : Finset (Fin 3)) := by decide
  rw [h, Finset.sum_pair (by decide : (1 : Fin 3) ≠ 2)]

lemma sum_erase_fin3_one (f : Fin 3 → ℚ) :
    ∑ j ∈ univ.erase (1 : Fin 3), f j = f 0 + f 2 := by
  have h : univ.erase (1 : Fin 3) = ({0, 2} : Finset (Fin 3)) := by decide
  rw [h, Finset.sum_pair (by decide : (0 : Fin 3) ≠ 2)]

lemma sum_erase_fin3_two (f : Fin 3 → ℚ) :
    ∑ j ∈ univ.erase (2 : Fin 3), f j = f 0 + f 1 := by
  have h : univ.erase (2 : Fin 3) = ({0, 1} : Finset (Fin 3)) := by decide
  rw [h, Finset.sum_pair (by decide : (0 : Fin 3) ≠ 1)]

lemma L0_00 : L0 (0 : Fin 3) (0 : Fin 3) = 3 := rfl
lemma L0_01 : L0 (0 : Fin 3) (1 : Fin 3) = 1 := rfl
lemma L0_02 : L0 (0 : Fin 3) (2 : Fin 3) = -2 := rfl
lemma L0_10 : L0 (1 : Fin 3) (0 : Fin 3) = 1 := rfl
lemma L0_11 : L0 (1 : Fin 3) (1 : Fin 3) = 3 := rfl
lemma L0_12 : L0 (1 : Fin 3) (2 : Fin 3) = -2 := rfl
lemma L0_20 : L0 (2 : Fin 3) (0 : Fin 3) = -2 := rfl
lemma L0_21 : L0 (2 : Fin 3) (1 : Fin 3) = -2 := rfl
lemma L0_22 : L0 (2 : Fin 3) (2 : Fin 3) = 4 := rfl

lemma L0_row0_dom :
    ∑ j ∈ univ.erase (0 : Fin 3), |L0 (0 : Fin 3) j| ≤ L0 (0 : Fin 3) 0 := by
  rw [sum_erase_fin3_zero, L0_01, L0_02, L0_00]
  norm_num

lemma L0_row1_dom :
    ∑ j ∈ univ.erase (1 : Fin 3), |L0 (1 : Fin 3) j| ≤ L0 (1 : Fin 3) 1 := by
  rw [sum_erase_fin3_one, L0_10, L0_12, L0_11]
  norm_num

lemma L0_row2_dom :
    ∑ j ∈ univ.erase (2 : Fin 3), |L0 (2 : Fin 3) j| ≤ L0 (2 : Fin 3) 2 := by
  rw [sum_erase_fin3_two, L0_20, L0_21, L0_22]
  norm_num

theorem L0_isDiagDominant : IsDiagDominant L0 := by
  intro i
  fin_cases i
  · exact L0_row0_dom
  · exact L0_row1_dom
  · exact L0_row2_dom

theorem L0_isSDD : IsSDD L0 :=
  ⟨L0_isSymm, L0_isDiagDominant⟩

theorem Lsharp_isSymm : Lsharp.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lsharp]

lemma Lsharp_00 : Lsharp (0 : Fin 3) (0 : Fin 3) = 4 := rfl
lemma Lsharp_01 : Lsharp (0 : Fin 3) (1 : Fin 3) = 1 := rfl
lemma Lsharp_02 : Lsharp (0 : Fin 3) (2 : Fin 3) = -2 := rfl
lemma Lsharp_10 : Lsharp (1 : Fin 3) (0 : Fin 3) = 1 := rfl
lemma Lsharp_11 : Lsharp (1 : Fin 3) (1 : Fin 3) = 4 := rfl
lemma Lsharp_12 : Lsharp (1 : Fin 3) (2 : Fin 3) = -2 := rfl
lemma Lsharp_20 : Lsharp (2 : Fin 3) (0 : Fin 3) = -2 := rfl
lemma Lsharp_21 : Lsharp (2 : Fin 3) (1 : Fin 3) = -2 := rfl
lemma Lsharp_22 : Lsharp (2 : Fin 3) (2 : Fin 3) = 5 := rfl

lemma Lsharp_row0_dom :
    ∑ j ∈ univ.erase (0 : Fin 3), |Lsharp (0 : Fin 3) j| ≤ Lsharp (0 : Fin 3) 0 := by
  rw [sum_erase_fin3_zero, Lsharp_01, Lsharp_02, Lsharp_00]
  norm_num

lemma Lsharp_row1_dom :
    ∑ j ∈ univ.erase (1 : Fin 3), |Lsharp (1 : Fin 3) j| ≤ Lsharp (1 : Fin 3) 1 := by
  rw [sum_erase_fin3_one, Lsharp_10, Lsharp_12, Lsharp_11]
  norm_num

lemma Lsharp_row2_dom :
    ∑ j ∈ univ.erase (2 : Fin 3), |Lsharp (2 : Fin 3) j| ≤ Lsharp (2 : Fin 3) 2 := by
  rw [sum_erase_fin3_two, Lsharp_20, Lsharp_21, Lsharp_22]
  norm_num

theorem Lsharp_isDiagDominant : IsDiagDominant Lsharp := by
  intro i
  fin_cases i
  · exact Lsharp_row0_dom
  · exact Lsharp_row1_dom
  · exact Lsharp_row2_dom

theorem Lsharp_isSDD : IsSDD Lsharp :=
  ⟨Lsharp_isSymm, Lsharp_isDiagDominant⟩

lemma Lsharp_row0_strict :
    ∑ j ∈ univ.erase (0 : Fin 3), |Lsharp (0 : Fin 3) j| < Lsharp (0 : Fin 3) 0 := by
  rw [sum_erase_fin3_zero, Lsharp_01, Lsharp_02, Lsharp_00]
  norm_num

lemma Lsharp_row1_strict :
    ∑ j ∈ univ.erase (1 : Fin 3), |Lsharp (1 : Fin 3) j| < Lsharp (1 : Fin 3) 1 := by
  rw [sum_erase_fin3_one, Lsharp_10, Lsharp_12, Lsharp_11]
  norm_num

lemma Lsharp_row2_strict :
    ∑ j ∈ univ.erase (2 : Fin 3), |Lsharp (2 : Fin 3) j| < Lsharp (2 : Fin 3) 2 := by
  rw [sum_erase_fin3_two, Lsharp_20, Lsharp_21, Lsharp_22]
  norm_num

theorem Lsharp_isStrictDiagDominant : IsStrictDiagDominant Lsharp := by
  intro i
  fin_cases i
  · exact Lsharp_row0_strict
  · exact Lsharp_row1_strict
  · exact Lsharp_row2_strict

theorem Lsharp_isStrictSDD : IsStrictSDD Lsharp :=
  ⟨Lsharp_isSymm, Lsharp_isStrictDiagDominant⟩

theorem L0_toReal_isSDD : IsSDD (toReal L0) :=
  toReal_isSDD L0_isSDD

theorem Lsharp_toReal_isSDD : IsSDD (toReal Lsharp) :=
  toReal_isSDD Lsharp_isSDD

theorem Lsharp_toReal_isStrictSDD : IsStrictSDD (toReal Lsharp) :=
  toReal_isStrictSDD Lsharp_isStrictSDD

theorem Lsharp_eq_L0_add_one : Lsharp = L0 + 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [L0, Lsharp] <;> norm_num

theorem Msharp_toReal_eq : toReal Msharp = toReal Lsharp + 1 := by
  rw [Lsharp_eq_Msharp_sub_one, toReal_add, toReal_one]

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

theorem Lsharp_eq_M0 : Lsharp = M0 := by
  rw [Lsharp_eq_L0_add_one, L0_eq_M0_sub_one]

theorem Lsharp_posDef : (toReal Lsharp).PosDef := by
  rw [Lsharp_eq_M0]
  exact M0_posDef

/-- Certified Colbrook values of the Nyström error of `M0`, by explicit
3×3 / 2×2 / 1×1 Cramer traces (kernel `norm_num`, not `native_decide`). -/

lemma M0_det : M0.det = 51 := by
  rw [det_fin_three]
  simp [M0]
  norm_num

lemma M0_adjugate_trace : M0.adjugate.trace = 47 := by
  rw [adjugate_fin_three, trace_fin_three]
  simp [M0]
  norm_num

lemma M0_cramerInv_trace : (cramerInv M0).trace = 47 / 51 := by
  rw [cramerInv, trace_smul, M0_adjugate_trace, M0_det]
  norm_num

theorem M0_cramer_empty : cramerNystromError M0 (∅ : Finset (Fin 3)) = 47 / 51 := by
  have h : compl (∅ : Finset (Fin 3)) = univ := by simp [compl]
  rw [cramerNystromError, h, cramerTraceInv_univ, M0_cramerInv_trace]

def fin2Equiv_one_two : Fin 2 ≃ PrincipalIndex ({1, 2} : Finset (Fin 3)) where
  toFun k := if k = 0 then ⟨1, by decide⟩ else ⟨2, by decide⟩
  invFun x := if x.1 = 1 then 0 else 1
  left_inv := by intro k; fin_cases k <;> simp
  right_inv := by
    intro x
    apply Subtype.ext
    have hx : x.1 = 1 ∨ x.1 = 2 :=
      (Finset.mem_insert.mp x.2).elim Or.inl fun h => Or.inr (Finset.mem_singleton.mp h)
    rcases hx with h | h
    · simp [h]
    · have : ¬ x.1 = 1 := by rw [h]; decide
      simp [h]

def fin2Equiv_zero_two : Fin 2 ≃ PrincipalIndex ({0, 2} : Finset (Fin 3)) where
  toFun k := if k = 0 then ⟨0, by decide⟩ else ⟨2, by decide⟩
  invFun x := if x.1 = 0 then 0 else 1
  left_inv := by intro k; fin_cases k <;> simp
  right_inv := by
    intro x
    apply Subtype.ext
    have hx : x.1 = 0 ∨ x.1 = 2 :=
      (Finset.mem_insert.mp x.2).elim Or.inl fun h => Or.inr (Finset.mem_singleton.mp h)
    rcases hx with h | h
    · simp [h]
    · have : ¬ x.1 = 0 := by rw [h]; decide
      simp [h]

def fin2Equiv_zero_one : Fin 2 ≃ PrincipalIndex ({0, 1} : Finset (Fin 3)) where
  toFun k := if k = 0 then ⟨0, by decide⟩ else ⟨1, by decide⟩
  invFun x := if x.1 = 0 then 0 else 1
  left_inv := by intro k; fin_cases k <;> simp
  right_inv := by
    intro x
    apply Subtype.ext
    have hx : x.1 = 0 ∨ x.1 = 1 :=
      (Finset.mem_insert.mp x.2).elim Or.inl fun h => Or.inr (Finset.mem_singleton.mp h)
    rcases hx with h | h
    · simp [h]
    · have : ¬ x.1 = 0 := by rw [h]; decide
      simp [h]

lemma M0_block_one_two :
    (principalSubmatrix M0 {1, 2}).submatrix fin2Equiv_one_two fin2Equiv_one_two =
      !![4, -2; -2, 5] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [principalSubmatrix, M0, fin2Equiv_one_two]

lemma M0_block_zero_two :
    (principalSubmatrix M0 {0, 2}).submatrix fin2Equiv_zero_two fin2Equiv_zero_two =
      !![4, -2; -2, 5] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [principalSubmatrix, M0, fin2Equiv_zero_two]

lemma cramerInv_block45_trace :
    (cramerInv (!![4, -2; -2, 5] : Matrix (Fin 2) (Fin 2) ℚ)).trace = 9 / 16 := by
  rw [cramerInv, det_fin_two, adjugate_fin_two, trace_smul, trace_fin_two]
  simp
  norm_num

theorem M0_cramer_zero : cramerNystromError M0 ({0} : Finset (Fin 3)) = 9 / 16 := by
  have hc : compl ({0} : Finset (Fin 3)) = {1, 2} := by decide
  rw [cramerNystromError, hc,
    cramerTraceInv_submatrix_equiv M0 {1, 2} fin2Equiv_one_two, M0_block_one_two,
    cramerInv_block45_trace]

theorem M0_cramer_one : cramerNystromError M0 ({1} : Finset (Fin 3)) = 9 / 16 := by
  have hc : compl ({1} : Finset (Fin 3)) = {0, 2} := by decide
  rw [cramerNystromError, hc,
    cramerTraceInv_submatrix_equiv M0 {0, 2} fin2Equiv_zero_two, M0_block_zero_two,
    cramerInv_block45_trace]

theorem M0_cramer_zero_one :
    cramerNystromError M0 ({0, 1} : Finset (Fin 3)) = 1 / 5 := by
  have hc : compl ({0, 1} : Finset (Fin 3)) = {2} := by decide
  rw [cramerNystromError, hc, cramerTraceInv_singleton]
  simp [M0]

/-- The four-point defect at \(A=\emptyset\), \(i=0\), \(j=1\). -/
theorem M0_delta :
    cramerNystromSupermodularDiff M0 ({0} : Finset (Fin 3)) {1} = -7 / 2040 := by
  unfold cramerNystromSupermodularDiff
  have hU : ({0} : Finset (Fin 3)) ∪ {1} = {0, 1} := by simp
  have hI : ({0} : Finset (Fin 3)) ∩ {1} = ∅ := by simp
  rw [hU, hI, M0_cramer_zero_one, M0_cramer_empty, M0_cramer_zero, M0_cramer_one]
  norm_num

theorem M0_delta_neg :
    cramerNystromError M0 (∅ : Finset (Fin 3)) +
        cramerNystromError M0 ({0, 1} : Finset (Fin 3)) <
      cramerNystromError M0 ({0} : Finset (Fin 3)) +
        cramerNystromError M0 ({1} : Finset (Fin 3)) := by
  rw [M0_cramer_empty, M0_cramer_zero_one, M0_cramer_zero, M0_cramer_one]
  norm_num

lemma Msharp_det : Msharp.det = 112 := by
  rw [det_fin_three]
  simp [Msharp]
  norm_num

lemma Msharp_adjugate_trace : Msharp.adjugate.trace = 76 := by
  rw [adjugate_fin_three, trace_fin_three]
  simp [Msharp]
  norm_num

lemma Msharp_cramerInv_trace : (cramerInv Msharp).trace = 19 / 28 := by
  rw [cramerInv, trace_smul, Msharp_adjugate_trace, Msharp_det]
  norm_num

theorem Msharp_cramer_empty : cramerNystromError Msharp (∅ : Finset (Fin 3)) = 19 / 28 := by
  have h : compl (∅ : Finset (Fin 3)) = univ := by simp [compl]
  rw [cramerNystromError, h, cramerTraceInv_univ, Msharp_cramerInv_trace]

lemma Msharp_block_one_two :
    (principalSubmatrix Msharp {1, 2}).submatrix fin2Equiv_one_two fin2Equiv_one_two =
      !![5, -2; -2, 6] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [principalSubmatrix, Msharp, fin2Equiv_one_two]

lemma Msharp_block_zero_two :
    (principalSubmatrix Msharp {0, 2}).submatrix fin2Equiv_zero_two fin2Equiv_zero_two =
      !![5, -2; -2, 6] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [principalSubmatrix, Msharp, fin2Equiv_zero_two]

lemma cramerInv_block56_trace :
    (cramerInv (!![5, -2; -2, 6] : Matrix (Fin 2) (Fin 2) ℚ)).trace = 11 / 26 := by
  rw [cramerInv, det_fin_two, adjugate_fin_two, trace_smul, trace_fin_two]
  simp
  norm_num

theorem Msharp_cramer_zero : cramerNystromError Msharp ({0} : Finset (Fin 3)) = 11 / 26 := by
  have hc : compl ({0} : Finset (Fin 3)) = {1, 2} := by decide
  rw [cramerNystromError, hc,
    cramerTraceInv_submatrix_equiv Msharp {1, 2} fin2Equiv_one_two, Msharp_block_one_two,
    cramerInv_block56_trace]

theorem Msharp_cramer_one : cramerNystromError Msharp ({1} : Finset (Fin 3)) = 11 / 26 := by
  have hc : compl ({1} : Finset (Fin 3)) = {0, 2} := by decide
  rw [cramerNystromError, hc,
    cramerTraceInv_submatrix_equiv Msharp {0, 2} fin2Equiv_zero_two, Msharp_block_zero_two,
    cramerInv_block56_trace]

theorem Msharp_cramer_zero_one :
    cramerNystromError Msharp ({0, 1} : Finset (Fin 3)) = 1 / 6 := by
  have hc : compl ({0, 1} : Finset (Fin 3)) = {2} := by decide
  rw [cramerNystromError, hc, cramerTraceInv_singleton]
  simp [Msharp]

theorem Msharp_delta :
    cramerNystromSupermodularDiff Msharp ({0} : Finset (Fin 3)) {1} = -1 / 1092 := by
  unfold cramerNystromSupermodularDiff
  have hU : ({0} : Finset (Fin 3)) ∪ {1} = {0, 1} := by simp
  have hI : ({0} : Finset (Fin 3)) ∩ {1} = ∅ := by simp
  rw [hU, hI, Msharp_cramer_zero_one, Msharp_cramer_empty, Msharp_cramer_zero, Msharp_cramer_one]
  norm_num

theorem Msharp_delta_neg :
    cramerNystromError Msharp (∅ : Finset (Fin 3)) +
        cramerNystromError Msharp ({0, 1} : Finset (Fin 3)) <
      cramerNystromError Msharp ({0} : Finset (Fin 3)) +
        cramerNystromError Msharp ({1} : Finset (Fin 3)) := by
  rw [Msharp_cramer_empty, Msharp_cramer_zero_one, Msharp_cramer_zero, Msharp_cramer_one]
  norm_num

theorem not_supermodular_nystromError_Msharp :
    ¬ Supermodular (nystromError (toReal Msharp)) := by
  intro hf
  have h := hf ({0} : Finset (Fin 3)) ({1} : Finset (Fin 3))
  have hunion : ({0} : Finset (Fin 3)) ∪ {1} = {0, 1} := by simp
  have hinter : ({0} : Finset (Fin 3)) ∩ {1} = ∅ := by simp
  rw [hunion, hinter] at h
  have h0 : nystromError (toReal Msharp) ({0} : Finset (Fin 3)) = ((11 / 26 : ℚ) : ℝ) := by
    rw [← toReal_nystromError, Msharp_cramer_zero]
  have h1 : nystromError (toReal Msharp) ({1} : Finset (Fin 3)) = ((11 / 26 : ℚ) : ℝ) := by
    rw [← toReal_nystromError, Msharp_cramer_one]
  have h01 : nystromError (toReal Msharp) ({0, 1} : Finset (Fin 3)) = ((1 / 6 : ℚ) : ℝ) := by
    rw [← toReal_nystromError, Msharp_cramer_zero_one]
  have hemp : nystromError (toReal Msharp) (∅ : Finset (Fin 3)) = ((19 / 28 : ℚ) : ℝ) := by
    rw [← toReal_nystromError, Msharp_cramer_empty]
  rw [h0, h1, h01, hemp] at h
  norm_num at h

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
