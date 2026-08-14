import NystromSubmodularity.Counterexamples.SDDDim3
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.Data.Real.Star
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.BigOperators.Fin

/-!
# A minimal 4×4 nonempty-base SDD obstruction

Colbrook (arXiv:2607.19282), equations (28)–(29). After selecting the last
index, the residual is a scaled copy of the three-dimensional signed
triangle: the leading \(3\times 3\) of \(M_4=L_4+I\) is \(10M_0\).

Living numbers (\(\gamma=1\), \(A=\{3\}\)):
* \(\mathcal{E}(A)=47/510\), \(\mathcal{E}(A\cup\{0\})=\mathcal{E}(A\cup\{1\})=9/160\),
  \(\mathcal{E}(A\cup\{0,1\})=1/50\), hence \(\Delta=-7/20400<0\).
-/

namespace NystromSubmodularity
namespace Counterexamples

open Matrix Finset

/-- Colbrook's strictly SDD \(4\times 4\) matrix \(L_4\). -/
def L4 : Matrix (Fin 4) (Fin 4) ℚ :=
  !![39, 10, -20, -1;
     10, 39, -20, -1;
     -20, -20, 49, -1;
     -1, -1, -1, 4]

/-- Precision matrix \(M_4=L_4+I\). -/
def M4 : Matrix (Fin 4) (Fin 4) ℚ :=
  !![40, 10, -20, -1;
     10, 40, -20, -1;
     -20, -20, 50, -1;
     -1, -1, -1, 5]

theorem L4_eq_M4_sub_one : M4 = L4 + 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [L4, M4] <;> norm_num

lemma L4_00 : L4 (0 : Fin 4) (0 : Fin 4) = 39 := rfl
lemma L4_01 : L4 (0 : Fin 4) (1 : Fin 4) = 10 := rfl
lemma L4_02 : L4 (0 : Fin 4) (2 : Fin 4) = -20 := rfl
lemma L4_03 : L4 (0 : Fin 4) (3 : Fin 4) = -1 := rfl
lemma L4_10 : L4 (1 : Fin 4) (0 : Fin 4) = 10 := rfl
lemma L4_11 : L4 (1 : Fin 4) (1 : Fin 4) = 39 := rfl
lemma L4_12 : L4 (1 : Fin 4) (2 : Fin 4) = -20 := rfl
lemma L4_13 : L4 (1 : Fin 4) (3 : Fin 4) = -1 := rfl
lemma L4_20 : L4 (2 : Fin 4) (0 : Fin 4) = -20 := rfl
lemma L4_21 : L4 (2 : Fin 4) (1 : Fin 4) = -20 := rfl
lemma L4_22 : L4 (2 : Fin 4) (2 : Fin 4) = 49 := rfl
lemma L4_23 : L4 (2 : Fin 4) (3 : Fin 4) = -1 := rfl
lemma L4_30 : L4 (3 : Fin 4) (0 : Fin 4) = -1 := rfl
lemma L4_31 : L4 (3 : Fin 4) (1 : Fin 4) = -1 := rfl
lemma L4_32 : L4 (3 : Fin 4) (2 : Fin 4) = -1 := rfl
lemma L4_33 : L4 (3 : Fin 4) (3 : Fin 4) = 4 := rfl

lemma sum_erase_fin4_zero (f : Fin 4 → ℚ) :
    ∑ j ∈ univ.erase (0 : Fin 4), f j = f 1 + f 2 + f 3 := by
  have h : univ.erase (0 : Fin 4) = ({1, 2, 3} : Finset (Fin 4)) := by decide
  have h1 : (1 : Fin 4) ∉ ({2, 3} : Finset (Fin 4)) := by decide
  have h2 : (2 : Fin 4) ∉ ({3} : Finset (Fin 4)) := by decide
  rw [h, Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton]
  abel

lemma sum_erase_fin4_one (f : Fin 4 → ℚ) :
    ∑ j ∈ univ.erase (1 : Fin 4), f j = f 0 + f 2 + f 3 := by
  have h : univ.erase (1 : Fin 4) = ({0, 2, 3} : Finset (Fin 4)) := by decide
  have h0 : (0 : Fin 4) ∉ ({2, 3} : Finset (Fin 4)) := by decide
  have h2 : (2 : Fin 4) ∉ ({3} : Finset (Fin 4)) := by decide
  rw [h, Finset.sum_insert h0, Finset.sum_insert h2, Finset.sum_singleton]
  abel

lemma sum_erase_fin4_two (f : Fin 4 → ℚ) :
    ∑ j ∈ univ.erase (2 : Fin 4), f j = f 0 + f 1 + f 3 := by
  have h : univ.erase (2 : Fin 4) = ({0, 1, 3} : Finset (Fin 4)) := by decide
  have h0 : (0 : Fin 4) ∉ ({1, 3} : Finset (Fin 4)) := by decide
  have h1 : (1 : Fin 4) ∉ ({3} : Finset (Fin 4)) := by decide
  rw [h, Finset.sum_insert h0, Finset.sum_insert h1, Finset.sum_singleton]
  abel

lemma sum_erase_fin4_three (f : Fin 4 → ℚ) :
    ∑ j ∈ univ.erase (3 : Fin 4), f j = f 0 + f 1 + f 2 := by
  have h : univ.erase (3 : Fin 4) = ({0, 1, 2} : Finset (Fin 4)) := by decide
  have h0 : (0 : Fin 4) ∉ ({1, 2} : Finset (Fin 4)) := by decide
  have h1 : (1 : Fin 4) ∉ ({2} : Finset (Fin 4)) := by decide
  rw [h, Finset.sum_insert h0, Finset.sum_insert h1, Finset.sum_singleton]
  abel

theorem L4_isSymm : L4.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [L4]

lemma L4_row0_strict :
    ∑ j ∈ univ.erase (0 : Fin 4), |L4 (0 : Fin 4) j| < L4 (0 : Fin 4) 0 := by
  rw [sum_erase_fin4_zero, L4_01, L4_02, L4_03, L4_00]
  norm_num

lemma L4_row1_strict :
    ∑ j ∈ univ.erase (1 : Fin 4), |L4 (1 : Fin 4) j| < L4 (1 : Fin 4) 1 := by
  rw [sum_erase_fin4_one, L4_10, L4_12, L4_13, L4_11]
  norm_num

lemma L4_row2_strict :
    ∑ j ∈ univ.erase (2 : Fin 4), |L4 (2 : Fin 4) j| < L4 (2 : Fin 4) 2 := by
  rw [sum_erase_fin4_two, L4_20, L4_21, L4_23, L4_22]
  norm_num

lemma L4_row3_strict :
    ∑ j ∈ univ.erase (3 : Fin 4), |L4 (3 : Fin 4) j| < L4 (3 : Fin 4) 3 := by
  rw [sum_erase_fin4_three, L4_30, L4_31, L4_32, L4_33]
  norm_num

theorem L4_isStrictDiagDominant : IsStrictDiagDominant L4 := by
  intro i
  fin_cases i
  · exact L4_row0_strict
  · exact L4_row1_strict
  · exact L4_row2_strict
  · exact L4_row3_strict

theorem L4_isStrictSDD : IsStrictSDD L4 :=
  ⟨L4_isSymm, L4_isStrictDiagDominant⟩

theorem L4_toReal_isStrictSDD : IsStrictSDD (toReal L4) :=
  toReal_isStrictSDD L4_isStrictSDD

theorem L4_complete_support {i j : Fin 4} (hij : i ≠ j) : L4 i j ≠ 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [L4]

theorem M4_toReal_eq : toReal M4 = toReal L4 + 1 := by
  rw [L4_eq_M4_sub_one, toReal_add, toReal_one]

/-- Explicit quadratic form of `toReal L4`: a sum of squares built from the
\(L_0\) form plus a strictly convex coupling to the fourth coordinate. -/
theorem L4_quadratic (x : Fin 4 → ℝ) :
    star x ⬝ᵥ (toReal L4 *ᵥ x) =
      10 * (2 * (x 0 - x 2) ^ 2 + 2 * (x 1 - x 2) ^ 2 + (x 0 + x 1) ^ 2) +
        8 * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) +
        (x 0 - x 3) ^ 2 + (x 1 - x 3) ^ 2 + (x 2 - x 3) ^ 2 + x 3 ^ 2 := by
  simp [dotProduct, mulVec, toReal, L4, Fin.sum_univ_four, Pi.star_apply]
  ring

theorem L4_posDef : (toReal L4).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · rw [isHermitian_iff_isSymm]
    exact toReal_isSymm L4_isSymm
  · intro x hx
    have hform := L4_quadratic x
    have hsq :
        0 ≤ 10 * (2 * (x 0 - x 2) ^ 2 + 2 * (x 1 - x 2) ^ 2 + (x 0 + x 1) ^ 2) +
          8 * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) +
          (x 0 - x 3) ^ 2 + (x 1 - x 3) ^ 2 + (x 2 - x 3) ^ 2 + x 3 ^ 2 := by
      nlinarith [sq_nonneg (x 0 - x 2), sq_nonneg (x 1 - x 2), sq_nonneg (x 0 + x 1),
        sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
        sq_nonneg (x 0 - x 3), sq_nonneg (x 1 - x 3), sq_nonneg (x 2 - x 3),
        sq_nonneg (x 3)]
    have hpos :
        0 < 10 * (2 * (x 0 - x 2) ^ 2 + 2 * (x 1 - x 2) ^ 2 + (x 0 + x 1) ^ 2) +
          8 * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) +
          (x 0 - x 3) ^ 2 + (x 1 - x 3) ^ 2 + (x 2 - x 3) ^ 2 + x 3 ^ 2 := by
      by_contra h
      have hz :
          10 * (2 * (x 0 - x 2) ^ 2 + 2 * (x 1 - x 2) ^ 2 + (x 0 + x 1) ^ 2) +
            8 * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) +
            (x 0 - x 3) ^ 2 + (x 1 - x 3) ^ 2 + (x 2 - x 3) ^ 2 + x 3 ^ 2 = 0 :=
        le_antisymm (le_of_not_gt h) hsq
      have h0 : x 0 - x 2 = 0 := by
        nlinarith [sq_nonneg (x 0 - x 2), sq_nonneg (x 1 - x 2), sq_nonneg (x 0 + x 1),
          sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
          sq_nonneg (x 0 - x 3), sq_nonneg (x 1 - x 3), sq_nonneg (x 2 - x 3),
          sq_nonneg (x 3)]
      have h1 : x 1 - x 2 = 0 := by
        nlinarith [sq_nonneg (x 0 - x 2), sq_nonneg (x 1 - x 2), sq_nonneg (x 0 + x 1),
          sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
          sq_nonneg (x 0 - x 3), sq_nonneg (x 1 - x 3), sq_nonneg (x 2 - x 3),
          sq_nonneg (x 3)]
      have h2 : x 0 + x 1 = 0 := by
        nlinarith [sq_nonneg (x 0 - x 2), sq_nonneg (x 1 - x 2), sq_nonneg (x 0 + x 1),
          sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
          sq_nonneg (x 0 - x 3), sq_nonneg (x 1 - x 3), sq_nonneg (x 2 - x 3),
          sq_nonneg (x 3)]
      have hx0 : x 0 = 0 := by linarith
      have hx1 : x 1 = 0 := by linarith
      have hx2 : x 2 = 0 := by linarith
      have hx3 : x 3 = 0 := by
        nlinarith [sq_nonneg (x 0 - x 3), sq_nonneg (x 1 - x 3), sq_nonneg (x 2 - x 3),
          sq_nonneg (x 3)]
      apply hx
      funext k
      fin_cases k <;> assumption
    rw [hform]
    exact hpos

/-- Identify the leading \(3\times 3\) of \(M_4\) with `Fin 3`. -/
def fin3Equiv_leading : Fin 3 ≃ PrincipalIndex ({0, 1, 2} : Finset (Fin 4)) where
  toFun k := if k = 0 then ⟨0, by decide⟩ else if k = 1 then ⟨1, by decide⟩ else ⟨2, by decide⟩
  invFun x := if x.1 = 0 then 0 else if x.1 = 1 then 1 else 2
  left_inv := by intro k; fin_cases k <;> simp
  right_inv := by
    intro x
    apply Subtype.ext
    have hx : x.1 = 0 ∨ x.1 = 1 ∨ x.1 = 2 := by
      have h := Finset.mem_insert.mp x.2
      rcases h with h | h
      · exact Or.inl h
      · have h' := Finset.mem_insert.mp h
        rcases h' with h' | h'
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr (Finset.mem_singleton.mp h'))
    rcases hx with h | h | h
    · simp [h]
    · have : ¬ x.1 = 0 := by rw [h]; decide
      simp [h]
    · have h0 : ¬ x.1 = 0 := by rw [h]; decide
      have h1 : ¬ x.1 = 1 := by rw [h]; decide
      simp [h]

/-- The residual after selecting index \(3\) is a scaled copy of \(M_0\). -/
lemma M4_leading_block :
    (principalSubmatrix M4 {0, 1, 2}).submatrix fin3Equiv_leading fin3Equiv_leading =
      (10 : ℚ) • M0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [principalSubmatrix, M4, fin3Equiv_leading, M0, Matrix.smul_apply] <;> norm_num

lemma ten_ne_zero : (10 : ℚ) ≠ 0 := by norm_num

theorem M4_cramer_three : cramerNystromError M4 ({3} : Finset (Fin 4)) = 47 / 510 := by
  have hc : compl ({3} : Finset (Fin 4)) = {0, 1, 2} := by decide
  rw [cramerNystromError, hc,
    cramerTraceInv_submatrix_equiv M4 {0, 1, 2} fin3Equiv_leading, M4_leading_block,
    cramerInv_smul (10 : ℚ) M0 ten_ne_zero, trace_smul, smul_eq_mul, M0_cramerInv_trace]
  norm_num

def fin2Equiv_one_two_fin4 : Fin 2 ≃ PrincipalIndex ({1, 2} : Finset (Fin 4)) where
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

def fin2Equiv_zero_two_fin4 : Fin 2 ≃ PrincipalIndex ({0, 2} : Finset (Fin 4)) where
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

lemma M4_block_one_two :
    (principalSubmatrix M4 {1, 2}).submatrix fin2Equiv_one_two_fin4 fin2Equiv_one_two_fin4 =
      (10 : ℚ) • (!![4, -2; -2, 5] : Matrix (Fin 2) (Fin 2) ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [principalSubmatrix, M4, fin2Equiv_one_two_fin4, Matrix.smul_apply] <;> norm_num

lemma M4_block_zero_two :
    (principalSubmatrix M4 {0, 2}).submatrix fin2Equiv_zero_two_fin4 fin2Equiv_zero_two_fin4 =
      (10 : ℚ) • (!![4, -2; -2, 5] : Matrix (Fin 2) (Fin 2) ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [principalSubmatrix, M4, fin2Equiv_zero_two_fin4, Matrix.smul_apply] <;> norm_num

theorem M4_cramer_zero_three :
    cramerNystromError M4 ({0, 3} : Finset (Fin 4)) = 9 / 160 := by
  have hc : compl ({0, 3} : Finset (Fin 4)) = {1, 2} := by decide
  rw [cramerNystromError, hc,
    cramerTraceInv_submatrix_equiv M4 {1, 2} fin2Equiv_one_two_fin4, M4_block_one_two,
    cramerInv_smul (10 : ℚ) _ ten_ne_zero, trace_smul, smul_eq_mul, cramerInv_block45_trace]
  norm_num

theorem M4_cramer_one_three :
    cramerNystromError M4 ({1, 3} : Finset (Fin 4)) = 9 / 160 := by
  have hc : compl ({1, 3} : Finset (Fin 4)) = {0, 2} := by decide
  rw [cramerNystromError, hc,
    cramerTraceInv_submatrix_equiv M4 {0, 2} fin2Equiv_zero_two_fin4, M4_block_zero_two,
    cramerInv_smul (10 : ℚ) _ ten_ne_zero, trace_smul, smul_eq_mul, cramerInv_block45_trace]
  norm_num

theorem M4_cramer_zero_one_three :
    cramerNystromError M4 ({0, 1, 3} : Finset (Fin 4)) = 1 / 50 := by
  have hc : compl ({0, 1, 3} : Finset (Fin 4)) = {2} := by decide
  rw [cramerNystromError, hc, cramerTraceInv_singleton]
  simp [M4]

/-- The four-point defect at \(A=\{3\}\), \(i=0\), \(j=1\). -/
theorem M4_delta :
    cramerNystromSupermodularDiff M4 ({0, 3} : Finset (Fin 4)) {1, 3} =
      -7 / 20400 := by
  unfold cramerNystromSupermodularDiff
  have hU : ({0, 3} : Finset (Fin 4)) ∪ ({1, 3} : Finset (Fin 4)) =
      ({0, 1, 3} : Finset (Fin 4)) := by decide
  have hI : ({0, 3} : Finset (Fin 4)) ∩ ({1, 3} : Finset (Fin 4)) =
      ({3} : Finset (Fin 4)) := by decide
  rw [hU, hI, M4_cramer_zero_one_three, M4_cramer_three, M4_cramer_zero_three,
    M4_cramer_one_three]
  norm_num

theorem M4_delta_neg :
    cramerNystromError M4 ({3} : Finset (Fin 4)) +
        cramerNystromError M4 ({0, 1, 3} : Finset (Fin 4)) <
      cramerNystromError M4 ({0, 3} : Finset (Fin 4)) +
        cramerNystromError M4 ({1, 3} : Finset (Fin 4)) := by
  rw [M4_cramer_three, M4_cramer_zero_one_three, M4_cramer_zero_three, M4_cramer_one_three]
  norm_num

theorem M4_delta_neg_real :
    nystromError (toReal M4) ({3} : Finset (Fin 4)) +
        nystromError (toReal M4) ({0, 1, 3} : Finset (Fin 4)) <
      nystromError (toReal M4) ({0, 3} : Finset (Fin 4)) +
        nystromError (toReal M4) ({1, 3} : Finset (Fin 4)) := by
  have h3 : nystromError (toReal M4) ({3} : Finset (Fin 4)) = ((47 / 510 : ℚ) : ℝ) := by
    rw [← toReal_nystromError, M4_cramer_three]
  have h03 : nystromError (toReal M4) ({0, 3} : Finset (Fin 4)) = ((9 / 160 : ℚ) : ℝ) := by
    rw [← toReal_nystromError, M4_cramer_zero_three]
  have h13 : nystromError (toReal M4) ({1, 3} : Finset (Fin 4)) = ((9 / 160 : ℚ) : ℝ) := by
    rw [← toReal_nystromError, M4_cramer_one_three]
  have h013 : nystromError (toReal M4) ({0, 1, 3} : Finset (Fin 4)) = ((1 / 50 : ℚ) : ℝ) := by
    rw [← toReal_nystromError, M4_cramer_zero_one_three]
  rw [h3, h03, h13, h013]
  norm_num

/-- The Nyström error of `toReal M4` fails supermodularity at a nonempty base. -/
theorem not_supermodular_nystromError_M4 :
    ¬ Supermodular (nystromError (toReal M4)) := by
  intro hf
  have h := hf ({0, 3} : Finset (Fin 4)) ({1, 3} : Finset (Fin 4))
  have hunion : ({0, 3} : Finset (Fin 4)) ∪ ({1, 3} : Finset (Fin 4)) =
      ({0, 1, 3} : Finset (Fin 4)) := by decide
  have hinter : ({0, 3} : Finset (Fin 4)) ∩ ({1, 3} : Finset (Fin 4)) =
      ({3} : Finset (Fin 4)) := by decide
  rw [hunion, hinter] at h
  linarith [h, M4_delta_neg_real]

end Counterexamples
end NystromSubmodularity
