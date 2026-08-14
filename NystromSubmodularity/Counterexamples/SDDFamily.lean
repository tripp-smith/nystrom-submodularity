import NystromSubmodularity.Counterexamples.SDDDim3
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Real.Star
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Fin

/-!
# The one-parameter SDD family \(L(t)\)

Colbrook (arXiv:2607.19282), equations (14)–(19) / Theorem 10. For \(t>0\),

\[
L(t)=\begin{pmatrix}t+1&1&-t\\1&t+1&-t\\-t&-t&2t\end{pmatrix}
\]

is positive definite and SDD, and at \(\gamma=1\) the empty-base four-point
defect on \(\{0,1\}\) is negative if and only if
\(\varphi<t<1+\sqrt{2}\).
-/

namespace NystromSubmodularity
namespace Counterexamples

open Matrix Finset

/-- Colbrook's signed-triangle family. -/
def Lfam (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![t + 1, 1, -t; 1, t + 1, -t; -t, -t, 2 * t]

/-- Precision matrix \(M(t)=L(t)+I\). -/
def Mfam (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![t + 2, 1, -t; 1, t + 2, -t; -t, -t, 2 * t + 1]

theorem Lfam_eq_Mfam_sub_one (t : ℝ) : Mfam t = Lfam t + 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lfam, Mfam] <;> ring

lemma Lfam_00 (t : ℝ) : Lfam t (0 : Fin 3) 0 = t + 1 := by simp [Lfam]
lemma Lfam_01 (t : ℝ) : Lfam t (0 : Fin 3) 1 = 1 := by simp [Lfam]
lemma Lfam_02 (t : ℝ) : Lfam t (0 : Fin 3) 2 = -t := by simp [Lfam]
lemma Lfam_10 (t : ℝ) : Lfam t (1 : Fin 3) 0 = 1 := by simp [Lfam]
lemma Lfam_11 (t : ℝ) : Lfam t (1 : Fin 3) 1 = t + 1 := by simp [Lfam]
lemma Lfam_12 (t : ℝ) : Lfam t (1 : Fin 3) 2 = -t := by simp [Lfam]
lemma Lfam_20 (t : ℝ) : Lfam t (2 : Fin 3) 0 = -t := by simp [Lfam]
lemma Lfam_21 (t : ℝ) : Lfam t (2 : Fin 3) 1 = -t := by simp [Lfam]
lemma Lfam_22 (t : ℝ) : Lfam t (2 : Fin 3) 2 = 2 * t := by simp [Lfam]

theorem Lfam_isSymm (t : ℝ) : (Lfam t).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lfam]

lemma sum_erase_fin3R_zero (f : Fin 3 → ℝ) :
    ∑ j ∈ univ.erase (0 : Fin 3), f j = f 1 + f 2 := by
  have h : univ.erase (0 : Fin 3) = ({1, 2} : Finset (Fin 3)) := by decide
  rw [h, Finset.sum_pair (by decide : (1 : Fin 3) ≠ 2)]

lemma sum_erase_fin3R_one (f : Fin 3 → ℝ) :
    ∑ j ∈ univ.erase (1 : Fin 3), f j = f 0 + f 2 := by
  have h : univ.erase (1 : Fin 3) = ({0, 2} : Finset (Fin 3)) := by decide
  rw [h, Finset.sum_pair (by decide : (0 : Fin 3) ≠ 2)]

lemma sum_erase_fin3R_two (f : Fin 3 → ℝ) :
    ∑ j ∈ univ.erase (2 : Fin 3), f j = f 0 + f 1 := by
  have h : univ.erase (2 : Fin 3) = ({0, 1} : Finset (Fin 3)) := by decide
  rw [h, Finset.sum_pair (by decide : (0 : Fin 3) ≠ 1)]

lemma Lfam_row0_dom {t : ℝ} (ht : 0 ≤ t) :
    ∑ j ∈ univ.erase (0 : Fin 3), |Lfam t (0 : Fin 3) j| ≤ Lfam t (0 : Fin 3) 0 := by
  have hsum := sum_erase_fin3R_zero fun j => |Lfam t (0 : Fin 3) j|
  rw [hsum, Lfam_01, Lfam_02, Lfam_00, abs_one, abs_neg, abs_of_nonneg ht]
  linarith

lemma Lfam_row1_dom {t : ℝ} (ht : 0 ≤ t) :
    ∑ j ∈ univ.erase (1 : Fin 3), |Lfam t (1 : Fin 3) j| ≤ Lfam t (1 : Fin 3) 1 := by
  have hsum := sum_erase_fin3R_one fun j => |Lfam t (1 : Fin 3) j|
  rw [hsum, Lfam_10, Lfam_12, Lfam_11, abs_one, abs_neg, abs_of_nonneg ht]
  linarith

lemma Lfam_row2_dom {t : ℝ} (ht : 0 ≤ t) :
    ∑ j ∈ univ.erase (2 : Fin 3), |Lfam t (2 : Fin 3) j| ≤ Lfam t (2 : Fin 3) 2 := by
  have hsum := sum_erase_fin3R_two fun j => |Lfam t (2 : Fin 3) j|
  rw [hsum, Lfam_20, Lfam_21, Lfam_22, abs_neg, abs_of_nonneg ht]
  linarith

theorem Lfam_isDiagDominant {t : ℝ} (ht : 0 ≤ t) : IsDiagDominant (Lfam t) := by
  intro i
  fin_cases i
  · exact Lfam_row0_dom ht
  · exact Lfam_row1_dom ht
  · exact Lfam_row2_dom ht

theorem Lfam_isSDD {t : ℝ} (ht : 0 ≤ t) : IsSDD (Lfam t) :=
  ⟨Lfam_isSymm t, Lfam_isDiagDominant ht⟩

theorem Lfam_quadratic (t : ℝ) (x : Fin 3 → ℝ) :
    star x ⬝ᵥ (Lfam t *ᵥ x) =
      t * (x 0 - x 2) ^ 2 + t * (x 1 - x 2) ^ 2 + (x 0 + x 1) ^ 2 := by
  simp [dotProduct, mulVec, Lfam, Fin.sum_univ_three, Pi.star_apply]
  ring

theorem Lfam_posDef {t : ℝ} (ht : 0 < t) : (Lfam t).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · rw [isHermitian_iff_isSymm]
    exact Lfam_isSymm t
  · intro x hx
    have hform := Lfam_quadratic t x
    have hsq :
        0 ≤ t * (x 0 - x 2) ^ 2 + t * (x 1 - x 2) ^ 2 + (x 0 + x 1) ^ 2 := by
      nlinarith [ht, sq_nonneg (x 0 - x 2), sq_nonneg (x 1 - x 2), sq_nonneg (x 0 + x 1)]
    have hpos :
        0 < t * (x 0 - x 2) ^ 2 + t * (x 1 - x 2) ^ 2 + (x 0 + x 1) ^ 2 := by
      by_contra h
      have hz :
          t * (x 0 - x 2) ^ 2 + t * (x 1 - x 2) ^ 2 + (x 0 + x 1) ^ 2 = 0 :=
        le_antisymm (le_of_not_gt h) hsq
      have n0 : 0 ≤ t * (x 0 - x 2) ^ 2 := mul_nonneg ht.le (sq_nonneg _)
      have n1 : 0 ≤ t * (x 1 - x 2) ^ 2 := mul_nonneg ht.le (sq_nonneg _)
      have n2 : 0 ≤ (x 0 + x 1) ^ 2 := sq_nonneg _
      have z0 : t * (x 0 - x 2) ^ 2 = 0 := le_antisymm (by linarith [hz, n1, n2]) n0
      have z1 : t * (x 1 - x 2) ^ 2 = 0 := le_antisymm (by linarith [hz, n0, n2]) n1
      have z2 : (x 0 + x 1) ^ 2 = 0 := le_antisymm (by linarith [hz, n0, n1]) n2
      have h0 : x 0 - x 2 = 0 :=
        sq_eq_zero_iff.mp ((mul_eq_zero.mp z0).resolve_left ht.ne')
      have h1 : x 1 - x 2 = 0 :=
        sq_eq_zero_iff.mp ((mul_eq_zero.mp z1).resolve_left ht.ne')
      have h2 : x 0 + x 1 = 0 := sq_eq_zero_iff.mp z2
      have hx0 : x 0 = 0 := by linarith
      have hx1 : x 1 = 0 := by linarith
      have hx2 : x 2 = 0 := by linarith
      apply hx
      funext k
      fin_cases k <;> assumption
    rw [hform]
    exact hpos

theorem Mfam_isSymm (t : ℝ) : (Mfam t).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Mfam]

theorem Mfam_posDef {t : ℝ} (ht : 0 < t) : (Mfam t).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · rw [isHermitian_iff_isSymm]
    exact Mfam_isSymm t
  · intro x hx
    have hM : star x ⬝ᵥ (Mfam t *ᵥ x) =
        star x ⬝ᵥ (Lfam t *ᵥ x) + star x ⬝ᵥ x := by
      rw [Lfam_eq_Mfam_sub_one, add_mulVec, dotProduct_add, one_mulVec]
    have hL : 0 ≤ star x ⬝ᵥ (Lfam t *ᵥ x) := by
      rw [Lfam_quadratic]
      nlinarith [ht, sq_nonneg (x 0 - x 2), sq_nonneg (x 1 - x 2), sq_nonneg (x 0 + x 1)]
    have hnorm : 0 < star x ⬝ᵥ x := by
      have hstar : star x = x := funext fun i => star_trivial (x i)
      rw [hstar]
      have : x ⬝ᵥ x = 0 ↔ x = 0 := dotProduct_self_eq_zero
      have hne : x ⬝ᵥ x ≠ 0 := this.not.mpr hx
      have hnn : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
      exact lt_of_le_of_ne hnn hne.symm
    rw [hM]
    linarith

lemma Mfam_det (t : ℝ) : (Mfam t).det = (t + 1) * (7 * t + 3) := by
  rw [det_fin_three]
  simp [Mfam]
  ring

lemma Mfam_adjugate_trace (t : ℝ) :
    (Mfam t).adjugate.trace = 3 * t ^ 2 + 14 * t + 7 := by
  rw [adjugate_fin_three, trace_fin_three]
  simp [Mfam]
  ring

lemma Mfam_cramerInv_trace (t : ℝ) :
    (cramerInv (Mfam t)).trace =
      (3 * t ^ 2 + 14 * t + 7) / ((t + 1) * (7 * t + 3)) := by
  rw [cramerInv, trace_smul, Mfam_adjugate_trace, Mfam_det, smul_eq_mul]
  field_simp

theorem Mfam_cramer_empty (t : ℝ) :
    cramerNystromError (Mfam t) (∅ : Finset (Fin 3)) =
      (3 * t ^ 2 + 14 * t + 7) / ((t + 1) * (7 * t + 3)) := by
  have h : compl (∅ : Finset (Fin 3)) = univ := by simp [compl]
  rw [cramerNystromError, h, cramerTraceInv_univ, Mfam_cramerInv_trace]

lemma Mfam_block_one_two (t : ℝ) :
    (principalSubmatrix (Mfam t) {1, 2}).submatrix fin2Equiv_one_two fin2Equiv_one_two =
      !![t + 2, -t; -t, 2 * t + 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [principalSubmatrix, Mfam, fin2Equiv_one_two]

lemma Mfam_block_zero_two (t : ℝ) :
    (principalSubmatrix (Mfam t) {0, 2}).submatrix fin2Equiv_zero_two fin2Equiv_zero_two =
      !![t + 2, -t; -t, 2 * t + 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [principalSubmatrix, Mfam, fin2Equiv_zero_two]

lemma cramerInv_block_Mfam_trace (t : ℝ) :
    (cramerInv (!![t + 2, -t; -t, 2 * t + 1] : Matrix (Fin 2) (Fin 2) ℝ)).trace =
      3 * (t + 1) / (t ^ 2 + 5 * t + 2) := by
  rw [cramerInv, det_fin_two, adjugate_fin_two, trace_smul, trace_fin_two]
  simp
  field_simp
  ring

theorem Mfam_cramer_zero (t : ℝ) :
    cramerNystromError (Mfam t) ({0} : Finset (Fin 3)) =
      3 * (t + 1) / (t ^ 2 + 5 * t + 2) := by
  have hc : compl ({0} : Finset (Fin 3)) = {1, 2} := by decide
  rw [cramerNystromError, hc,
    cramerTraceInv_submatrix_equiv (Mfam t) {1, 2} fin2Equiv_one_two, Mfam_block_one_two,
    cramerInv_block_Mfam_trace]

theorem Mfam_cramer_one (t : ℝ) :
    cramerNystromError (Mfam t) ({1} : Finset (Fin 3)) =
      3 * (t + 1) / (t ^ 2 + 5 * t + 2) := by
  have hc : compl ({1} : Finset (Fin 3)) = {0, 2} := by decide
  rw [cramerNystromError, hc,
    cramerTraceInv_submatrix_equiv (Mfam t) {0, 2} fin2Equiv_zero_two, Mfam_block_zero_two,
    cramerInv_block_Mfam_trace]

theorem Mfam_cramer_zero_one (t : ℝ) :
    cramerNystromError (Mfam t) ({0, 1} : Finset (Fin 3)) = (2 * t + 1)⁻¹ := by
  have hc : compl ({0, 1} : Finset (Fin 3)) = {2} := by decide
  rw [cramerNystromError, hc, cramerTraceInv_singleton]
  simp [Mfam]

lemma Mfam_quad_denom_pos {t : ℝ} (ht : 0 < t) : 0 < t ^ 2 + 5 * t + 2 := by
  nlinarith [sq_nonneg t]

lemma Mfam_denoms_ne_zero {t : ℝ} (ht : 0 < t) :
    t + 1 ≠ 0 ∧ 2 * t + 1 ≠ 0 ∧ 7 * t + 3 ≠ 0 ∧ t ^ 2 + 5 * t + 2 ≠ 0 := by
  refine ⟨by linarith, by linarith, by linarith, ?_⟩
  exact (Mfam_quad_denom_pos ht).ne'

/-- Colbrook (18): the empty-base \((0,1)\) four-point defect. -/
theorem Mfam_delta (t : ℝ) (ht : 0 < t) :
    cramerNystromError (Mfam t) (∅ : Finset (Fin 3)) +
        cramerNystromError (Mfam t) ({0, 1} : Finset (Fin 3)) -
      cramerNystromError (Mfam t) ({0} : Finset (Fin 3)) -
        cramerNystromError (Mfam t) ({1} : Finset (Fin 3)) =
      2 * (3 * t + 1) * (t ^ 2 - 2 * t - 1) * (t ^ 2 - t - 1) /
        ((t + 1) * (2 * t + 1) * (7 * t + 3) * (t ^ 2 + 5 * t + 2)) := by
  have ⟨h1, h2, h7, hq⟩ := Mfam_denoms_ne_zero ht
  rw [Mfam_cramer_empty, Mfam_cramer_zero_one, Mfam_cramer_zero, Mfam_cramer_one]
  field_simp [h1, h2, h7, hq]
  ring

lemma quad_golden (t : ℝ) :
    t ^ 2 - t - 1 = (t - Real.goldenRatio) * (t - Real.goldenConj) := by
  have hsum := Real.goldenRatio_add_goldenConj
  have hprod := Real.goldenRatio_mul_goldenConj
  calc
    t ^ 2 - t - 1 = t ^ 2 - (Real.goldenRatio + Real.goldenConj) * t +
        Real.goldenRatio * Real.goldenConj := by
      rw [hsum, hprod]; ring
    _ = (t - Real.goldenRatio) * (t - Real.goldenConj) := by ring

lemma quad_silver (t : ℝ) :
    t ^ 2 - 2 * t - 1 = (t - (1 + √2)) * (t - (1 - √2)) := by
  have hs : (√2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  calc
    t ^ 2 - 2 * t - 1 = (t - 1) ^ 2 - 2 := by ring
    _ = (t - 1) ^ 2 - (√2) ^ 2 := by rw [hs]
    _ = ((t - 1) - √2) * ((t - 1) + √2) := by ring
    _ = (t - (1 + √2)) * (t - (1 - √2)) := by ring

lemma one_lt_sqrt_two : (1 : ℝ) < √2 := by
  rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
  norm_num

lemma one_sub_sqrt_two_neg : 1 - √2 < 0 := by
  linarith [one_lt_sqrt_two]

lemma quad_golden_pos_iff {t : ℝ} (ht : 0 < t) :
    0 < t ^ 2 - t - 1 ↔ Real.goldenRatio < t := by
  rw [quad_golden, mul_pos_iff_of_pos_right]
  · simp [sub_pos]
  · linarith [ht, Real.goldenConj_neg]

lemma quad_silver_neg_iff {t : ℝ} (ht : 0 < t) :
    t ^ 2 - 2 * t - 1 < 0 ↔ t < 1 + √2 := by
  have hb : 0 < t - (1 - √2) := by linarith [ht, one_sub_sqrt_two_neg]
  constructor
  · intro h
    have : (t - (1 + √2)) * (t - (1 - √2)) < 0 := by
      rwa [← quad_silver]
    have ha : t - (1 + √2) < 0 := by nlinarith [hb]
    exact sub_neg.mp ha
  · intro ht'
    have ha : t - (1 + √2) < 0 := sub_neg.mpr ht'
    have : (t - (1 + √2)) * (t - (1 - √2)) < 0 := mul_neg_of_neg_of_pos ha hb
    rwa [← quad_silver] at this

lemma Mfam_delta_denom_pos {t : ℝ} (ht : 0 < t) :
    0 < (t + 1) * (2 * t + 1) * (7 * t + 3) * (t ^ 2 + 5 * t + 2) := by
  have ⟨h1, h2, h7, hq⟩ := Mfam_denoms_ne_zero ht
  have h1p : 0 < t + 1 := by linarith
  have h2p : 0 < 2 * t + 1 := by linarith
  have h7p : 0 < 7 * t + 3 := by linarith
  have hqp : 0 < t ^ 2 + 5 * t + 2 := Mfam_quad_denom_pos ht
  positivity

lemma Mfam_delta_num_factor_pos {t : ℝ} (ht : 0 < t) : 0 < 2 * (3 * t + 1) := by
  nlinarith

/-- Colbrook (19): failure on the empty-base pair \(\{0,1\}\) is exactly the
open interval between the golden ratio and \(1+\sqrt{2}\). -/
theorem Mfam_delta_neg_iff {t : ℝ} (ht : 0 < t) :
    cramerNystromError (Mfam t) (∅ : Finset (Fin 3)) +
        cramerNystromError (Mfam t) ({0, 1} : Finset (Fin 3)) <
      cramerNystromError (Mfam t) ({0} : Finset (Fin 3)) +
        cramerNystromError (Mfam t) ({1} : Finset (Fin 3)) ↔
      Real.goldenRatio < t ∧ t < 1 + √2 := by
  have hΔ := Mfam_delta t ht
  have hden := Mfam_delta_denom_pos ht
  have hfac := Mfam_delta_num_factor_pos ht
  have hiff :
      cramerNystromError (Mfam t) (∅ : Finset (Fin 3)) +
          cramerNystromError (Mfam t) ({0, 1} : Finset (Fin 3)) <
        cramerNystromError (Mfam t) ({0} : Finset (Fin 3)) +
          cramerNystromError (Mfam t) ({1} : Finset (Fin 3)) ↔
        2 * (3 * t + 1) * (t ^ 2 - 2 * t - 1) * (t ^ 2 - t - 1) /
          ((t + 1) * (2 * t + 1) * (7 * t + 3) * (t ^ 2 + 5 * t + 2)) < 0 := by
    constructor
    · intro h
      linarith [hΔ]
    · intro h
      linarith [hΔ]
  refine hiff.trans ?_
  have hdiv : 2 * (3 * t + 1) * (t ^ 2 - 2 * t - 1) * (t ^ 2 - t - 1) /
        ((t + 1) * (2 * t + 1) * (7 * t + 3) * (t ^ 2 + 5 * t + 2)) < 0 ↔
      2 * (3 * t + 1) * (t ^ 2 - 2 * t - 1) * (t ^ 2 - t - 1) < 0 := by
    constructor
    · intro h
      nlinarith [div_mul_cancel₀
        (2 * (3 * t + 1) * (t ^ 2 - 2 * t - 1) * (t ^ 2 - t - 1)) hden.ne']
    · intro h
      exact div_neg_of_neg_of_pos h hden
  refine hdiv.trans ?_
  have hprod : 2 * (3 * t + 1) * (t ^ 2 - 2 * t - 1) * (t ^ 2 - t - 1) < 0 ↔
      (t ^ 2 - 2 * t - 1) * (t ^ 2 - t - 1) < 0 := by
    constructor <;> intro h <;> nlinarith [hfac]
  refine hprod.trans ?_
  set A := t ^ 2 - 2 * t - 1
  set B := t ^ 2 - t - 1
  have hord : A < B := by
    change t ^ 2 - 2 * t - 1 < t ^ 2 - t - 1
    linarith [ht]
  constructor
  · intro hAB
    have hB : 0 < B := by
      by_contra hB
      have : B ≤ 0 := le_of_not_gt hB
      have : 0 ≤ A * B := mul_nonneg_of_nonpos_of_nonpos (hord.le.trans this) this
      linarith
    have hA : A < 0 := by nlinarith
    exact ⟨(quad_golden_pos_iff ht).mp hB, (quad_silver_neg_iff ht).mp hA⟩
  · intro ⟨hφ, hsil⟩
    have hgol : 0 < B := (quad_golden_pos_iff ht).mpr hφ
    have hsi : A < 0 := (quad_silver_neg_iff ht).mpr hsil
    nlinarith

theorem Mfam_delta_neg_real {t : ℝ} (ht : 0 < t)
    (hφ : Real.goldenRatio < t) (hsil : t < 1 + √2) :
    nystromError (Mfam t) (∅ : Finset (Fin 3)) +
        nystromError (Mfam t) ({0, 1} : Finset (Fin 3)) <
      nystromError (Mfam t) ({0} : Finset (Fin 3)) +
        nystromError (Mfam t) ({1} : Finset (Fin 3)) := by
  have h := (Mfam_delta_neg_iff ht).mpr ⟨hφ, hsil⟩
  simpa [cramerNystromError_eq_nystromError] using h

theorem not_supermodular_nystromError_Mfam {t : ℝ} (ht : 0 < t)
    (hφ : Real.goldenRatio < t) (hsil : t < 1 + √2) :
    ¬ Supermodular (nystromError (Mfam t)) := by
  intro hf
  have h := hf ({0} : Finset (Fin 3)) ({1} : Finset (Fin 3))
  have hunion : ({0} : Finset (Fin 3)) ∪ {1} = {0, 1} := by simp
  have hinter : ({0} : Finset (Fin 3)) ∩ {1} = ∅ := by simp
  rw [hunion, hinter] at h
  linarith [h, Mfam_delta_neg_real ht hφ hsil]

theorem Lfam_two_eq_L0 : Lfam 2 = toReal L0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Lfam, toReal, L0] <;> norm_num

theorem two_mem_Lfam_interval : Real.goldenRatio < (2 : ℝ) ∧ (2 : ℝ) < 1 + √2 :=
  ⟨Real.goldenRatio_lt_two, by linarith [one_lt_sqrt_two]⟩

end Counterexamples
end NystromSubmodularity
