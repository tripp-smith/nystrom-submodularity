import NystromSubmodularity.Counterexamples.SDDFamily
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Data.Rat.Cast.Order

/-!
# Greedy one-column misselection

Colbrook (31)–(33): on the failure interval of \(L(t)\), and on the strictly
SDD witness \(L^\sharp\), greedy one-column selection picks index \(2\),
which lies in no optimal pair.
-/

namespace NystromSubmodularity
namespace Counterexamples

open Matrix Finset

lemma one_lt_goldenRatio : (1 : ℝ) < Real.goldenRatio := by
  have h5 : (1 : ℝ) < √5 := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
    norm_num
  have hφ : Real.goldenRatio = (1 + √5) / 2 := rfl
  linarith [hφ, h5]

lemma one_lt_of_mem_Lfam_interval {t : ℝ} (hφ : Real.goldenRatio < t) : 1 < t :=
  lt_trans one_lt_goldenRatio hφ

lemma Mfam_singleton_two_lt_zero {t : ℝ} (ht : 1 < t) :
    cramerNystromError (Mfam t) ({2} : Finset (Fin 3)) <
      cramerNystromError (Mfam t) ({0} : Finset (Fin 3)) := by
  have ht0 : 0 < t := lt_trans (by norm_num : (0 : ℝ) < 1) ht
  have ⟨h1, _, _, hq⟩ := Mfam_denoms_ne_zero ht0
  have ⟨_, ht3⟩ := Mfam_extra_denoms_ne_zero ht0
  have hden2 : 0 < (t + 1) * (t + 3) := by nlinarith
  have hden0 : 0 < t ^ 2 + 5 * t + 2 := Mfam_quad_denom_pos ht0
  rw [Mfam_cramer_two, Mfam_cramer_zero]
  refine (div_lt_div_iff₀ hden2 hden0).mpr ?_
  have hdiff : 3 * (t + 1) ^ 2 * (t + 3) - 2 * (t + 2) * (t ^ 2 + 5 * t + 2) =
      (t - 1) * (t ^ 2 + 2 * t - 1) := by ring
  have hpos : 0 < (t - 1) * (t ^ 2 + 2 * t - 1) := by
    have hlin : 0 < t - 1 := sub_pos.mpr ht
    have hquad : 0 < t ^ 2 + 2 * t - 1 := by
      nlinarith [sq_nonneg (t + 1), ht]
    exact mul_pos hlin hquad
  linarith [hdiff, hpos]

lemma Mfam_pair_zero_one_lt_zero_two {t : ℝ} (ht : 1 < t) :
    cramerNystromError (Mfam t) ({0, 1} : Finset (Fin 3)) <
      cramerNystromError (Mfam t) ({0, 2} : Finset (Fin 3)) := by
  have ht0 : 0 < t := lt_trans (by norm_num : (0 : ℝ) < 1) ht
  have ⟨_, h2, _, _⟩ := Mfam_denoms_ne_zero ht0
  have ⟨ht2, _⟩ := Mfam_extra_denoms_ne_zero ht0
  rw [Mfam_cramer_zero_one, Mfam_cramer_zero_two]
  exact (inv_lt_inv₀ (by linarith : (0 : ℝ) < 2 * t + 1)
      (by linarith : (0 : ℝ) < t + 2)).mpr (by linarith)

lemma Mfam_pair_ratio {t : ℝ} (ht : 0 < t) :
    cramerNystromError (Mfam t) ({0, 2} : Finset (Fin 3)) /
        cramerNystromError (Mfam t) ({0, 1} : Finset (Fin 3)) =
      (2 * t + 1) / (t + 2) := by
  have ⟨_, h2, _, _⟩ := Mfam_denoms_ne_zero ht
  have ⟨ht2, _⟩ := Mfam_extra_denoms_ne_zero ht
  rw [Mfam_cramer_zero_two, Mfam_cramer_zero_one]
  field_simp [h2, ht2]

lemma Mfam_pair_ratio_gt_one {t : ℝ} (ht : 1 < t) :
    1 < (2 * t + 1) / (t + 2) := by
  have ht2 : 0 < t + 2 := by linarith
  refine (one_lt_div ht2).mpr ?_
  linarith

lemma Mfam_pair_ratio_at_two : (2 * (2 : ℝ) + 1) / (2 + 2) = 5 / 4 := by
  norm_num

lemma fin3_card_two {s : Finset (Fin 3)} (hs : s.card = 2) :
    s = {0, 1} ∨ s = {0, 2} ∨ s = {1, 2} := by
  revert s
  decide

lemma fin3_ne_two {i : Fin 3} (hi : i ≠ 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp_all

/-- On the Colbrook interval, greedy one-column selection on \(L(t)\)
picks index \(2\), which lies in no optimal pair. -/
theorem Lfam_greedy_misses_optimal_pair {t : ℝ}
    (hφ : Real.goldenRatio < t) (_hsil : t < 1 + √2) :
    (∀ i : Fin 3, i ≠ 2 →
      nystromError (Lfam t + 1) ({2} : Finset (Fin 3)) <
        nystromError (Lfam t + 1) {i}) ∧
    (∀ s : Finset (Fin 3), s.card = 2 → s ≠ {0, 1} →
      nystromError (Lfam t + 1) ({0, 1} : Finset (Fin 3)) <
        nystromError (Lfam t + 1) s) ∧
    nystromError (Lfam t + 1) ({0, 2} : Finset (Fin 3)) /
        nystromError (Lfam t + 1) ({0, 1} : Finset (Fin 3)) =
      (2 * t + 1) / (t + 2) := by
  have ht : 0 < t := lt_trans Real.goldenRatio_pos hφ
  have ht1 : 1 < t := one_lt_of_mem_Lfam_interval hφ
  have hLM : Lfam t + 1 = Mfam t := (Lfam_eq_Mfam_sub_one t).symm
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [hLM]
    have hlt := Mfam_singleton_two_lt_zero ht1
    rcases fin3_ne_two hi with rfl | rfl
    · simpa [cramerNystromError_eq_nystromError] using hlt
    · have h01 : nystromError (Mfam t) ({0} : Finset (Fin 3)) =
          nystromError (Mfam t) ({1} : Finset (Fin 3)) := by
        simp [← cramerNystromError_eq_nystromError, Mfam_cramer_zero, Mfam_cramer_one]
      rw [← h01]
      simpa [cramerNystromError_eq_nystromError] using hlt
  · intro s hs hne
    rw [hLM]
    have hlt := Mfam_pair_zero_one_lt_zero_two ht1
    rcases fin3_card_two hs with rfl | rfl | rfl
    · exact (hne rfl).elim
    · simpa [cramerNystromError_eq_nystromError] using hlt
    · have hpair : nystromError (Mfam t) ({0, 2} : Finset (Fin 3)) =
          nystromError (Mfam t) ({1, 2} : Finset (Fin 3)) := by
        simp [← cramerNystromError_eq_nystromError, Mfam_cramer_zero_two, Mfam_cramer_one_two]
      rw [← hpair]
      simpa [cramerNystromError_eq_nystromError] using hlt
  · rw [hLM]
    simpa [cramerNystromError_eq_nystromError] using Mfam_pair_ratio ht

/-- On \(L^\sharp\), greedy picks \(\{2\}\) (\(5/12<11/26\)); the resulting
pair residual is \(1/5\), worse than the optimum \(1/6\). -/
theorem Lsharp_greedy_misses_optimal_pair :
    nystromError (toReal Msharp) ({2} : Finset (Fin 3)) = ((5 / 12 : ℚ) : ℝ) ∧
    nystromError (toReal Msharp) ({0} : Finset (Fin 3)) = ((11 / 26 : ℚ) : ℝ) ∧
    ((5 / 12 : ℚ) : ℝ) < ((11 / 26 : ℚ) : ℝ) ∧
    nystromError (toReal Msharp) ({0, 1} : Finset (Fin 3)) = ((1 / 6 : ℚ) : ℝ) ∧
    nystromError (toReal Msharp) ({0, 2} : Finset (Fin 3)) = ((1 / 5 : ℚ) : ℝ) ∧
    ((1 / 6 : ℚ) : ℝ) < ((1 / 5 : ℚ) : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← toReal_nystromError, Msharp_cramer_two]
  · rw [← toReal_nystromError, Msharp_cramer_zero]
  · norm_num
  · rw [← toReal_nystromError, Msharp_cramer_zero_one]
  · rw [← toReal_nystromError, Msharp_cramer_zero_two]
  · norm_num

end Counterexamples
end NystromSubmodularity
