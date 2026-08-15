import NystromSubmodularity.Counterexamples.SDDFamily
import NystromSubmodularity.Counterexamples.SDDDim3
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Rat.Cast.Order

/-!
# How common is the SDD failure?

Two finite certified censuses. On the Colbrook family, a seven-point
positive rational grid has a single failure (\(t=2\)), matching
Theorem 10. Among the 64 complete-support integer triangles with
off-diagonals in \(\{\pm 1,\pm 2\}\) and strictly dominant integer
diagonals, exactly four have a negative empty-base \((0,1)\) defect —
the \(L^\sharp\) sign pattern and its signature orbit.
-/

namespace NystromSubmodularity
namespace Counterexamples

open Matrix Finset

def familyGrid : List ℚ := [1 / 2, 1, 3 / 2, 2, 5 / 2, 3, 4]

/-- Off-diagonal triples for the integer strict-SDD census. -/
def integerOffs : List (ℚ × ℚ × ℚ) :=
  let xs : List ℚ := [-2, -1, 1, 2]
  xs.flatMap fun p =>
    xs.flatMap fun q =>
      xs.map fun r => (p, q, r)

/-- Strictly SDD integer triangle with off-diagonals `p,q,r`. -/
def integerTriangle (p q r : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1 + |p| + |q|, p, q;
     p, 1 + |p| + |r|, r;
     q, r, 1 + |q| + |r|]

def integerPrecision (p q r : ℚ) : Matrix (Fin 3) (Fin 3) ℚ :=
  integerTriangle p q r + 1

def integerFailsEmpty01 (p q r : ℚ) : Bool :=
  decide
    (cramerNystromError (integerPrecision p q r) (∅ : Finset (Fin 3)) +
        cramerNystromError (integerPrecision p q r) ({0, 1} : Finset (Fin 3)) <
      cramerNystromError (integerPrecision p q r) ({0} : Finset (Fin 3)) +
        cramerNystromError (integerPrecision p q r) ({1} : Finset (Fin 3)))

theorem integerOffs_card : integerOffs.length = 64 := by native_decide

/-- Exactly four of the 64 integer strict-SDD triangles fail the empty-base
\((0,1)\) test. -/
theorem integer_sdd_census_four_failures :
    (integerOffs.filter (fun t => integerFailsEmpty01 t.1 t.2.1 t.2.2)).length = 4 := by
  native_decide

/-- The four failures are the \(L^\sharp\) pattern and its three signature
images (off-diagonals \(\pm 1,\pm 2\) with two equal signs on the base
pair). -/
theorem integer_sdd_failing_triples :
    integerFailsEmpty01 1 (-2) (-2) = true ∧
      integerFailsEmpty01 (-1) (-2) 2 = true ∧
        integerFailsEmpty01 (-1) 2 (-2) = true ∧
          integerFailsEmpty01 1 2 2 = true := by
  native_decide

/-- On the seven-point family grid, only \(t=2\) lies in
\(\varphi<t<1+\sqrt{2}\). -/
lemma goldenRatio_gt_three_halves : (3 / 2 : ℝ) < Real.goldenRatio := by
  have h : (2 : ℝ) < √5 := (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 2)).mpr (by norm_num)
  rw [Real.goldenRatio]
  linarith

lemma one_add_sqrt_two_lt_five_halves : 1 + √2 < (5 / 2 : ℝ) := by
  have h : √2 < (3 / 2 : ℝ) := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  linarith

lemma goldenRatio_lt_two : Real.goldenRatio < (2 : ℝ) := by
  have h : √5 < (3 : ℝ) := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  rw [Real.goldenRatio]
  linarith

lemma two_lt_one_add_sqrt_two : (2 : ℝ) < 1 + √2 := by
  have h : (1 : ℝ) < √2 := (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).mpr (by norm_num)
  linarith

theorem Lfam_grid_interval :
    (∀ t ∈ ([1 / 2, 1, 3 / 2, 5 / 2, 3, 4] : List ℝ),
        ¬ (Real.goldenRatio < t ∧ t < 1 + √2)) ∧
      (Real.goldenRatio < (2 : ℝ) ∧ (2 : ℝ) < 1 + √2) := by
  constructor
  · intro t ht
    simp at ht
    rcases ht with (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact fun h =>
        (not_lt.mpr (le_of_lt (lt_trans (by norm_num : (2 : ℝ)⁻¹ < 1)
          Real.one_lt_goldenRatio))) (by simpa using h.1)
    · exact fun h => (not_lt.mpr (le_of_lt Real.one_lt_goldenRatio)) h.1
    · exact fun h => (not_lt.mpr (le_of_lt goldenRatio_gt_three_halves)) h.1
    · exact fun h => (not_lt.mpr (le_of_lt one_add_sqrt_two_lt_five_halves)) h.2
    · exact fun h => (not_lt.mpr (le_of_lt (lt_trans one_add_sqrt_two_lt_five_halves
        (by norm_num : (5 / 2 : ℝ) < 3)))) h.2
    · exact fun h => (not_lt.mpr (le_of_lt (lt_trans one_add_sqrt_two_lt_five_halves
        (by norm_num : (5 / 2 : ℝ) < 4)))) h.2
  · exact ⟨goldenRatio_lt_two, two_lt_one_add_sqrt_two⟩

theorem Lfam_grid_only_two_fails :
    ¬ Supermodular (nystromError (Mfam 2)) :=
  not_supermodular_nystromError_Mfam (by norm_num)
    goldenRatio_lt_two two_lt_one_add_sqrt_two

end Counterexamples
end NystromSubmodularity
