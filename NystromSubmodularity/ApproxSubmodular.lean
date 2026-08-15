import NystromSubmodularity.InverseTrace
import NystromSubmodularity.Computable
import NystromSubmodularity.Counterexamples.SDDDim3
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Approximate supermodularity ratio

The four-point defect \(\Delta(M;A,i,j)\) is nonnegative on every
Stieltjes (hence every SDDM \(+\gamma I\)) precision matrix. For an
arbitrary perturbation \(E\) that keeps \(M+E\) positive definite, the
map \(M\mapsto\mathcal{E}(M,S)\) is Lipschitz in the entrywise
\(\ell^1\) mass of the complementary principal block of \(E\).
Consequently \(\Delta\) can drop by at most a controlled slack
(\(\varepsilon\)-approximate supermodularity), and the ratio
\(\gamma=(\mathcal{E}(A)+\mathcal{E}(A\cup\{i,j\}))/(\mathcal{E}(A\cup\{i\})+\mathcal{E}(A\cup\{j\}))\)
stays within a definite distance of \(1\).

On Colbrook’s \(M_0\) the empty-base \((0,1)\) ratio is the certified
rational \(2288/2295<1\).
-/

namespace NystromSubmodularity

open Finset
open scoped Matrix

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Four-point defect and ratio -/

/-- Four-point supermodularity defect of the Nyström error. -/
noncomputable def fourPointDefect (M : Matrix ι ι ℝ) (A : Finset ι) (i j : ι) : ℝ :=
  nystromError M A + nystromError M (insert j (insert i A)) -
    nystromError M (insert i A) - nystromError M (insert j A)

/-- Numerator of the approximate supermodularity ratio. -/
noncomputable def fourPointNum (M : Matrix ι ι ℝ) (A : Finset ι) (i j : ι) : ℝ :=
  nystromError M A + nystromError M (insert j (insert i A))

/-- Denominator of the approximate supermodularity ratio. -/
noncomputable def fourPointDen (M : Matrix ι ι ℝ) (A : Finset ι) (i j : ι) : ℝ :=
  nystromError M (insert i A) + nystromError M (insert j A)

theorem fourPointDefect_eq_num_sub_den (M : Matrix ι ι ℝ) (A : Finset ι) (i j : ι) :
    fourPointDefect M A i j = fourPointNum M A i j - fourPointDen M A i j := by
  simp [fourPointDefect, fourPointNum, fourPointDen]
  ring

/-- Approximate supermodularity ratio of a four-point pair. Exact
supermodularity is the inequality `1 ≤ supermodularityRatio`. -/
noncomputable def supermodularityRatio (M : Matrix ι ι ℝ) (A : Finset ι) (i j : ι) : ℝ :=
  if fourPointDen M A i j = 0 then 1
  else fourPointNum M A i j / fourPointDen M A i j

theorem supermodularityRatio_of_den_eq_zero {M : Matrix ι ι ℝ} {A : Finset ι} {i j : ι}
    (h : fourPointDen M A i j = 0) :
    supermodularityRatio M A i j = 1 :=
  if_pos h

theorem supermodularityRatio_of_den_ne_zero {M : Matrix ι ι ℝ} {A : Finset ι} {i j : ι}
    (h : fourPointDen M A i j ≠ 0) :
    supermodularityRatio M A i j = fourPointNum M A i j / fourPointDen M A i j :=
  if_neg h

theorem fourPointDefect_eq_den_mul_ratio_sub_one {M : Matrix ι ι ℝ} {A : Finset ι}
    {i j : ι} (h : fourPointDen M A i j ≠ 0) :
    fourPointDefect M A i j =
      fourPointDen M A i j * (supermodularityRatio M A i j - 1) := by
  rw [fourPointDefect_eq_num_sub_den, supermodularityRatio_of_den_ne_zero h]
  field_simp [h]

/-! ## Entrywise \(\ell^1\) mass -/

/-- Entrywise \(\ell^1\) mass of a real matrix. -/
def entryL1 (M : Matrix ι ι ℝ) : ℝ :=
  ∑ i : ι, ∑ j : ι, |M i j|

theorem entryL1_nonneg (M : Matrix ι ι ℝ) : 0 ≤ entryL1 M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem entryL1_neg (M : Matrix ι ι ℝ) : entryL1 (-M) = entryL1 M := by
  simp [entryL1, abs_neg]

theorem entryL1_sub_comm (A B : Matrix ι ι ℝ) : entryL1 (A - B) = entryL1 (B - A) := by
  rw [← neg_sub, entryL1_neg]

theorem abs_trace_le_entryL1 (A : Matrix ι ι ℝ) : |A.trace| ≤ entryL1 A := by
  unfold entryL1
  refine (abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  exact Finset.single_le_sum (fun j _ => abs_nonneg (A i j)) (mem_univ i)

theorem entryL1_mul (A B : Matrix ι ι ℝ) :
    entryL1 (A * B) ≤ entryL1 A * entryL1 B := by
  have habs :
      entryL1 (A * B) ≤ ∑ i : ι, ∑ j : ι, ∑ k : ι, |A i k| * |B k j| := by
    unfold entryL1
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    simpa [Matrix.mul_apply, abs_mul] using
      (abs_sum_le_sum_abs (s := univ) (fun k : ι => A i k * B k j))
  have hswap :
      (∑ i : ι, ∑ j : ι, ∑ k : ι, |A i k| * |B k j|) =
        ∑ k : ι, (∑ i : ι, |A i k|) * (∑ j : ι, |B k j|) := by
    calc
      ∑ i : ι, ∑ j : ι, ∑ k : ι, |A i k| * |B k j|
        = ∑ i : ι, ∑ k : ι, ∑ j : ι, |A i k| * |B k j| := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i : ι, ∑ k : ι, |A i k| * ∑ j : ι, |B k j| := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
            (Finset.mul_sum _ _ _).symm
      _ = ∑ k : ι, ∑ i : ι, |A i k| * ∑ j : ι, |B k j| := Finset.sum_comm
      _ = ∑ k : ι, (∑ i : ι, |A i k|) * (∑ j : ι, |B k j|) := by
          refine Finset.sum_congr rfl fun k _ => (Finset.sum_mul _ _ _).symm
  have hA : entryL1 A = ∑ k : ι, ∑ i : ι, |A i k| := by
    unfold entryL1
    exact Finset.sum_comm
  have hB : entryL1 B = ∑ k : ι, ∑ j : ι, |B k j| := rfl
  have ha : ∀ k : ι, 0 ≤ ∑ i : ι, |A i k| :=
    fun k => Finset.sum_nonneg fun i _ => abs_nonneg (A i k)
  have hb_le : ∀ k : ι, ∑ j : ι, |B k j| ≤ entryL1 B := fun k => by
    rw [hB]
    exact Finset.single_le_sum
      (fun k' _ => Finset.sum_nonneg fun j _ => abs_nonneg (B k' j)) (mem_univ k)
  have hprod :
      (∑ k : ι, (∑ i : ι, |A i k|) * (∑ j : ι, |B k j|)) ≤ entryL1 A * entryL1 B := by
    calc
      ∑ k : ι, (∑ i : ι, |A i k|) * (∑ j : ι, |B k j|)
        ≤ ∑ k : ι, (∑ i : ι, |A i k|) * entryL1 B :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hb_le k) (ha k)
      _ = (∑ k : ι, ∑ i : ι, |A i k|) * entryL1 B := (Finset.sum_mul _ _ _).symm
      _ = entryL1 A * entryL1 B := by rw [hA]
  exact habs.trans (hswap.trans_le hprod)

theorem principalSubmatrix_add (M E : Matrix ι ι ℝ) (T : Finset ι) :
    principalSubmatrix (M + E) T = principalSubmatrix M T + principalSubmatrix E T := by
  ext i j
  simp

theorem principalSubmatrix_sub (M E : Matrix ι ι ℝ) (T : Finset ι) :
    principalSubmatrix (M - E) T = principalSubmatrix M T - principalSubmatrix E T := by
  ext i j
  simp

theorem sum_principalIndex (T : Finset ι) (f : ι → ℝ) :
    ∑ p : PrincipalIndex T, f p.1 = ∑ i ∈ T, f i := by
  rw [Finset.univ_eq_attach T, Finset.sum_attach T f]

theorem entryL1_principal_le (M : Matrix ι ι ℝ) (T : Finset ι) :
    entryL1 (principalSubmatrix M T) ≤ entryL1 M := by
  unfold entryL1
  simp only [principalSubmatrix_apply]
  have hinner : ∀ i ∈ T, ∑ q : PrincipalIndex T, |M i q.1| ≤ ∑ j : ι, |M i j| := by
    intro i _
    rw [sum_principalIndex T (fun j => |M i j|)]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ T) fun _ _ _ => abs_nonneg _
  have houter :
      ∑ p : PrincipalIndex T, ∑ j : ι, |M p.1 j| ≤ ∑ i : ι, ∑ j : ι, |M i j| := by
    rw [sum_principalIndex T (fun i => ∑ j : ι, |M i j|)]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ T)
      fun _ _ _ => sum_nonneg fun _ _ => abs_nonneg _
  calc
    ∑ p : PrincipalIndex T, ∑ q : PrincipalIndex T, |M p.1 q.1|
      ≤ ∑ p : PrincipalIndex T, ∑ j : ι, |M p.1 j| :=
        sum_le_sum fun p _ => hinner p.1 p.2
    _ ≤ ∑ i : ι, ∑ j : ι, |M i j| := houter

/-! ## Inverse-trace Lipschitz bound -/

/-- Entrywise \(\ell^1\) mass of a principal inverse. -/
noncomputable def invEntryBound (M : Matrix ι ι ℝ) (T : Finset ι) : ℝ :=
  entryL1 (principalSubmatrix M T)⁻¹

theorem posDef_principal {M : Matrix ι ι ℝ} (hM : M.PosDef) (T : Finset ι) :
    (principalSubmatrix M T).PosDef :=
  hM.submatrix Subtype.val_injective

theorem nystromError_nonneg {M : Matrix ι ι ℝ} (hM : M.PosDef) (S : Finset ι) :
    0 ≤ nystromError M S :=
  ((posDef_principal hM (compl S)).inv).posSemidef.trace_nonneg

theorem abs_traceInv_sub_le {M E : Matrix ι ι ℝ} {T : Finset ι}
    (hM : M.PosDef) (hME : (M + E).PosDef) :
    |traceInv (M + E) T - traceInv M T| ≤
      invEntryBound (M + E) T * entryL1 (principalSubmatrix E T) * invEntryBound M T := by
  have hP : (principalSubmatrix M T).PosDef := posDef_principal hM T
  have hPE : (principalSubmatrix (M + E) T).PosDef := posDef_principal hME T
  have hiff : IsUnit (principalSubmatrix (M + E) T) ↔ IsUnit (principalSubmatrix M T) :=
    iff_of_true hPE.isUnit hP.isUnit
  have hdiff :
      (principalSubmatrix (M + E) T)⁻¹ - (principalSubmatrix M T)⁻¹ =
        (principalSubmatrix (M + E) T)⁻¹ *
          (principalSubmatrix M T - principalSubmatrix (M + E) T) *
          (principalSubmatrix M T)⁻¹ :=
    Matrix.inv_sub_inv hiff
  have hE : principalSubmatrix M T - principalSubmatrix (M + E) T =
      -principalSubmatrix E T := by
    rw [principalSubmatrix_add]
    abel
  unfold traceInv invEntryBound
  have htr :
      |(principalSubmatrix (M + E) T)⁻¹.trace - (principalSubmatrix M T)⁻¹.trace| =
        |((principalSubmatrix (M + E) T)⁻¹ - (principalSubmatrix M T)⁻¹).trace| := by
    rw [Matrix.trace_sub]
  rw [htr, hdiff, hE]
  have hbound :=
    abs_trace_le_entryL1
      ((principalSubmatrix (M + E) T)⁻¹ * (-principalSubmatrix E T) *
        (principalSubmatrix M T)⁻¹)
  refine hbound.trans ?_
  have hmul :=
    (entryL1_mul
        ((principalSubmatrix (M + E) T)⁻¹ * (-principalSubmatrix E T))
        (principalSubmatrix M T)⁻¹).trans
      (mul_le_mul_of_nonneg_right
        (entryL1_mul (principalSubmatrix (M + E) T)⁻¹ (-principalSubmatrix E T))
        (entryL1_nonneg _))
  refine hmul.trans ?_
  rw [entryL1_neg]

/-- Lipschitz bound for a single Nyström value. -/
noncomputable def nystromLipschitzBound (M E : Matrix ι ι ℝ) (S : Finset ι) : ℝ :=
  invEntryBound (M + E) (compl S) * entryL1 (principalSubmatrix E (compl S)) *
    invEntryBound M (compl S)

theorem nystromLipschitzBound_le_entryL1 (M E : Matrix ι ι ℝ) (S : Finset ι) :
    nystromLipschitzBound M E S ≤
      invEntryBound (M + E) (compl S) * entryL1 E * invEntryBound M (compl S) := by
  unfold nystromLipschitzBound
  refine mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (entryL1_principal_le E (compl S))
      (entryL1_nonneg _))
    (entryL1_nonneg _)

theorem abs_nystromError_sub_le {M E : Matrix ι ι ℝ} {S : Finset ι}
    (hM : M.PosDef) (hME : (M + E).PosDef) :
    |nystromError (M + E) S - nystromError M S| ≤ nystromLipschitzBound M E S :=
  abs_traceInv_sub_le hM hME

theorem abs_add_sub_sub_le (a b c d : ℝ) :
    |a + b - c - d| ≤ |a| + |b| + |c| + |d| := by
  have h : a + b - c - d = (a + b) - (c + d) := by abel
  rw [h]
  calc
    |(a + b) - (c + d)| ≤ |a + b| + |c + d| := abs_sub _ _
    _ ≤ |a| + |b| + |c| + |d| := by
      linarith [abs_add_le a b, abs_add_le c d]

/-- Four-term Lipschitz slack of a four-point defect. -/
noncomputable def fourPointLipschitzBound (M E : Matrix ι ι ℝ) (A : Finset ι)
    (i j : ι) : ℝ :=
  nystromLipschitzBound M E A +
    nystromLipschitzBound M E (insert j (insert i A)) +
      nystromLipschitzBound M E (insert i A) +
        nystromLipschitzBound M E (insert j A)

theorem abs_fourPointDefect_sub_le {M E : Matrix ι ι ℝ} {A : Finset ι} {i j : ι}
    (hM : M.PosDef) (hME : (M + E).PosDef) :
    |fourPointDefect (M + E) A i j - fourPointDefect M A i j| ≤
      fourPointLipschitzBound M E A i j := by
  unfold fourPointDefect fourPointLipschitzBound
  have hA := abs_nystromError_sub_le (S := A) hM hME
  have hAi := abs_nystromError_sub_le (S := insert i A) hM hME
  have hAj := abs_nystromError_sub_le (S := insert j A) hM hME
  have hAij := abs_nystromError_sub_le (S := insert j (insert i A)) hM hME
  have hsplit :
      fourPointDefect (M + E) A i j - fourPointDefect M A i j =
        (nystromError (M + E) A - nystromError M A) +
          (nystromError (M + E) (insert j (insert i A)) -
            nystromError M (insert j (insert i A))) -
          (nystromError (M + E) (insert i A) - nystromError M (insert i A)) -
          (nystromError (M + E) (insert j A) - nystromError M (insert j A)) := by
    simp [fourPointDefect]
    ring
  -- unfold already expanded the defects; rewrite the goal's left-hand side.
  change
    |(nystromError (M + E) A + nystromError (M + E) (insert j (insert i A)) -
        nystromError (M + E) (insert i A) - nystromError (M + E) (insert j A)) -
      (nystromError M A + nystromError M (insert j (insert i A)) -
        nystromError M (insert i A) - nystromError M (insert j A))| ≤ _
  have hform :
      (nystromError (M + E) A + nystromError (M + E) (insert j (insert i A)) -
          nystromError (M + E) (insert i A) - nystromError (M + E) (insert j A)) -
        (nystromError M A + nystromError M (insert j (insert i A)) -
          nystromError M (insert i A) - nystromError M (insert j A)) =
        (nystromError (M + E) A - nystromError M A) +
          (nystromError (M + E) (insert j (insert i A)) -
            nystromError M (insert j (insert i A))) -
          (nystromError (M + E) (insert i A) - nystromError M (insert i A)) -
          (nystromError (M + E) (insert j A) - nystromError M (insert j A)) := by
    ring
  rw [hform]
  refine (abs_add_sub_sub_le _ _ _ _).trans ?_
  linarith [hA, hAi, hAj, hAij]

/-- If the unperturbed defect is nonnegative, the perturbed defect is at
least the negative of the four-term Lipschitz slack. -/
theorem fourPointDefect_approx_of_nonneg {M E : Matrix ι ι ℝ} {A : Finset ι}
    {i j : ι} (hM : M.PosDef) (hME : (M + E).PosDef)
    (hΔ : 0 ≤ fourPointDefect M A i j) :
    -fourPointLipschitzBound M E A i j ≤ fourPointDefect (M + E) A i j := by
  have h := abs_fourPointDefect_sub_le (A := A) (i := i) (j := j) hM hME
  have : fourPointDefect M A i j - fourPointLipschitzBound M E A i j ≤
      fourPointDefect (M + E) A i j := by
    linarith [neg_le_abs (fourPointDefect (M + E) A i j - fourPointDefect M A i j),
      le_of_abs_le h]
  linarith

theorem fourPointDefect_nonneg_of_isStieltjes {M : Matrix ι ι ℝ} (hM : IsStieltjes M)
    {A : Finset ι} {i j : ι} (hij : i ≠ j) (hi : i ∉ A) (hj : j ∉ A) :
    0 ≤ fourPointDefect M A i j := by
  have hf : FourPointSupermodular (nystromError M) :=
    fourPointSupermodular_of_supermodular
      (supermodular_compl (traceInv_supermodular_of_isStieltjes hM))
  have h := hf A i j hij hi hj
  simp [fourPointDefect]
  linarith

theorem fourPointDefect_approx_of_isStieltjes {M E : Matrix ι ι ℝ} {A : Finset ι}
    {i j : ι} (hM : IsStieltjes M) (hME : (M + E).PosDef)
    (hij : i ≠ j) (hi : i ∉ A) (hj : j ∉ A) :
    -fourPointLipschitzBound M E A i j ≤ fourPointDefect (M + E) A i j :=
  fourPointDefect_approx_of_nonneg hM.posDef hME
    (fourPointDefect_nonneg_of_isStieltjes hM hij hi hj)

/-! ## Ratio on Stieltjes matrices and under perturbation -/

theorem fourPointNum_nonneg {M : Matrix ι ι ℝ} (hM : M.PosDef) (A : Finset ι)
    (i j : ι) : 0 ≤ fourPointNum M A i j :=
  add_nonneg (nystromError_nonneg hM _) (nystromError_nonneg hM _)

theorem fourPointDen_nonneg {M : Matrix ι ι ℝ} (hM : M.PosDef) (A : Finset ι)
    (i j : ι) : 0 ≤ fourPointDen M A i j :=
  add_nonneg (nystromError_nonneg hM _) (nystromError_nonneg hM _)

theorem one_le_supermodularityRatio_of_isStieltjes {M : Matrix ι ι ℝ}
    (hM : IsStieltjes M) {A : Finset ι} {i j : ι}
    (hij : i ≠ j) (hi : i ∉ A) (hj : j ∉ A) :
    1 ≤ supermodularityRatio M A i j := by
  by_cases h0 : fourPointDen M A i j = 0
  · simp [supermodularityRatio, h0]
  · have hpos : 0 < fourPointDen M A i j :=
      lt_of_le_of_ne (fourPointDen_nonneg hM.posDef A i j) (Ne.symm h0)
    have hΔ := fourPointDefect_nonneg_of_isStieltjes hM hij hi hj
    have hnum : fourPointDen M A i j ≤ fourPointNum M A i j := by
      linarith [fourPointDefect_eq_num_sub_den M A i j]
    rw [supermodularityRatio_of_den_ne_zero h0]
    exact (one_le_div hpos).mpr hnum

theorem abs_fourPointNum_sub_le {M E : Matrix ι ι ℝ} {A : Finset ι} {i j : ι}
    {ε : ℝ}
    (hA : |nystromError (M + E) A - nystromError M A| ≤ ε)
    (hAij : |nystromError (M + E) (insert j (insert i A)) -
      nystromError M (insert j (insert i A))| ≤ ε) :
    |fourPointNum (M + E) A i j - fourPointNum M A i j| ≤ 2 * ε := by
  unfold fourPointNum
  have : fourPointNum (M + E) A i j - fourPointNum M A i j =
      (nystromError (M + E) A - nystromError M A) +
        (nystromError (M + E) (insert j (insert i A)) -
          nystromError M (insert j (insert i A))) := by
    simp [fourPointNum]
    ring
  change |(nystromError (M + E) A + nystromError (M + E) (insert j (insert i A))) -
      (nystromError M A + nystromError M (insert j (insert i A)))| ≤ 2 * ε
  have hform :
      (nystromError (M + E) A + nystromError (M + E) (insert j (insert i A))) -
          (nystromError M A + nystromError M (insert j (insert i A))) =
        (nystromError (M + E) A - nystromError M A) +
          (nystromError (M + E) (insert j (insert i A)) -
            nystromError M (insert j (insert i A))) := by
    ring
  rw [hform]
  refine (abs_add_le _ _).trans ?_
  linarith

theorem abs_fourPointDen_sub_le {M E : Matrix ι ι ℝ} {A : Finset ι} {i j : ι}
    {ε : ℝ}
    (hAi : |nystromError (M + E) (insert i A) - nystromError M (insert i A)| ≤ ε)
    (hAj : |nystromError (M + E) (insert j A) - nystromError M (insert j A)| ≤ ε) :
    |fourPointDen (M + E) A i j - fourPointDen M A i j| ≤ 2 * ε := by
  have hform :
      fourPointDen (M + E) A i j - fourPointDen M A i j =
        (nystromError (M + E) (insert i A) - nystromError M (insert i A)) +
          (nystromError (M + E) (insert j A) - nystromError M (insert j A)) := by
    simp [fourPointDen]
    ring
  rw [hform]
  refine (abs_add_le _ _).trans ?_
  linarith

/-- If an unperturbed pair is supermodular (\(\gamma\ge 1\)) and each of
the four Nyström values moves by at most \(\varepsilon\le\mathrm{den}/2\),
the perturbed ratio is at least \(1-4\varepsilon/(\mathrm{den}+2\varepsilon)\). -/
theorem supermodularityRatio_perturbation_lower {M E : Matrix ι ι ℝ}
    {A : Finset ι} {i j : ι} {ε : ℝ}
    (_hM : M.PosDef) (hME : (M + E).PosDef) (hε : 0 ≤ ε)
    (hγ : 1 ≤ supermodularityRatio M A i j)
    (hdenpos : 0 < fourPointDen M A i j)
    (hεden : 2 * ε ≤ fourPointDen M A i j)
    (hA : |nystromError (M + E) A - nystromError M A| ≤ ε)
    (hAi : |nystromError (M + E) (insert i A) - nystromError M (insert i A)| ≤ ε)
    (hAj : |nystromError (M + E) (insert j A) - nystromError M (insert j A)| ≤ ε)
    (hAij : |nystromError (M + E) (insert j (insert i A)) -
      nystromError M (insert j (insert i A))| ≤ ε) :
    1 - 4 * ε / (fourPointDen M A i j + 2 * ε) ≤
      supermodularityRatio (M + E) A i j := by
  have hnumΔ := abs_fourPointNum_sub_le hA hAij
  have hdenΔ := abs_fourPointDen_sub_le hAi hAj
  set den := fourPointDen M A i j
  set den' := fourPointDen (M + E) A i j
  set num := fourPointNum M A i j
  set num' := fourPointNum (M + E) A i j
  have hden0 : den ≠ 0 := hdenpos.ne'
  have hratio : supermodularityRatio M A i j = num / den :=
    supermodularityRatio_of_den_ne_zero hden0
  have hnum_ge : den ≤ num := (one_le_div hdenpos).mp (hratio ▸ hγ)
  have hnum' : den - 2 * ε ≤ num' := by
    have : num - 2 * ε ≤ num' := by
      linarith [neg_le_abs (num' - num), le_of_abs_le (by
        simpa [num, num'] using hnumΔ)]
    linarith
  have hden'u : den' ≤ den + 2 * ε := by
    linarith [le_of_abs_le (by simpa [den, den'] using hdenΔ)]
  have hden'n : 0 ≤ den' := fourPointDen_nonneg hME A i j
  have hnum'n : 0 ≤ den - 2 * ε := sub_nonneg.mpr hεden
  have hden2 : 0 < den + 2 * ε := by linarith
  by_cases hden'0 : den' = 0
  · rw [supermodularityRatio_of_den_eq_zero (by simpa [den'] using hden'0)]
    have : 0 ≤ 4 * ε / (den + 2 * ε) :=
      div_nonneg (mul_nonneg (by norm_num) hε) hden2.le
    linarith
  · have hden'pos : 0 < den' := lt_of_le_of_ne hden'n (Ne.symm hden'0)
    rw [supermodularityRatio_of_den_ne_zero (by simpa [den'] using hden'0)]
    have hfrac : (den - 2 * ε) / (den + 2 * ε) ≤ num' / den' := by
      refine (div_le_div_iff₀ hden2 hden'pos).mpr ?_
      have h1 : (den - 2 * ε) * den' ≤ (den - 2 * ε) * (den + 2 * ε) :=
        mul_le_mul_of_nonneg_left hden'u hnum'n
      have h2 : (den - 2 * ε) * (den + 2 * ε) ≤ num' * (den + 2 * ε) :=
        mul_le_mul_of_nonneg_right hnum' hden2.le
      linarith
    have hid : (den - 2 * ε) / (den + 2 * ε) = 1 - 4 * ε / (den + 2 * ε) := by
      field_simp [hden2.ne']
      ring
    simpa [num', den', hid] using hfrac

theorem supermodularityRatio_perturbation_of_lipschitz {M E : Matrix ι ι ℝ}
    {A : Finset ι} {i j : ι} {ε : ℝ}
    (hM : M.PosDef) (hME : (M + E).PosDef) (hε : 0 ≤ ε)
    (hγ : 1 ≤ supermodularityRatio M A i j)
    (hdenpos : 0 < fourPointDen M A i j)
    (hεden : 2 * ε ≤ fourPointDen M A i j)
    (hA : nystromLipschitzBound M E A ≤ ε)
    (hAi : nystromLipschitzBound M E (insert i A) ≤ ε)
    (hAj : nystromLipschitzBound M E (insert j A) ≤ ε)
    (hAij : nystromLipschitzBound M E (insert j (insert i A)) ≤ ε) :
    1 - 4 * ε / (fourPointDen M A i j + 2 * ε) ≤
      supermodularityRatio (M + E) A i j :=
  supermodularityRatio_perturbation_lower hM hME hε hγ hdenpos hεden
    ((abs_nystromError_sub_le hM hME).trans hA)
    ((abs_nystromError_sub_le hM hME).trans hAi)
    ((abs_nystromError_sub_le hM hME).trans hAj)
    ((abs_nystromError_sub_le hM hME).trans hAij)

/-! ## Certified ratio on \(M_0\) -/

open Counterexamples

theorem M0_supermodularityRatio_empty_zero_one :
    supermodularityRatio (toReal M0) (∅ : Finset (Fin 3)) 0 1 =
      (2288 / 2295 : ℝ) := by
  have hemp : nystromError (toReal M0) (∅ : Finset (Fin 3)) = ((47 / 51 : ℚ) : ℝ) := by
    rw [← toReal_nystromError, M0_cramer_empty]
  have h0 : nystromError (toReal M0) ({0} : Finset (Fin 3)) = ((9 / 16 : ℚ) : ℝ) := by
    rw [← toReal_nystromError, M0_cramer_zero]
  have h1 : nystromError (toReal M0) ({1} : Finset (Fin 3)) = ((9 / 16 : ℚ) : ℝ) := by
    rw [← toReal_nystromError, M0_cramer_one]
  have h01 : nystromError (toReal M0) ({0, 1} : Finset (Fin 3)) = ((1 / 5 : ℚ) : ℝ) := by
    rw [← toReal_nystromError, M0_cramer_zero_one]
  have hi : insert (0 : Fin 3) (∅ : Finset (Fin 3)) = {0} := by simp
  have hj : insert (1 : Fin 3) (∅ : Finset (Fin 3)) = {1} := by simp
  have hij : insert (1 : Fin 3) (insert 0 (∅ : Finset (Fin 3))) = {0, 1} := by decide
  have hden : fourPointDen (toReal M0) (∅ : Finset (Fin 3)) 0 1 ≠ 0 := by
    unfold fourPointDen
    rw [hi, hj, h0, h1]
    norm_num
  unfold supermodularityRatio
  rw [if_neg hden]
  unfold fourPointNum fourPointDen
  rw [hij, hi, hj, hemp, h0, h1, h01]
  norm_num

theorem M0_supermodularityRatio_lt_one :
    supermodularityRatio (toReal M0) (∅ : Finset (Fin 3)) 0 1 < 1 := by
  rw [M0_supermodularityRatio_empty_zero_one]
  norm_num

theorem M0_fourPointDefect_eq_ratio_form :
    fourPointDefect (toReal M0) (∅ : Finset (Fin 3)) 0 1 = ((-7 / 2040 : ℚ) : ℝ) := by
  have hemp : nystromError (toReal M0) (∅ : Finset (Fin 3)) = ((47 / 51 : ℚ) : ℝ) := by
    rw [← toReal_nystromError, M0_cramer_empty]
  have h0 : nystromError (toReal M0) ({0} : Finset (Fin 3)) = ((9 / 16 : ℚ) : ℝ) := by
    rw [← toReal_nystromError, M0_cramer_zero]
  have h1 : nystromError (toReal M0) ({1} : Finset (Fin 3)) = ((9 / 16 : ℚ) : ℝ) := by
    rw [← toReal_nystromError, M0_cramer_one]
  have h01 : nystromError (toReal M0) ({0, 1} : Finset (Fin 3)) = ((1 / 5 : ℚ) : ℝ) := by
    rw [← toReal_nystromError, M0_cramer_zero_one]
  have hi : insert (0 : Fin 3) (∅ : Finset (Fin 3)) = {0} := by simp
  have hj : insert (1 : Fin 3) (∅ : Finset (Fin 3)) = {1} := by simp
  have hij : insert (1 : Fin 3) (insert 0 (∅ : Finset (Fin 3))) = {0, 1} := by decide
  unfold fourPointDefect
  rw [hij, hi, hj, hemp, h0, h1, h01]
  norm_num

end NystromSubmodularity
