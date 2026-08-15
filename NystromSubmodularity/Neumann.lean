import NystromSubmodularity.Stieltjes
import NystromSubmodularity.Definitions
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Neumann / closed-walk rewrite

Colbrook Proof 3.2 expands principal inverses of a Stieltjes matrix as a
Neumann series of the splitting \(B=sI-M\). This file formalizes the
splitting and the walk interpretation of the first two powers: the
length-1 traces are modular, and the length-2 closed-walk trace is
supermodular when \(B\) is entrywise nonnegative. The infinite series
identity \((I-A)^{-1}=\sum_k A^k\) holds in the \(\ell^2\) operator
norm whenever \(\|A\|_2<1\), and every positive-definite matrix admits
a splitting to which the identity applies.
-/

namespace NystromSubmodularity

open Matrix Finset

/-- Splitting matrix \(B=sI-M\). -/
def neumannSplit {ι : Type*} [DecidableEq ι] (s : ℝ) (M : Matrix ι ι ℝ) :
    Matrix ι ι ℝ :=
  s • (1 : Matrix ι ι ℝ) - M

/-- For a Stieltjes matrix, any \(s\) at least the largest diagonal entry
makes the splitting entrywise nonnegative. -/
theorem neumannSplit_nonneg {ι : Type*} [DecidableEq ι]
    {M : Matrix ι ι ℝ} (hM : IsStieltjes M) {s : ℝ}
    (hs : ∀ i : ι, M i i ≤ s) (i j : ι) :
    0 ≤ neumannSplit s M i j := by
  unfold neumannSplit
  by_cases hij : i = j
  · subst hij
    simp
    linarith [hs i]
  · have h1 : (1 : Matrix ι ι ℝ) i j = 0 := Matrix.one_apply_ne hij
    simp [h1, Matrix.sub_apply, Matrix.smul_apply]
    exact hM.offDiag_nonpos hij

/-- Length-1 closed-walk trace \(\operatorname{tr}(B[T])=\sum_{i\in T}B_{ii}\). -/
def walkTraceOne {ι : Type*} (B : Matrix ι ι ℝ) (T : Finset ι) : ℝ :=
  ∑ i ∈ T, B i i

/-- Length-2 closed-walk trace \(\sum_{i,j\in T}B_{ij}B_{ji}\). -/
def walkTraceTwo {ι : Type*} (B : Matrix ι ι ℝ) (T : Finset ι) : ℝ :=
  ∑ i ∈ T, ∑ j ∈ T, B i j * B j i

theorem walkTraceOne_eq_trace {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ)
    (T : Finset ι) :
    walkTraceOne B T = (principalSubmatrix B T).trace := by
  simp [walkTraceOne, Matrix.trace, principalSubmatrix, Matrix.diag]
  exact (Finset.sum_attach T (fun i => B i i)).symm

theorem walkTraceOne_modular {ι : Type*} [DecidableEq ι] (B : Matrix ι ι ℝ) :
    Supermodular (walkTraceOne B) ∧ Submodular (walkTraceOne B) := by
  constructor
  · intro A C
    simp [walkTraceOne, sum_union_inter]
  · intro A C
    simp [walkTraceOne, sum_union_inter]

theorem indicator_mem_pair_supermodular {ι : Type*} [DecidableEq ι] (i j : ι) :
    Supermodular (fun T : Finset ι => if i ∈ T ∧ j ∈ T then (1 : ℝ) else 0) := by
  intro A C
  by_cases hiA : i ∈ A <;> by_cases hjA : j ∈ A <;>
    by_cases hiC : i ∈ C <;> by_cases hjC : j ∈ C <;>
      simp [hiA, hjA, hiC, hjC, mem_union, mem_inter]

lemma walkTraceTwo_as_ite {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (T : Finset ι) :
    walkTraceTwo B T =
      ∑ i : ι, ∑ j : ι,
        B i j * B j i * (if i ∈ T ∧ j ∈ T then (1 : ℝ) else 0) := by
  unfold walkTraceTwo
  have hT : T = (univ : Finset ι).filter (· ∈ T) := by
    ext x; simp
  conv_lhs => rw [hT]
  simp [ite_and, mul_ite, mul_zero, mul_one]

theorem walkTraceTwo_supermodular {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : ∀ i j : ι, 0 ≤ B i j) :
    Supermodular (walkTraceTwo B) := by
  intro A C
  have hw (i j : ι) : 0 ≤ B i j * B j i := mul_nonneg (hB i j) (hB j i)
  have hcoeff (i j : ι) :
      B i j * B j i *
          ((if i ∈ A ∧ j ∈ A then (1 : ℝ) else 0) +
            (if i ∈ C ∧ j ∈ C then (1 : ℝ) else 0)) ≤
        B i j * B j i *
          ((if i ∈ A ∪ C ∧ j ∈ A ∪ C then (1 : ℝ) else 0) +
            (if i ∈ A ∩ C ∧ j ∈ A ∩ C then (1 : ℝ) else 0)) := by
    have hsm := indicator_mem_pair_supermodular (i := i) (j := j) A C
    nlinarith [hw i j, hsm]
  rw [walkTraceTwo_as_ite, walkTraceTwo_as_ite, walkTraceTwo_as_ite,
    walkTraceTwo_as_ite]
  simp_rw [← Finset.sum_add_distrib, ← mul_add]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hcoeff i j

/-- Partial Neumann sum of walk traces, as in Colbrook (12) before the
limit. Each finite sum is supermodular when the splitting is nonnegative. -/
noncomputable def neumannPartial {ι : Type*} (s : ℝ) (B : Matrix ι ι ℝ) (N : ℕ)
    (T : Finset ι) : ℝ :=
  (T.card : ℝ) / s +
    walkTraceOne B T / s ^ 2 +
      (if N = 0 then 0 else walkTraceTwo B T / s ^ 3)

theorem neumannPartial_supermodular {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℝ) (hs : 0 < s) (B : Matrix ι ι ℝ) (hB : ∀ i j : ι, 0 ≤ B i j)
    (N : ℕ) :
    Supermodular (neumannPartial s B N) := by
  intro A C
  have hcard : ((A ∪ C).card : ℝ) / s + ((A ∩ C).card : ℝ) / s =
      (A.card : ℝ) / s + (C.card : ℝ) / s := by
    have := congrArg (fun n : ℕ => (n : ℝ) / s) (card_union_add_card_inter A C)
    simpa [add_div] using this
  have h1 := (walkTraceOne_modular B).1 A C
  have h2 := walkTraceTwo_supermodular B hB A C
  have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs
  have hs3 : 0 < s ^ 3 := pow_pos hs 3
  have h1d : walkTraceOne B A / s ^ 2 + walkTraceOne B C / s ^ 2 ≤
      walkTraceOne B (A ∪ C) / s ^ 2 + walkTraceOne B (A ∩ C) / s ^ 2 := by
    simpa [add_div] using div_le_div_of_nonneg_right h1 hs2.le
  have h2d : walkTraceTwo B A / s ^ 3 + walkTraceTwo B C / s ^ 3 ≤
      walkTraceTwo B (A ∪ C) / s ^ 3 + walkTraceTwo B (A ∩ C) / s ^ 3 := by
    simpa [add_div] using div_le_div_of_nonneg_right h2 hs3.le
  simp only [neumannPartial]
  split_ifs
  · linarith
  · linarith

/-! ## Infinite Neumann series -/

open scoped Matrix.Norms.L2Operator

/-- Geometric series for the matrix inverse in the \(\ell^2\) operator
norm: \(\|A\|_2<1\) implies \((I-A)^{-1}=\sum_k A^k\). -/
theorem neumann_series_inv {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : ‖A‖ < 1) :
    (1 - A)⁻¹ = ∑' k : ℕ, A ^ k := by
  rw [nonsing_inv_eq_ringInverse, geom_series_eq_inverse A hA]

theorem neumannSplit_eq {ι : Type*} [DecidableEq ι] (s : ℝ) (M : Matrix ι ι ℝ) :
    M = s • (1 : Matrix ι ι ℝ) - neumannSplit s M := by
  simp [neumannSplit]

theorem neumannSplit_eq_smul_one_sub {ι : Type*} [DecidableEq ι] (s : ℝ)
    (hs : s ≠ 0) (M : Matrix ι ι ℝ) :
    M = s • ((1 : Matrix ι ι ℝ) - s⁻¹ • neumannSplit s M) := by
  have h : s • (s⁻¹ • neumannSplit s M) = neumannSplit s M := by
    rw [smul_smul, mul_inv_cancel₀ hs, one_smul]
  rw [smul_sub, h]
  exact neumannSplit_eq s M

/-- If the scaled splitting is a contraction, the inverse is the
Neumann series of that splitting. -/
theorem neumannSplit_inv_eq_tsum {n : Type*} [Fintype n] [DecidableEq n]
    (s : ℝ) (hs : 0 < s) (M : Matrix n n ℝ)
    (hB : ‖s⁻¹ • neumannSplit s M‖ < 1) :
    M⁻¹ = s⁻¹ • ∑' k : ℕ, (s⁻¹ • neumannSplit s M) ^ k := by
  set A := s⁻¹ • neumannSplit s M
  have hs0 : s ≠ 0 := hs.ne'
  have hM : M = s • ((1 : Matrix n n ℝ) - A) :=
    neumannSplit_eq_smul_one_sub s hs0 M
  have hinvA : (1 - A)⁻¹ = ∑' k : ℕ, A ^ k := neumann_series_inv A hB
  have hunit : IsUnit ((1 : Matrix n n ℝ) - A).det :=
    (Matrix.isUnit_iff_isUnit_det (1 - A)).mp (Units.oneSub A hB).isUnit
  have hR : (s • ((1 : Matrix n n ℝ) - A)) * (s⁻¹ • (1 - A)⁻¹) = 1 := by
    rw [smul_mul_smul_comm, Matrix.mul_nonsing_inv _ hunit]
    rw [mul_inv_cancel₀ hs0, one_smul]
  rw [hM, Matrix.inv_eq_right_inv hR, hinvA]

open Unitary

lemma neumannSplit_smul_eq_conj {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M.IsHermitian) {s : ℝ} (hs : s ≠ 0) :
    s⁻¹ • neumannSplit s M =
      conjStarAlgAut ℝ (Matrix n n ℝ) hM.eigenvectorUnitary
        (Matrix.diagonal fun i : n => (1 : ℝ) - s⁻¹ * hM.eigenvalues i) := by
  have h1 : conjStarAlgAut ℝ (Matrix n n ℝ) hM.eigenvectorUnitary (1 : Matrix n n ℝ) = 1 :=
    map_one _
  rw [neumannSplit, smul_sub, smul_smul, inv_mul_cancel₀ hs, one_smul]
  conv_lhs => rw [hM.spectral_theorem]
  rw [← map_smul (conjStarAlgAut ℝ (Matrix n n ℝ) hM.eigenvectorUnitary)]
  rw [← h1, ← map_sub]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [hij]

/-- Every positive-definite matrix admits a splitting whose scaled
ℓ² operator norm is strictly less than one. -/
theorem exists_neumannSplit_series_of_posDef {n : Type*} [Fintype n]
    [DecidableEq n] {M : Matrix n n ℝ} (hM : M.PosDef) :
    ∃ s : ℝ, 0 < s ∧ ‖s⁻¹ • neumannSplit s M‖ < 1 ∧
      M⁻¹ = s⁻¹ • ∑' k : ℕ, (s⁻¹ • neumannSplit s M) ^ k := by
  classical
  let s : ℝ := (∑ i : n, |hM.1.eigenvalues i|) + 1
  have hs : 0 < s := by
    have : 0 ≤ ∑ i : n, |hM.1.eigenvalues i| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hposEig : ∀ i : n, 0 < hM.1.eigenvalues i := fun i => hM.eigenvalues_pos i
  have hEig : ∀ i : n, |hM.1.eigenvalues i| < s := by
    intro i
    have hi : |hM.1.eigenvalues i| ≤ ∑ j : n, |hM.1.eigenvalues j| :=
      Finset.single_le_sum (f := fun j : n => |hM.1.eigenvalues j|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    linarith
  have hform := neumannSplit_smul_eq_conj hM.1 hs.ne'
  set_option backward.isDefEq.respectTransparency false in
  have hcontr : ‖s⁻¹ • neumannSplit s M‖ < 1 := by
    rw [hform]
    simp only [conjStarAlgAut_apply, ← Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
      l2_opNorm_diagonal]
    refine (pi_norm_lt_iff (by positivity : (0 : ℝ) < 1)).mpr fun i => ?_
    have hpos : 0 < hM.1.eigenvalues i := hposEig i
    have hlt : hM.1.eigenvalues i < s := (abs_lt.mp (hEig i)).2
    have hfrac : 0 < s⁻¹ * hM.1.eigenvalues i :=
      mul_pos (inv_pos.mpr hs) hpos
    have hfrac1 : s⁻¹ * hM.1.eigenvalues i < 1 := by
      rw [mul_comm, ← div_eq_mul_inv, div_lt_one hs]
      exact hlt
    change |1 - s⁻¹ * hM.1.eigenvalues i| < 1
    have : |1 - s⁻¹ * hM.1.eigenvalues i| = 1 - s⁻¹ * hM.1.eigenvalues i :=
      abs_of_nonneg (sub_nonneg.mpr hfrac1.le)
    rw [this]
    linarith [hfrac]
  refine ⟨s, hs, hcontr, neumannSplit_inv_eq_tsum s hs M hcontr⟩

/-- Certified 1×1 Neumann series: A = 1/2, both sides equal 2. -/
theorem neumann_series_inv_half :
    let A : Matrix (Fin 1) (Fin 1) ℝ := !![1 / 2]
    (1 - A)⁻¹ = ∑' k : ℕ, A ^ k ∧ (1 - A)⁻¹ = !![2] := by
  intro A
  have hA : ‖A‖ < 1 := by
    have hAeq : A = Matrix.diagonal fun _ : Fin 1 => (1 / 2 : ℝ) := by
      ext i j
      fin_cases i; fin_cases j
      simp [A]
    rw [hAeq, l2_opNorm_diagonal]
    refine (pi_norm_lt_iff (by positivity : (0 : ℝ) < 1)).mpr fun i => ?_
    simp
    norm_num
  refine ⟨neumann_series_inv A hA, ?_⟩
  have h1A : (1 : Matrix (Fin 1) (Fin 1) ℝ) - A = !![1 / 2] := by
    ext i j
    fin_cases i; fin_cases j
    simp [A]
    norm_num
  rw [h1A, Matrix.inv_def, Matrix.adjugate_fin_one]
  ext i j
  fin_cases i; fin_cases j
  simp

end NystromSubmodularity
