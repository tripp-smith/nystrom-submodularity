import NystromSubmodularity.Stieltjes
import NystromSubmodularity.InverseTrace
import NystromSubmodularity.Nystrom
import NystromSubmodularity.Minimality
import NystromSubmodularity.Counterexamples.SDDDim3
import NystromSubmodularity.Counterexamples.SDDDim4
import NystromSubmodularity.Counterexamples.SDDFamily
import NystromSubmodularity.Counterexamples.Greedy
import NystromSubmodularity.Signature
import NystromSubmodularity.OtherLosses
import NystromSubmodularity.Census
import NystromSubmodularity.Singular
import NystromSubmodularity.NuclearNormSVD
import NystromSubmodularity.Schur
import NystromSubmodularity.Neumann
import NystromSubmodularity.Perturbation
import NystromSubmodularity.ApproxSubmodular
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Fintype.Card
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Main theorems

The Nyström nuclear error \(\mathcal{E}(S)=\operatorname{tr}(M[S^{\mathsf{c}}]^{-1})\)
has diminishing returns (is **supermodular**) when \(M=L+\gamma I\) for an SDDM
matrix \(L\). The same inequality fails for some SDD matrices already at
\(n=3\), including strictly diagonally dominant ones; dimension three is
minimal (Colbrook Proposition 5.5). With a nonempty selected base, dimension
four is minimal (Colbrook (28)–(29)). The signed-triangle family \(L(t)\)
fails to be supermodular if and only if
\(\varphi<t<1+\sqrt{2}\) (Colbrook Theorem 10). A \(\{\pm 1\}\) signature
that produces a Stieltjes matrix is enough for supermodularity (Proposition
7); on a fully supported triangle this holds for every positive-definite
realization if and only if the sign pattern is antibalanced (Corollary 13).
Colbrook Theorem 2 identifies the Nyström residual with a padded complement
inverse, so the nuclear error equals the inverse-trace on that PSD residual.
The exact one-index increment (Lemma 3) holds for every positive-definite
precision matrix, \(\mathcal{E}\) is strictly decreasing, and scaling \(M\)
by \(\alpha\neq 0\) multiplies every inverse-trace by \(\alpha^{-1}\).

The four-point algebra is in `InverseTrace.lean`. Minimality of the
obstruction is in `Minimality.lean`. Greedy one-column misselection on
\(L(t)\) and \(L^\sharp\) is in `Counterexamples/Greedy.lean`. Signature
switching and the order-3 antibalance criterion are in `Signature.lean`.
The residual identity is in `Nystrom.lean`. The approximate
supermodularity ratio and entry-\(\ell^1\) Lipschitz bound are in
`ApproxSubmodular.lean`. A non-technical account is in `FINDINGS.md`.
The specification in `SPEC.md` is complete.
-/

namespace NystromSubmodularity

open Matrix Counterexamples

/-- There exist an SDD positive-definite matrix and a positive shift for which
the Nyström nuclear error is **not** supermodular. Witness: Colbrook's
\(3\times 3\) signed triangle \(L_0\) at \(\gamma=1\), with
\(\Delta(\emptyset;0,1)=-7/2040\). -/
theorem not_nystromError_supermodular_of_isSDD :
    ∃ (n : ℕ) (L : Matrix (Fin n) (Fin n) ℝ) (γ : ℝ),
      IsSDD L ∧ L.PosDef ∧ 0 < γ ∧
        ¬ Supermodular (nystromError (L + γ • (1 : Matrix (Fin n) (Fin n) ℝ))) := by
  refine ⟨3, toReal L0, 1, L0_toReal_isSDD, L0_posDef, by norm_num, ?_⟩
  convert not_supermodular_nystromError_M0
  rw [M0_toReal_eq, one_smul]

/-- Failure persists under strict diagonal dominance (Colbrook Proposition 4.5). -/
theorem not_nystromError_supermodular_of_isStrictSDD :
    ∃ (n : ℕ) (L : Matrix (Fin n) (Fin n) ℝ) (γ : ℝ),
      IsStrictSDD L ∧ L.PosDef ∧ 0 < γ ∧
        ¬ Supermodular (nystromError (L + γ • (1 : Matrix (Fin n) (Fin n) ℝ))) := by
  refine ⟨3, toReal Lsharp, 1, Lsharp_toReal_isStrictSDD, Lsharp_posDef, by norm_num, ?_⟩
  convert not_supermodular_nystromError_Msharp
  rw [Msharp_toReal_eq, one_smul]

theorem nystromError_supermodular_of_isStieltjes {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : IsStieltjes A) :
    Supermodular (nystromError A) :=
  supermodular_compl (traceInv_supermodular_of_isStieltjes hA)

/-- Nyström nuclear error is supermodular for SDDM precision matrices. -/
theorem nystromError_supermodular_of_isSDDM {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Matrix ι ι ℝ} {γ : ℝ} (hL : IsSDDM L) (hγ : 0 < γ) :
    Supermodular (nystromError (L + γ • (1 : Matrix ι ι ℝ))) :=
  nystromError_supermodular_of_isStieltjes (hL.add_pos_smul_one_isStieltjes hγ)

/-- Dimension at most two never fails, even without an SDD or sign hypothesis. -/
theorem nystromError_supermodular_of_card_le_two_posDef {ι : Type*} [Fintype ι]
    [DecidableEq ι] {M : Matrix ι ι ℝ} (hM : M.PosDef) (hcard : Fintype.card ι ≤ 2) :
    Supermodular (nystromError M) :=
  nystromError_supermodular_of_card_le_two hM hcard

/-- Colbrook (28)–(29): with a nonempty selected base, dimension four is
minimal even under strict diagonal dominance and complete support. -/
theorem exists_nystromError_fourPoint_neg_of_isStrictSDD_nonempty :
    ∃ (n : ℕ) (L : Matrix (Fin n) (Fin n) ℝ) (γ : ℝ)
      (A : Finset (Fin n)) (i j : Fin n),
      IsStrictSDD L ∧ L.PosDef ∧ 0 < γ ∧ A.Nonempty ∧
        i ≠ j ∧ i ∉ A ∧ j ∉ A ∧
        (∀ a b : Fin n, a ≠ b → L a b ≠ 0) ∧
        nystromError (L + γ • (1 : Matrix (Fin n) (Fin n) ℝ)) A +
            nystromError (L + γ • (1 : Matrix (Fin n) (Fin n) ℝ))
              (insert j (insert i A)) <
          nystromError (L + γ • (1 : Matrix (Fin n) (Fin n) ℝ)) (insert i A) +
            nystromError (L + γ • (1 : Matrix (Fin n) (Fin n) ℝ)) (insert j A) := by
  refine ⟨4, toReal L4, 1, {3}, 0, 1, L4_toReal_isStrictSDD, L4_posDef, by norm_num,
    Finset.singleton_nonempty _, by decide, by decide, by decide, ?_, ?_⟩
  · intro a b hab
    rw [toReal_apply]
    exact (Rat.cast_ne_zero (α := ℝ)).mpr (L4_complete_support hab)
  · rw [one_smul, ← M4_toReal_eq]
    have h013 : ({1, 0, 3} : Finset (Fin 4)) = ({0, 1, 3} : Finset (Fin 4)) := by decide
    rw [h013]
    exact M4_delta_neg_real

/-- Colbrook Theorem 10: for \(t>0\), the empty-base \((0,1)\) defect of
\(L(t)\) is negative if and only if \(\varphi<t<1+\sqrt{2}\). -/
theorem Lfam_fourPoint_neg_iff {t : ℝ} (ht : 0 < t) :
    nystromError (Lfam t + 1) (∅ : Finset (Fin 3)) +
        nystromError (Lfam t + 1) ({0, 1} : Finset (Fin 3)) <
      nystromError (Lfam t + 1) ({0} : Finset (Fin 3)) +
        nystromError (Lfam t + 1) ({1} : Finset (Fin 3)) ↔
      Real.goldenRatio < t ∧ t < 1 + √2 := by
  simpa [Lfam_eq_Mfam_sub_one t, cramerNystromError_eq_nystromError] using
    Mfam_delta_neg_iff ht

/-- Every parameter in the open Colbrook interval yields an SDD
positive-definite obstruction. -/
theorem not_nystromError_supermodular_of_Lfam {t : ℝ}
    (hφ : Real.goldenRatio < t) (hsil : t < 1 + √2) :
    IsSDD (Lfam t) ∧ (Lfam t).PosDef ∧
      ¬ Supermodular (nystromError (Lfam t + (1 : Matrix (Fin 3) (Fin 3) ℝ))) := by
  have ht : 0 < t := lt_trans Real.goldenRatio_pos hφ
  refine ⟨Lfam_isSDD ht.le, Lfam_posDef ht, ?_⟩
  convert not_supermodular_nystromError_Mfam ht hφ hsil
  exact (Lfam_eq_Mfam_sub_one t).symm

/-- Colbrook Theorem 10 (complete): \(\mathcal{E}_t\) is not supermodular
if and only if \(\varphi<t<1+\sqrt{2}\). Nonempty bases cannot fail at
\(n=3\), and the empty-base pairs involving index \(2\) have positive
defect. -/
theorem Lfam_not_supermodular_iff {t : ℝ} (ht : 0 < t) :
    ¬ Supermodular (nystromError (Lfam t + 1)) ↔
      Real.goldenRatio < t ∧ t < 1 + √2 := by
  have hLM : Lfam t + 1 = Mfam t := (Lfam_eq_Mfam_sub_one t).symm
  constructor
  · intro hns
    rw [hLM] at hns
    have hnotfp : ¬ FourPointSupermodular (nystromError (Mfam t)) :=
      mt supermodular_of_fourPointSupermodular hns
    unfold FourPointSupermodular at hnotfp
    push Not at hnotfp
    obtain ⟨A, i, j, hij, hi, hj, hlt⟩ := hnotfp
    by_cases hA : A.Nonempty
    · have hge :=
        nystromError_fourPoint_nonempty_of_card_le_three (M := Mfam t)
          (Mfam_posDef ht) (by simp [Fintype.card_fin]) hA hij hi hj
      linarith
    · have hAempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
      subst hAempty
      have h01 : ({1, 0} : Finset (Fin 3)) = {0, 1} := by decide
      have h02 : ({2, 0} : Finset (Fin 3)) = {0, 2} := by decide
      have h12 : ({2, 1} : Finset (Fin 3)) = {1, 2} := by decide
      fin_cases i <;> fin_cases j
      · exact (hij rfl).elim
      · refine (Mfam_empty_zero_one_neg_iff ht).mp ?_
        simpa [h01] using hlt
      · have hpos := Mfam_delta_zero_two_pos_real ht
        simp [h02] at hlt
        linarith
      · refine (Mfam_empty_zero_one_neg_iff ht).mp ?_
        have hlt' := hlt
        simp at hlt'
        linarith [hlt']
      · exact (hij rfl).elim
      · have hpos := Mfam_delta_one_two_pos_real ht
        simp [h12] at hlt
        linarith
      · have hpos := Mfam_delta_zero_two_pos_real ht
        simp at hlt
        linarith
      · have hpos := Mfam_delta_one_two_pos_real ht
        simp at hlt
        linarith
      · exact (hij rfl).elim
  · intro ⟨hφ, hsil⟩
    rw [hLM]
    exact not_supermodular_nystromError_Mfam ht hφ hsil

/-- Colbrook (31)–(33): on the failure interval, greedy one-column
selection on \(L(t)\) picks index \(2\), which lies in no optimal pair. -/
theorem Lfam_greedy_misses_optimal_pair {t : ℝ}
    (hφ : Real.goldenRatio < t) (hsil : t < 1 + √2) :
    (∀ i : Fin 3, i ≠ 2 →
      nystromError (Lfam t + 1) ({2} : Finset (Fin 3)) <
        nystromError (Lfam t + 1) {i}) ∧
    (∀ s : Finset (Fin 3), s.card = 2 → s ≠ {0, 1} →
      nystromError (Lfam t + 1) ({0, 1} : Finset (Fin 3)) <
        nystromError (Lfam t + 1) s) ∧
    nystromError (Lfam t + 1) ({0, 2} : Finset (Fin 3)) /
        nystromError (Lfam t + 1) ({0, 1} : Finset (Fin 3)) =
      (2 * t + 1) / (t + 2) :=
  Counterexamples.Lfam_greedy_misses_optimal_pair hφ hsil

/-- The same greedy misselection on the strictly SDD witness \(L^\sharp\). -/
theorem Lsharp_greedy_misses_optimal_pair :
    nystromError (toReal Msharp) ({2} : Finset (Fin 3)) = ((5 / 12 : ℚ) : ℝ) ∧
    nystromError (toReal Msharp) ({0} : Finset (Fin 3)) = ((11 / 26 : ℚ) : ℝ) ∧
    ((5 / 12 : ℚ) : ℝ) < ((11 / 26 : ℚ) : ℝ) ∧
    nystromError (toReal Msharp) ({0, 1} : Finset (Fin 3)) = ((1 / 6 : ℚ) : ℝ) ∧
    nystromError (toReal Msharp) ({0, 2} : Finset (Fin 3)) = ((1 / 5 : ℚ) : ℝ) ∧
    ((1 / 6 : ℚ) : ℝ) < ((1 / 5 : ℚ) : ℝ) :=
  Counterexamples.Lsharp_greedy_misses_optimal_pair

/-! Colbrook Proposition 7, Proposition 8 (\(n=3\)), and Corollary 13 are
`nystromError_supermodular_of_signature_stieltjes`,
`exists_signature_stieltjes_of_antibalanced_triangle`, and
`triangle_pd_nystrom_supermodular_iff_antibalanced` in `Signature.lean`.
Sanity: `pathM3_signature_flip_supermodular`, `Lsharp_not_antibalanced_pattern`.

Colbrook Theorem 2, Lemma 3, and (30) are
`nystromResidual_eq_padded_compl_inv`, `nuclearNystromError_eq_nystromError`
in `Nystrom.lean`, `exact_marginal` and `nystromError_strict_anti_monotone`
in `InverseTrace.lean`, and `nystromError_smul_scale` in `Computable.lean`.

Remaining research: `OtherLosses.lean`, `Census.lean`, `Singular.lean`,
`NuclearNormSVD.lean`, `Schur.lean`, `Neumann.lean`, `Perturbation.lean`,
`ApproxSubmodular.lean`, and `MATHLIB.md`. See `RESEARCH.md`.

The general approximate-supermodularity ratio is
`supermodularityRatio`; Stieltjes pairs have ratio at least one
(`one_le_supermodularityRatio_of_isStieltjes`). An arbitrary
positive-definite perturbation moves each Nyström value by at most
`nystromLipschitzBound` (`abs_nystromError_sub_le`) and the four-point
defect by at most `fourPointLipschitzBound`. On \(M_0\) the empty-base
\((0,1)\) ratio is \(2288/2295\).

Singular values of a real (including rectangular) matrix are
`matrixSingularValues`; `schattenOne` is their sum. On a Hermitian
matrix that sum equals the Hermitian nuclear norm
(`sum_matrixSingularValues_eq_hermitianNuclearNorm`), so Nyström
error is a singular-value sum of the complementary inverse.
Block-diagonal Hermitian nuclear mass adds
(`hermitianNuclearNorm_fromBlocks_diagonal`). The infinite Neumann
series equals the inverse whenever the \(\ell^2\) operator norm is
less than one (`neumann_series_inv`); every positive-definite matrix
admits such a splitting (`exists_neumannSplit_series_of_posDef`). -/

/-- Forces the residual identity, not only the inverse-trace definition:
the nuclear error of \(M_0\) at \(\{0\}\) is the certified Cramer value. -/
theorem nuclearNystromError_M0_zero :
    nuclearNystromError (toReal M0) ({0} : Finset (Fin 3)) = ((9 / 16 : ℚ) : ℝ) := by
  rw [nuclearNystromError_eq_nystromError M0_posDef, ← toReal_nystromError, M0_cramer_zero]

/-- Colbrook (30) on \(M_0\): scaling by \(10\) multiplies every inverse-trace
by \(1/10\). -/
theorem nystromError_ten_smul_M0 (S : Finset (Fin 3)) :
    nystromError ((10 : ℝ) • toReal M0) S =
      (10 : ℝ)⁻¹ * nystromError (toReal M0) S :=
  nystromError_smul_scale (10 : ℝ) (toReal M0) S (by norm_num)

theorem nystromError_ten_smul_M0_zero :
    nystromError ((10 : ℝ) • toReal M0) ({0} : Finset (Fin 3)) =
      ((9 / 160 : ℚ) : ℝ) := by
  rw [nystromError_ten_smul_M0, ← toReal_nystromError, M0_cramer_zero]
  norm_num

/-- On Colbrook’s \(M_0\), the empty-base \((0,1)\) approximate
supermodularity ratio is the certified rational \(2288/2295<1\). -/
theorem M0_supermodularityRatio :
    supermodularityRatio (toReal M0) (∅ : Finset (Fin 3)) 0 1 =
      (2288 / 2295 : ℝ) ∧
        supermodularityRatio (toReal M0) (∅ : Finset (Fin 3)) 0 1 < 1 ∧
          fourPointDefect (toReal M0) (∅ : Finset (Fin 3)) 0 1 =
            ((-7 / 2040 : ℚ) : ℝ) :=
  ⟨M0_supermodularityRatio_empty_zero_one, M0_supermodularityRatio_lt_one,
    M0_fourPointDefect_eq_ratio_form⟩

open scoped Matrix.Norms.L2Operator

/-- On a Hermitian matrix the singular-value sum equals \(\sum_i|\lambda_i|\). -/
theorem sum_singularValues_eq_hermitianNuclearNorm {n : Type*} [Fintype n]
    [DecidableEq n] {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    ∑ i ∈ Finset.range (Fintype.card n), matrixSingularValues A i =
      hermitianNuclearNorm A hA :=
  sum_matrixSingularValues_eq_hermitianNuclearNorm hA

/-- Nyström error is the singular-value sum of the complementary inverse. -/
theorem nystromError_eq_sum_singularValues_compl {ι : Type*} [Fintype ι]
    [DecidableEq ι] {M : Matrix ι ι ℝ} (hM : M.PosDef) (S : Finset ι) :
    nystromError M S =
      ∑ i ∈ Finset.range (Fintype.card (PrincipalIndex (compl S))),
        matrixSingularValues (principalSubmatrix M (compl S))⁻¹ i :=
  nystromError_eq_sum_matrixSingularValues_compl hM S

/-- If \(\|A\|_2<1\), then \((I-A)^{-1}=\sum_k A^k\). -/
theorem neumann_series_eq_inv {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : ‖A‖ < 1) :
    (1 - A)⁻¹ = ∑' k : ℕ, A ^ k :=
  neumann_series_inv A hA

/-- Every positive-definite matrix admits a Neumann splitting. -/
theorem exists_neumann_series_of_posDef {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℝ} (hM : M.PosDef) :
    ∃ s : ℝ, 0 < s ∧ ‖s⁻¹ • neumannSplit s M‖ < 1 ∧
      M⁻¹ = s⁻¹ • ∑' k : ℕ, (s⁻¹ • neumannSplit s M) ^ k :=
  exists_neumannSplit_series_of_posDef hM

/-- Certified \(1\times 1\) check: \(A=1/2\), both sides equal \(2\). -/
theorem neumann_series_half :
    let A : Matrix (Fin 1) (Fin 1) ℝ := !![1 / 2]
    (1 - A)⁻¹ = ∑' k : ℕ, A ^ k ∧ (1 - A)⁻¹ = !![2] :=
  neumann_series_inv_half

/-- The Schatten-1 norm of a \(1\times 1\) matrix is the absolute value. -/
theorem schattenOne_abs_of_fin_one (a : ℝ) :
    schattenOne (!![a] : Matrix (Fin 1) (Fin 1) ℝ) = |a| :=
  schattenOne_fin_one a

/-- Certified \(1\times 1\) Schatten-1 check: \(\operatorname{schattenOne}\,[\![-3]\!]=3\). -/
theorem schattenOne_neg_three_check :
    schattenOne (!![-3] : Matrix (Fin 1) (Fin 1) ℝ) = 3 :=
  schattenOne_neg_three

/-- Block-diagonal Hermitian nuclear mass adds. -/
theorem hermitianNuclearNorm_blockDiag {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {A : Matrix m m ℝ} {D : Matrix n n ℝ}
    (hA : A.IsHermitian) (hD : D.IsHermitian) :
    hermitianNuclearNorm (fromBlocks A (0 : Matrix m n ℝ) 0 D)
      (isHermitian_fromBlocks_diagonal hA hD) =
      hermitianNuclearNorm A hA + hermitianNuclearNorm D hD :=
  hermitianNuclearNorm_fromBlocks_diagonal hA hD

/-- Certified block-diagonal Schatten-1 check: \(\operatorname{diag}(2,3)\) has mass \(5\). -/
theorem schattenOne_diag_two_three :
    schattenOne
      (fromBlocks (!![2] : Matrix (Fin 1) (Fin 1) ℝ) 0 0
        (!![3] : Matrix (Fin 1) (Fin 1) ℝ)) = 5 :=
  schattenOne_fromBlocks_two_three

end NystromSubmodularity
