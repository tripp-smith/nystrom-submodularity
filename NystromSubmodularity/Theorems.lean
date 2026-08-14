import NystromSubmodularity.Stieltjes
import NystromSubmodularity.InverseTrace
import NystromSubmodularity.Minimality
import NystromSubmodularity.Counterexamples.SDDDim3
import NystromSubmodularity.Counterexamples.SDDDim4
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Data.Rat.Cast.Order

/-!
# Main theorems

The Nyström nuclear error \(\mathcal{E}(S)=\operatorname{tr}(M[S^{\mathsf{c}}]^{-1})\)
has diminishing returns (is **supermodular**) when \(M=L+\gamma I\) for an SDDM
matrix \(L\). The same inequality fails for some SDD matrices already at
\(n=3\), including strictly diagonally dominant ones; dimension three is
minimal (Colbrook Proposition 5.5). With a nonempty selected base, dimension
four is minimal (Colbrook (28)–(29)).

The four-point algebra is in `InverseTrace.lean`. Minimality of the
obstruction is in `Minimality.lean`. A non-technical account is in
`FINDINGS.md`.
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

end NystromSubmodularity
