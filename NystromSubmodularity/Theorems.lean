import NystromSubmodularity.Stieltjes
import NystromSubmodularity.InverseTrace
import NystromSubmodularity.Counterexamples.SDDDim3
import Mathlib.Tactic.NormNum

/-!
# Main theorems

The Nyström nuclear error \(\mathcal{E}(S)=\operatorname{tr}(M[S^{\mathsf{c}}]^{-1})\)
has diminishing returns (is **supermodular**) when \(M=L+\gamma I\) for an SDDM
matrix \(L\). The same inequality fails for some SDD matrices; the witness is
Colbrook's \(3\times 3\) signed triangle.

The four-point algebra is in `InverseTrace.lean`. A non-technical account of
what this means, and what is still open, is in `FINDINGS.md`.

`#print axioms nystromError_supermodular_of_isSDDM` and
`#print axioms not_nystromError_supermodular_of_isSDD` are the Lean defaults
(`propext` / `Classical.choice` / `Quot.sound`).
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

theorem nystromError_supermodular_of_isStieltjes {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : IsStieltjes A) :
    Supermodular (nystromError A) :=
  supermodular_compl (traceInv_supermodular_of_isStieltjes hA)

/-- Nyström nuclear error is supermodular for SDDM precision matrices. -/
theorem nystromError_supermodular_of_isSDDM {ι : Type*} [Fintype ι] [DecidableEq ι]
    {L : Matrix ι ι ℝ} {γ : ℝ} (hL : IsSDDM L) (hγ : 0 < γ) :
    Supermodular (nystromError (L + γ • (1 : Matrix ι ι ℝ))) :=
  nystromError_supermodular_of_isStieltjes (hL.add_pos_smul_one_isStieltjes hγ)

end NystromSubmodularity
