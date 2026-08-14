import NystromSubmodularity.Stieltjes
import NystromSubmodularity.InverseTrace
import NystromSubmodularity.Counterexamples.SDDDim3
import Mathlib.Tactic.NormNum

/-!
# Phase 2 — living blueprint

Problem 4.6 asks whether the Nyström nuclear error
\(\mathcal{E}(S)=\|K-\mathcal{N}_S(K)\|_*\) has diminishing returns
(\(\Delta_{\mathcal{E}}\ge 0\)). That is **supermodularity** of \(\mathcal{E}\)
in the standard combinatorial sense (workshop wording says “submodularity of
the error”).

**Reduction (Colbrook Theorem 2).** For PD \(M=L+\gamma I\),
\(\mathcal{E}(S)=\operatorname{tr}(M[S^{\mathsf{c}}]^{-1})\) (empty inverse-trace
is \(0\)). This is the working definition of `nystromError`.

**SDD (done).** An explicit rational \(3\times 3\) signed triangle \(L_0\)
with \(\gamma=1\) has \(\Delta=-7/2040<0\). Packaged as
`not_nystromError_supermodular_of_isSDD`.

**SDDM (done).** Colbrook Theorem 4: `IsSDDM L` and `0 < γ` imply
`IsStieltjes (L+γI)`. Stieltjes matrices have entrywise-nonnegative inverses
(block induction in `Stieltjes.lean`). The Atamtürk–Gómez four-point identity
in `InverseTrace.lean` then gives supermodularity of
\(T\mapsto\operatorname{tr}(A[T]^{-1})\) via the \(2\times 2\) Schur
complement `Q` and Gram `H = Cᵀ N⁻² C`. Complements yield
`nystromError_supermodular_of_isSDDM`.

`#print axioms nystromError_supermodular_of_isSDDM` is the Lean defaults
(`propext` / `Classical.choice` / `Quot.sound`). The SDD existence theorem
currently also depends on `native_decide` certificates for the rational Cramer
traces of `M0`. Replacing those with kernel `norm_num` proofs is a closing
item, not a blocker for the combinatorial SDDM statement.
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

end NystromSubmodularity
