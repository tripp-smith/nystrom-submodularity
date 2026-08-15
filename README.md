# nystrom-submodularity

Lean 4 / mathlib4 formalization of Simons workshop [Problem 4.6](https://arxiv.org/abs/2607.19282)
(Colbrook, *Nyström Error Beyond M-Matrices*).

**Start here if you are not a mathematician:** [FINDINGS.md](FINDINGS.md) explains
what was proved, why the sign pattern of a precision matrix matters for greedy
landmark selection, and what is still open.

## Sign convention

Diminishing returns \(\Delta_{\mathcal{E}}(A;i,j)\ge 0\) is **supermodularity** of
the error \(\mathcal{E}\) (equivalently, submodularity of the gain
\(G(S)=\mathcal{E}(\emptyset)-\mathcal{E}(S)\)). The workshop report calls the same
inequality “submodularity of the error”. Theorems in this library use the
Wikipedia names.

## Schur reduction (Colbrook Theorem 2)

For symmetric positive-definite \(M=L+\gamma I\), after permuting \(S\) before \(S^{\mathsf{c}}\),

\[
K-\mathcal{N}_S(K)=\begin{pmatrix}0&0\\0&M[S^{\mathsf{c}}]^{-1}\end{pmatrix},
\qquad
\mathcal{E}(S)=\operatorname{tr}(M[S^{\mathsf{c}}]^{-1}),
\]

with the empty-matrix convention \(\operatorname{tr}(M[\emptyset]^{-1})=0\).
This block identity is `nystromResidual_eq_padded_compl_inv`. The residual is
PSD, so its nuclear (Schatten-1) norm equals its trace and
`nuclearNystromError_eq_nystromError`. We identify the nuclear norm with that
trace on this residual; there is no general SVD API.

## Status

**Small-instance checks.** Exact \(\mathbb{Q}\) checker (`cramerTraceInv`); path/cycle
SDDM instances on \(n=3,4,5\) with exhaustive four-point checks; Colbrook’s
signed triangle \(L_0\) with certified values
\(\mathcal{E}(\emptyset)=47/51\), \(\mathcal{E}(\{0\})=\mathcal{E}(\{1\})=9/16\),
\(\mathcal{E}(\{0,1\})=1/5\), hence \(\Delta=-7/2040<0\). The exhaustive
\(n\le 5\) pair checks use `native_decide`. The \(3\times 3\) SDD witness itself
is kernel `norm_num` / Cramer traces.

**SDD obstruction.** `not_nystromError_supermodular_of_isSDD`: there exist \(n\),
SDD PD \(L\), and \(\gamma>0\) such that \(\mathcal{E}\) is not supermodular.
The same failure occurs under *strict* diagonal dominance
(`not_nystromError_supermodular_of_isStrictSDD`, Colbrook’s \(L^\sharp\)).
The one-parameter family \(L(t)\) is SDD and positive definite for every
\(t>0\), and \(\mathcal{E}_t\) is not supermodular if and only if
\(\varphi<t<1+\sqrt{2}\) (`Lfam_not_supermodular_iff`, Colbrook Theorem 10
complete). The empty-base pairs involving index \(2\) have positive defect;
a nonempty base cannot fail at \(n=3\).
On that interval greedy one-column selection picks index \(2\), which lies
in no optimal pair (`Lfam_greedy_misses_optimal_pair`); the pair-error
ratio is \((2t+1)/(t+2)\) (\(5/4\) at \(t=2\)). The same misselection
occurs for \(L^\sharp\) (`Lsharp_greedy_misses_optimal_pair`: residual
\(1/5\) versus optimum \(1/6\)).

**Signature switching.** `nystromError_supermodular_of_signature_stieltjes`
(Colbrook Proposition 7): a \(\{\pm 1\}\) diagonal congruence that produces
a Stieltjes matrix implies supermodularity of \(\mathcal{E}\). On a fully
supported triangle this happens for every positive-definite realization if
and only if the sign pattern is antibalanced
(`triangle_pd_nystrom_supermodular_iff_antibalanced`, Corollary 13).
Flipping the sign of index \(2\) on a path Laplacian stays supermodular;
the \(L^\sharp\) pattern (signs \(+,-,-\), product \(+1\)) is not
antibalanced.

**Minimality.** `nystromError_supermodular_of_card_le_two_posDef`: every
positive-definite precision matrix on at most two indices has supermodular
Nyström error, so dimension three is minimal. If the base set is nonempty and
\(n\le 3\), the four-point defect cannot be negative
(`nystromError_fourPoint_nonempty_of_card_le_three`). Dimension four is sharp:
Colbrook’s strictly SDD \(L_4\) with complete support fails at \(A=\{3\}\),
\(\Delta=-7/20400\) (`exists_nystromError_fourPoint_neg_of_isStrictSDD_nonempty`).

**SDDM theorem.** `nystromError_supermodular_of_isSDDM`:
`IsSDDM L` and `0 < γ` imply supermodularity of \(\mathcal{E}\) for \(M=L+\gamma I\).
The argument is Stieltjes inverse-nonnegativity plus the Atamtürk–Gómez
four-point identity (`InverseTrace.lean`).

**Schur residual and exact marginal.** `nystromResidual_eq_padded_compl_inv`
is Colbrook Theorem 2. `exact_marginal` is Lemma 3 for every
positive-definite precision matrix, so \(\mathcal{E}\) is strictly
decreasing (`nystromError_strict_anti_monotone`). Scaling \(M\) by
\(\alpha\neq 0\) multiplies every inverse-trace by \(\alpha^{-1}\)
(`nystromError_smul_scale`). On \(M_0\), the nuclear error at \(\{0\}\)
is the certified Cramer value \(9/16\); the traces of \(10\cdot M_0\)
are one-tenth of those of \(M_0\).

Both public theorems print the Lean defaults (`propext`, `Classical.choice`,
`Quot.sound`).

**Not in scope.** SVD nuclear-norm API, Neumann series, other losses, or
the true singular case \(\gamma=0\).

Build: `lake build`. No `sorry` in the library target.

## Modules

| File | Role |
|------|------|
| `Definitions.lean` | `Submodular` / `Supermodular`, SDDM/SDD/Stieltjes predicates |
| `PrincipalSubmatrix.lean` | `traceInv`, `nystromError`, insert₁/insert₂ block identifications |
| `Computable.lean` | exact \(\mathbb{Q}\) Cramer traces |
| `Nystrom.lean` | Nyström residual identity; nuclear error equals inverse-trace |
| `Stieltjes.lean` | inverse-nonnegativity; SDDM + \(\gamma I\) is Stieltjes |
| `InverseTrace.lean` | four-point identity; exact marginal for every PD matrix |
| `Minimality.lean` | terminal \(2\times 2\) identity; \(n\le 2\) never fails |
| `SmallInstanceChecks.lean` | exhaustive \(n\le 5\) SDDM checks |
| `Counterexamples/SDDDim3.lean` | signed triangle \(L_0\) and strictly SDD \(L^\sharp\) |
| `Counterexamples/SDDDim4.lean` | nonempty-base strictly SDD \(L_4\) |
| `Counterexamples/SDDFamily.lean` | signed-triangle family \(L(t)\) and sharp interval |
| `Counterexamples/Greedy.lean` | greedy one-column misselection on \(L(t)\) and \(L^\sharp\) |
| `Signature.lean` | signature congruence, antibalance, order-3 Corollary 13 |
| `Theorems.lean` | public theorems: SDDM supermodularity and SDD obstruction |
