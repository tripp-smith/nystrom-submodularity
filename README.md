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
`nystromError M S` is this inverse-trace formula. `nuclearNorm` is currently this
trace, not an SVD sum; that is enough for the PSD residual of a positive-definite
precision matrix.

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

**Minimality.** `nystromError_supermodular_of_card_le_two_posDef`: every
positive-definite precision matrix on at most two indices has supermodular
Nyström error, so dimension three is minimal. If the base set is nonempty and
\(n\le 3\), the four-point defect cannot be negative
(`nystromError_fourPoint_nonempty_of_card_le_three`).

**SDDM theorem.** `nystromError_supermodular_of_isSDDM`:
`IsSDDM L` and `0 < γ` imply supermodularity of \(\mathcal{E}\) for \(M=L+\gamma I\).
The argument is Stieltjes inverse-nonnegativity plus the Atamtürk–Gómez
four-point identity (`InverseTrace.lean`).

Both public theorems print the Lean defaults (`propext`, `Classical.choice`,
`Quot.sound`).

**Not in scope.** Full Schur residual identity, SVD nuclear-norm API, Neumann
series, signature switching, or a nonempty-base \(n=4\) witness.

Build: `lake build`. No `sorry` in the library target.

## Modules

| File | Role |
|------|------|
| `Definitions.lean` | `Submodular` / `Supermodular`, SDDM/SDD/Stieltjes predicates |
| `PrincipalSubmatrix.lean` | `traceInv`, `nystromError`, insert₁/insert₂ block identifications |
| `Computable.lean` | exact \(\mathbb{Q}\) Cramer traces |
| `Nystrom.lean` | Nyström approximation/residual (trace nuclear norm) |
| `Stieltjes.lean` | inverse-nonnegativity; SDDM + \(\gamma I\) is Stieltjes |
| `InverseTrace.lean` | four-point identity for \(T\mapsto\operatorname{tr}(A[T]^{-1})\) |
| `Minimality.lean` | terminal \(2\times 2\) identity; \(n\le 2\) never fails |
| `SmallInstanceChecks.lean` | exhaustive \(n\le 5\) SDDM checks |
| `Counterexamples/SDDDim3.lean` | signed triangle \(L_0\) and strictly SDD \(L^\sharp\) |
| `Theorems.lean` | public theorems: SDDM supermodularity and SDD obstruction |
