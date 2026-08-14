# nystrom-submodularity

Lean 4 / mathlib4 formalization of Simons workshop [Problem 4.6](https://arxiv.org/abs/2607.19282)
(Colbrook, *Nyström Error Beyond M-Matrices*): supermodularity of the nuclear-norm
Nyström residual for SDDM precision matrices, and a \(3\times 3\) SDD obstruction.

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
`nystromError M S` is this inverse-trace formula (so Phase 1 never inverts \(K\)
or computes singular values).

## Status

**Phase 1 (landed).** Exact \(\mathbb{Q}\) checker (`cramerTraceInv`); path/cycle
SDDM instances on \(n=3,4,5\) with exhaustive four-point checks; Colbrook’s
signed triangle \(L_0\) with certified values
\(\mathcal{E}(\emptyset)=47/51\), \(\mathcal{E}(\{0\})=\mathcal{E}(\{1\})=9/16\),
\(\mathcal{E}(\{0,1\})=1/5\), hence \(\Delta=-7/2040<0\). These checks use
`native_decide` (compiler certificates), which is the intended Phase 1 tool.

**Phase 2, SDD (landed as a statement).** `not_nystromError_supermodular_of_isSDD`:
there exist \(n\), SDD PD \(L\), and \(\gamma>0\) such that \(\mathcal{E}\) is not
supermodular. The proof still inherits the `native_decide` Cramer traces of \(M_0\).

**Phase 2, SDDM (landed).** `nystromError_supermodular_of_isSDDM`:
`IsSDDM L` and `0 < γ` imply supermodularity of \(\mathcal{E}\) for \(M=L+\gamma I\).
The argument is Stieltjes inverse-nonnegativity plus the Atamtürk–Gómez
four-point identity on \(T\mapsto\operatorname{tr}(A[T]^{-1})\) (`InverseTrace.lean`).

**Not required to close Phase 1–2.** Full Schur residual identity
(`nystromResidual M⁻¹ S` equal to the padded inverse), SVD nuclear-norm API,
Neumann series, signature switching, or minimality of \(n=3\).

Build: `lake build`. No `sorry` in the library target.
