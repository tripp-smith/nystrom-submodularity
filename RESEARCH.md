# Remaining research threads

The original [SPEC.md](SPEC.md) and Colbrook Theorem 1 are complete. This
note is the specification for the leftover threads recorded in
`FINDINGS.md`. Each thread has a Lean delivery, the same verification
cadence (`.cursor/skills/nystrom-phase/SKILL.md`: `lake build`, no
`sorry`, Lean-default axioms on public theorems), and a documentation
update.

Wikipedia supermodularity names are used throughout.

## Success criteria

| Thread | Delivery |
|--------|----------|
| 1 Other losses | Frobenius, operator-norm, and residual-quadratic (“prediction”) errors on \(M_0\); nuclear is not the only loss that fails |
| 2 Census | Finite certified counts: Colbrook-family rational grid; 64 integer strict-SDD triangles |
| 3 Singular \(\gamma=0\) | SDDM is PSD; unshifted path Laplacian is singular; Nyström error on proper complements is well-defined and the nonempty-base four-point stays nonnegative |
| 4 SVD / nuclear API | Hermitian nuclear norm \(\sum_i\|\lambda_i\|\) via mathlib eigenvalues; equals trace on PSD matrices |
| 5 Mathlib extraction | `MathlibReady.lean` + `MATHLIB.md` packaging the Stieltjes / four-point lemmas |
| 6 Neumann | Stieltjes splitting \(B=sI-M\ge 0\); length-1 modular and length-2 supermodular walk traces |
| 7 Perturbation | Explicit neighborhood of \(M_0\) keeps a negative defect; scale invariance already in the library |
| 8 Approx. ratio | Entry-\(\ell^1\) Lipschitz of \(\mathcal{E}\) and \(\Delta\); Stieltjes pairs have \(\gamma\ge 1\); \(M_0\) empty-base ratio \(2288/2295\) |

## Thread 8 — Approximate-supermodularity ratio

Phase cadence: `.cursor/skills/nystrom-phase/SKILL.md`.

The seven threads above include an explicit ridge neighborhood of \(M_0\)
and scale-invariance of the defect sign. They do **not** give a ratio
that applies to an arbitrary symmetric perturbation of a
positive-definite precision matrix. This thread does.

Wikipedia names: the four-point defect
\(\Delta(M;A,i,j)=\mathcal{E}(A)+\mathcal{E}(A\cup\{i,j\})-\mathcal{E}(A\cup\{i\})-\mathcal{E}(A\cup\{j\})\)
is nonnegative iff \(\mathcal{E}\) is supermodular on that pair. The
**approximate supermodularity ratio** of the pair is
\(\gamma=( \mathcal{E}(A)+\mathcal{E}(A\cup\{i,j\}) ) / ( \mathcal{E}(A\cup\{i\})+\mathcal{E}(A\cup\{j\}) )\)
when the denominator is positive, and \(1\) when it vanishes. Exact
supermodularity is \(\gamma\ge 1\). A perturbation is
\(\varepsilon\)-approximately supermodular when \(\Delta\ge -\varepsilon\).

| Name | Claim |
|------|--------|
| `fourPointDefect` | \(\Delta(M;A,i,j)\) |
| `supermodularityRatio` | \(\gamma(M;A,i,j)\) |
| `entryL1` | entrywise \(\ell^1\) mass \(\sum_{i,j}\|M_{ij}\|\) |
| `abs_nystromError_sub_le` | \(\|\mathcal{E}(M+E,S)-\mathcal{E}(M,S)\|\) bounded by inverse entry-\(\ell^1\) masses times `entryL1 E[Sᶜ]` |
| `abs_fourPointDefect_sub_le` | \(\|\Delta(M+E)-\Delta(M)\|\) is at most the sum of the four error bounds |
| `fourPointDefect_approx_of_nonneg` | \(\Delta(M)\ge 0\) implies \(\Delta(M+E)\ge -\|\Delta(M+E)-\Delta(M)\|\) |
| `one_le_supermodularityRatio_of_isStieltjes` | Stieltjes (hence SDDM \(+\gamma I\)) pairs have \(\gamma\ge 1\) |
| `supermodularityRatio_perturbation_lower` | if \(\gamma(M)\ge 1\) and each of the four errors moves by at most \(\varepsilon\le \mathrm{den}/2\), then \(\gamma(M+E)\ge 1-4\varepsilon/(\mathrm{den}+2\varepsilon)\) |
| `M0_supermodularityRatio_empty_zero_one` | on \(M_0\), empty-base \((0,1)\), \(\gamma=2288/2295<1\) |

File: `NystromSubmodularity/ApproxSubmodular.lean`. Delivered.

Intentional after this thread: a full `LinearMap.singularValues` wrapper;
an infinite Neumann series equaling the inverse; opening an actual
mathlib PR on `leanprover-community/mathlib4`.

## Verification (every thread)

- `lake build` sorry-free
- `rg sorry --glob '*.lean'` empty
- `#print axioms` on structural theorems: `propext`, `Classical.choice`,
  `Quot.sound`. Cramer evaluations (Frobenius / prediction traces, the
  64-matrix census, path-Laplacian principals, ridge defects) use
  `native_decide`, as the existing \(n\le 5\) SDDM checks do.
- Independent rational check when a closed form is claimed
