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
| 9 Singular values | `matrixSingularValues` wraps `LinearMap.singularValues`; sum equals \(\sum_i|\lambda_i|\) on Hermitian matrices |
| 10 Infinite Neumann | \(\|A\|_2<1\Rightarrow(I-A)^{-1}=\sum_k A^k\); every PD matrix admits a splitting; \(1\times 1\) check equals \(2\) |
| 11 Schatten-1 / Schur / CI | Rectangular SVD; `schattenOne`; block-diagonal nuclear additivity; GitHub Actions `lake build` + no-`sorry` |

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

## Thread 9 — `LinearMap.singularValues` wrapper

Phase cadence: `.cursor/skills/nystrom-phase/SKILL.md`.

Thread 4 identified the nuclear norm of a Hermitian matrix with
\(\sum_i|\lambda_i|\). Mathlib already defines
`LinearMap.singularValues` on finite-dimensional inner-product maps.
This thread wraps that API on matrices and identifies the two sums on
PSD residuals.

| Name | Claim |
|------|--------|
| `matrixSingularValues` | `A.toEuclideanLin.singularValues` |
| `matrixSingularValues_nonneg` | every singular value is nonnegative |
| `sum_matrixSingularValues_eq_hermitianNuclearNorm` | on a Hermitian matrix, \(\sum_i\sigma_i=\sum_i\|\lambda_i\|\) |
| `nuclearNorm_eq_sum_matrixSingularValues` | on a PSD matrix the library `nuclearNorm` equals that sum |
| `nystromError_eq_sum_matrixSingularValues_compl` | \(\mathcal{E}(S)\) is the singular-value sum of the complementary inverse |

File: `NystromSubmodularity/NuclearNormSVD.lean`. Delivered.

## Thread 10 — Infinite Neumann series

The walk traces in `Neumann.lean` stop at length 2. The missing identity
is the geometric series for the inverse: if \(\|A\|_2<1\) in the
\(\ell^2\) operator norm, then \((I-A)^{-1}=\sum_{k=0}^\infty A^k\).
On a positive-definite precision matrix the Stieltjes splitting
\(B=sI-M\) satisfies \(\|B/s\|_2<1\) for all sufficiently large \(s\),
so \(M^{-1}=s^{-1}\sum_k (B/s)^k\).

| Name | Claim |
|------|--------|
| `neumann_series_inv` | \(\|A\|_2<1\) implies \((I-A)^{-1}=\sum_k A^k\) |
| `neumannSplit_inv_eq_tsum` | if \(\|B/s\|_2<1\) and \(M=sI-B\), then \(M^{-1}=s^{-1}\sum_k(B/s)^k\) |
| `exists_neumannSplit_series_of_posDef` | every PD matrix admits such an \(s\) |
| `neumann_series_inv_half` | certified \(1\times 1\) check: \(A=(1/2)\), both sides equal \(2\) |

File: `NystromSubmodularity/Neumann.lean`. Delivered.

## Thread 11 — Schatten-1, Schur infrastructure, CI

Phase cadence: `.cursor/skills/nystrom-phase/SKILL.md`.

Thread 9 wraps singular values on **square** real matrices and identifies
their sum with \(\sum_i|\lambda_i|\) on Hermitian matrices. The library
`nuclearNorm` is still the trace (valid on PSD residuals). This thread
extends that API to a usable Schatten-1 norm on rectangular matrices,
adds block-diagonal nuclear identities next to the existing Schur
complements, and installs CI so the mathlib-quality bar is checked on
every push.

| Name | Claim |
|------|--------|
| `matrixSingularValues` | `A.toEuclideanLin.singularValues` for `Matrix m n ℝ` |
| `schattenOne` | \(\sum_{i<\#n}\sigma_i(A)\) (Schatten-1 / nuclear) |
| `schattenOne_nonneg` | \(\operatorname{schattenOne} A\ge 0\) |
| `schattenOne_zero` | `schattenOne 0 = 0` |
| `schattenOne_eq_hermitianNuclearNorm` | on a Hermitian square matrix, equals \(\sum_i\|\lambda_i\|\) |
| `schattenOne_eq_trace_of_posSemidef` | on a PSD matrix, equals `trace` |
| `schattenOne_smul` | `schattenOne (c • A) = \|c\| * schattenOne A` |
| `schattenOne_neg` | `schattenOne (-A) = schattenOne A` |
| `schattenOne_fin_one` | `schattenOne !![a] = \|a\|` |
| `schattenOne_neg_three` | certified `!![-3]` has Schatten-1 equal to `3` |
| `isHermitian_fromBlocks_diagonal` | `fromBlocks A 0 0 D` is Hermitian if `A` and `D` are |
| `fromBlocks_diagonal_posSemidef` | block-diagonal of PSD blocks is PSD |
| `hermitianNuclearNorm_fromBlocks_diagonal` | \(\|\operatorname{diag}(A,D)\|_*=\|A\|_*+\|D\|_*\) |
| `schattenOne_fromBlocks_diagonal_of_posSemidef` | equals `A.trace + D.trace` |
| `schattenOne_fromBlocks_two_three` | certified `diag(2,3)` has Schatten-1 equal to `5` |

Files: `NystromSubmodularity/NuclearNormSVD.lean` (rectangular SVD /
`schattenOne`); `NystromSubmodularity/Schur.lean` (block-diagonal
nuclear identities and Schur re-exports). Existing Schur positivity
lemmas stay in `Stieltjes.lean` / `Nystrom.lean` (moving them would
break imports). CI: `.github/workflows/lean.yml` (`lake build`, no
`sorry`). Local cadence: `scripts/verify.sh`.

Do **not** claim: nuclear-norm triangle inequality / Ky Fan; an actual
mathlib4 PR; a change of Wikipedia vs workshop names.

Delivered.

Intentional after these threads: opening an actual mathlib PR on
`leanprover-community/mathlib4` (the phase skill does not open
upstream PRs).

## Verification (every thread)

- `lake build` sorry-free
- `rg sorry --glob '*.lean'` empty
- `#print axioms` on structural theorems: `propext`, `Classical.choice`,
  `Quot.sound`. Cramer evaluations (Frobenius / prediction traces, the
  64-matrix census, path-Laplacian principals, ridge defects) use
  `native_decide`, as the existing \(n\le 5\) SDDM checks do.
- Independent rational check when a closed form is claimed
