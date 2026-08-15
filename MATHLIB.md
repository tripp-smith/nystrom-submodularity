# Proposed mathlib extraction

The lemmas below are candidates for a mathlib pull request. They do not
depend on Nyström approximation — only on principal submatrices,
Stieltjes / SDDM matrices, and inverse traces. This repository is the
working copy; no PR has been opened on
`leanprover-community/mathlib4`.

## Suggested landing spots

| Lemma | Proposed mathlib file |
|-------|------------------------|
| `IsSDDM`, `IsSDD`, `IsStieltjes` | `Mathlib.LinearAlgebra.Matrix.Stieltjes` (new) |
| `IsSDDM.quad_nonneg`, `IsSDDM.posSemidef` | same |
| `IsSDDM.add_pos_smul_one_isStieltjes` | same |
| `IsStieltjes.inv_nonneg` | same |
| `traceInv`, insert₁ / insert₂ block lemmas | `Mathlib.LinearAlgebra.Matrix.PrincipalSubmatrix` (new) |
| `exact_marginal`, four-point identity | `Mathlib.LinearAlgebra.Matrix.InverseTrace` (new) |
| `neumannSplit_nonneg`, `walkTraceTwo_supermodular` | same, or a remark in the Stieltjes module |
| `hermitianNuclearNorm_eq_trace_of_posSemidef` | `Mathlib.Analysis.Matrix.Spectrum` (near `trace_eq_sum_eigenvalues`) |

## Source files in this repo

The wrapper `NystromSubmodularity/MathlibReady.lean` re-exports the
public names and is the checklist for an upstream PR. Dependencies are
mathlib v4.33.0 (`lakefile.toml`).

## Out of an upstream PR

Nyström residuals, Colbrook counter-examples, greedy misselection, and
the signed-triangle family stay in this dedicated library.
