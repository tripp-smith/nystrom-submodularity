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
| `neumann_series_inv`, `exists_neumannSplit_series_of_posDef` | same, or `Mathlib.Analysis.Matrix.Neumann` (new) |
| `hermitianNuclearNorm_eq_trace_of_posSemidef` | `Mathlib.Analysis.Matrix.Spectrum` (near `trace_eq_sum_eigenvalues`) |
| `matrixSingularValues`, `sum_matrixSingularValues_eq_hermitianNuclearNorm` | `Mathlib.Analysis.InnerProductSpace.SingularValues` (matrix wrapper) |
| `schattenOne`, `schattenOne_eq_hermitianNuclearNorm`, `schattenOne_smul` | same, or `Mathlib.Analysis.Matrix.Schatten` (new) |
| `hermitianNuclearNorm_fromBlocks_diagonal` | `Mathlib.Analysis.Matrix.Spectrum` (near `charpoly_fromBlocks_zero₁₂`) |
| `schurComplement_posDef`, `schur_of_inv_eq_compl_inv` | `Mathlib.LinearAlgebra.Matrix.SchurComplement` |

## Source files in this repo

The wrapper `NystromSubmodularity/MathlibReady.lean` re-exports the
public names and is the checklist for an upstream PR. Dependencies are
mathlib v4.33.0 (`lakefile.toml`).

## Out of an upstream PR

Nyström residuals, Colbrook counter-examples, greedy misselection, and
the signed-triangle family stay in this dedicated library.
