import NystromSubmodularity.Stieltjes
import NystromSubmodularity.InverseTrace
import NystromSubmodularity.Neumann
import NystromSubmodularity.NuclearNormSVD
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Mathlib-ready re-exports

Wrappers for the lemmas listed in `MATHLIB.md`. Importing this module
pulls only the linear-algebra core (Stieltjes, inverse-trace,
Neumann splitting, Hermitian nuclear norm, SDDM positive-semidefiniteness),
not the Colbrook counter-examples.
-/

namespace NystromSubmodularity

open scoped Matrix.Norms.L2Operator

/-- Checklist: Stieltjes inverse-nonnegativity. -/
abbrev mathlib_IsStieltjes_inv_nonneg := @IsStieltjes.inv_nonneg

/-- Checklist: SDDM plus a positive shift is Stieltjes. -/
abbrev mathlib_IsSDDM_add_pos_smul_one_isStieltjes :=
  @IsSDDM.add_pos_smul_one_isStieltjes

/-- Checklist: SDDM quadratic forms are nonnegative. -/
abbrev mathlib_IsSDDM_quad_nonneg := @IsSDDM.quad_nonneg

/-- Checklist: every SDDM matrix is positive semidefinite. -/
abbrev mathlib_IsSDDM_posSemidef := @IsSDDM.posSemidef

/-- Checklist: exact one-index inverse-trace increment. -/
abbrev mathlib_exact_marginal := @exact_marginal

/-- Checklist: Hermitian nuclear norm equals trace on PSD matrices. -/
abbrev mathlib_hermitianNuclearNorm_eq_trace_of_posSemidef :=
  @hermitianNuclearNorm_eq_trace_of_posSemidef

/-- Checklist: nonnegative splitting of a Stieltjes matrix. -/
abbrev mathlib_neumannSplit_nonneg := @neumannSplit_nonneg

/-- Checklist: length-2 closed walks are supermodular. -/
abbrev mathlib_walkTraceTwo_supermodular := @walkTraceTwo_supermodular

/-- Checklist: singular-value sum equals the Hermitian nuclear norm. -/
abbrev mathlib_sum_matrixSingularValues_eq_hermitianNuclearNorm :=
  @sum_matrixSingularValues_eq_hermitianNuclearNorm

/-- Checklist: Neumann series equals the inverse under an L2 contraction. -/
abbrev mathlib_neumann_series_inv := @neumann_series_inv

end NystromSubmodularity
