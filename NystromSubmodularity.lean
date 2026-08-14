import NystromSubmodularity.Definitions
import NystromSubmodularity.PrincipalSubmatrix
import NystromSubmodularity.Nystrom
import NystromSubmodularity.Computable
import NystromSubmodularity.Stieltjes
import NystromSubmodularity.InverseTrace
import NystromSubmodularity.Phase1_Exploration
import NystromSubmodularity.Phase2_Proof
import NystromSubmodularity.Counterexamples.SDDDim3

/-!
# NystromSubmodularity

Root module for the Lean 4 / mathlib4 formalization of Problem 4.6:
supermodularity of the nuclear-norm Nyström residual for SDDM matrices,
and a 3×3 SDD obstruction.

Public theorems live in `Phase2_Proof.lean`. See `README.md` for the module
map and `SPEC.md` for the original two-phase plan plus recorded outcome.
-/
