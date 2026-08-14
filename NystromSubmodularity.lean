import NystromSubmodularity.Definitions
import NystromSubmodularity.PrincipalSubmatrix
import NystromSubmodularity.Nystrom
import NystromSubmodularity.Computable
import NystromSubmodularity.Stieltjes
import NystromSubmodularity.InverseTrace
import NystromSubmodularity.Minimality
import NystromSubmodularity.SmallInstanceChecks
import NystromSubmodularity.Theorems
import NystromSubmodularity.Counterexamples.SDDDim3
import NystromSubmodularity.Counterexamples.SDDDim4
import NystromSubmodularity.Counterexamples.SDDFamily

/-!
# NystromSubmodularity

Root module for the Lean 4 / mathlib4 formalization of Problem 4.6:
supermodularity of the nuclear-norm Nyström residual for SDDM matrices,
and a 3×3 SDD obstruction (including a strictly diagonally dominant witness).
Dimension three is minimal. With a nonempty selected base, dimension four is
minimal. The signed-triangle family \(L(t)\) has a sharp failure interval
\(\varphi<t<1+\sqrt{2}\).

Public theorems live in `Theorems.lean`. See `FINDINGS.md` for a
non-technical account, `README.md` for the module map, and `SPEC.md` for the
original two-phase plan plus recorded outcome.
-/
