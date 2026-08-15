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
import NystromSubmodularity.Counterexamples.Greedy
import NystromSubmodularity.Signature

/-!
# NystromSubmodularity

Root module for the Lean 4 / mathlib4 formalization of Problem 4.6:
supermodularity of the nuclear-norm Nyström residual for SDDM matrices,
and a 3×3 SDD obstruction (including a strictly diagonally dominant witness).
Dimension three is minimal. With a nonempty selected base, dimension four is
minimal. The signed-triangle family \(L(t)\) fails to be supermodular if and only if
\(\varphi<t<1+\sqrt{2}\) (Colbrook Theorem 10). On that interval, and on
\(L^\sharp\), greedy one-column selection picks a landmark that lies in no
optimal pair. Inverse-trace supermodularity is a property of the signed
support graph: a \(\{\pm 1\}\) signature that produces a Stieltjes matrix
is enough (Colbrook Proposition 7), and on a fully supported triangle this
happens for every positive-definite realization if and only if the sign
pattern is antibalanced (Corollary 13). Colbrook Theorem 2 identifies the
Nyström residual with a padded complement inverse, so nuclear error equals
the inverse-trace on that PSD residual. The exact one-index increment holds
for every positive-definite precision matrix, \(\mathcal{E}\) is strictly
decreasing, and a nonzero scale multiplies every inverse-trace by its
reciprocal.

Public theorems live in `Theorems.lean`. See `FINDINGS.md` for a
non-technical account, `README.md` for the module map, and `SPEC.md` for the
original two-phase plan. The specification is complete.
-/
