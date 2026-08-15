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
import NystromSubmodularity.CPQR
import NystromSubmodularity.Signature
import NystromSubmodularity.OtherLosses
import NystromSubmodularity.Census
import NystromSubmodularity.Singular
import NystromSubmodularity.NuclearNormSVD
import NystromSubmodularity.Schur
import NystromSubmodularity.Neumann
import NystromSubmodularity.Perturbation
import NystromSubmodularity.ApproxSubmodular
import NystromSubmodularity.MathlibReady

/-!
# NystromSubmodularity

Root module for the Lean 4 / mathlib4 formalization of Problem 4.6:
supermodularity of the nuclear-norm Nyström residual for SDDM matrices,
and a 3×3 SDD obstruction (including a strictly diagonally dominant witness).
Dimension three is minimal. With a nonempty selected base, dimension four is
minimal. The signed-triangle family \(L(t)\) fails to be supermodular if and only if
\(\varphi<t<1+\sqrt{2}\) (Colbrook Theorem 4.3). On that interval, and on
\(L^\sharp\), greedy one-column selection picks a landmark that lies in no
optimal pair. Column-pivoted QR on \(M_0^{-1}\) makes the same first-column
mistake (`M0_cpqr_misses_optimal_pair`). Inverse-trace supermodularity is a property of the signed
support graph: a \(\{\pm 1\}\) signature that produces a Stieltjes matrix
is enough, and on a fully supported triangle this happens for every
positive-definite realization if and only if the sign pattern is
antibalanced (Corollary 13). Colbrook Theorem 2.1 identifies the Nyström
residual with a padded complement inverse, and
`schattenOne_nystromResidual_eq_nystromError` is the Schatten-1 norm of
that residual. The exact one-index increment holds for every
positive-definite precision matrix, \(\mathcal{E}\) is strictly
decreasing, and a nonzero scale multiplies every inverse-trace by its
reciprocal.

The approximate supermodularity ratio of a four-point pair is at least
one on every Stieltjes matrix; an arbitrary positive-definite
perturbation changes \(\mathcal{E}\) by an entry-\(\ell^1\) Lipschitz
bound. On \(M_0\) the empty-base \((0,1)\) ratio is \(2288/2295\).
Singular values wrap `LinearMap.singularValues` on rectangular real
matrices; `schattenOne` is their sum and equals the Hermitian nuclear
norm on Hermitian matrices. Block-diagonal nuclear mass adds. The
infinite Neumann series equals the inverse under an \(\ell^2\)
contraction.

Public theorems live in `Theorems.lean`. See `FINDINGS.md` for a
non-technical account, `README.md` for the module map, and `SPEC.md` for the
original two-phase plan. The specification is complete. Leftover
research threads and Milestone E are specified in `RESEARCH.md` and
are in the library. Milestone F (CSSP) remains specified only. New
phases follow `.cursor/skills/nystrom-phase/SKILL.md`.
-/
