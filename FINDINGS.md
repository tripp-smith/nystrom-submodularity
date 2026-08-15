# What we found, in plain language

This note is for a reader who is comfortable with applied empirical work —
covariance matrices, greedy algorithms, diminishing returns — but who does not
want to read a linear-algebra paper. Think of it as a short memo: what the
result says for landmark selection, which matrices it covers, and what it does
not cover. The Lean files are the proof; this is the punchline.

**Bottom line.** If the precision matrix has the Laplacian / M-matrix sign
pattern (off-diagonals all \(\le 0\)), greedy landmark selection for Nyström
nuclear error has the usual diminishing-returns guarantee. If off-diagonals
are allowed to mix signs — some complements, some substitutes — that
guarantee can already fail on a \(3\times 3\) example. Diagonal dominance
alone is not enough. The specification in `SPEC.md` is complete. The leftover research
threads are specified in `RESEARCH.md` and are now in the library;
what remains at the end is a short list of things we deliberately
did not claim.

## The practical question

Suppose you have a large covariance (or precision) matrix for \(n\) variables,
and you can afford to treat only a subset \(S\) of those variables “exactly.”
Nyström approximation fills in the rest from the \(S\)-block. It is a standard
trick in Gaussian process regression, spatial statistics, and large-scale
graphical models: pick a few landmarks, invert a small matrix, and pretend you
have inverted the big one.

The leftover is an error matrix. We measure its size by the *nuclear* error
\(\mathcal{E}(S)\): the sum of the leftover singular values — a single number
that shrinks as you explain more of the matrix. For a positive-definite
precision matrix the leftover is itself positive semidefinite and equals a
padded inverse of the unselected block, so that nuclear number is exactly
the trace of the leftover (no SVD required). When \(S\) is empty you have
explained nothing; when \(S\) is everything the error is zero. Adding a
landmark always strictly decreases the error.

The design question is whether landmark selection has **diminishing returns**:
does the benefit of adding index \(i\) shrink as the set you already have gets
larger? That is the same structure as greedy facility location or greedy
instrument selection. If yes, a simple greedy rule — always add the landmark
that helps most right now — has the usual \((1-1/e)\) performance guarantee
relative to the best set of the same size. If no, greedy can be arbitrarily
misleading, and you are back to combinatorics.

Workshop language calls this “submodularity of the error.” In the usual
combinatorial dictionary, diminishing returns of \(\mathcal{E}\) is
**supermodularity** of \(\mathcal{E}\) (equivalently, submodularity of the *gain*
from each extra landmark). We use the dictionary names in the theorems.

## Two kinds of matrix

The precision matrix is \(M = L + \gamma I\) with \(\gamma>0\). The interesting
object is \(L\).

**SDDM** (“symmetric diagonally dominant M-matrix”). Off-diagonal entries are
all \(\le 0\), the diagonal is positive, and each row’s diagonal at least
covers the rest of the row in absolute value. Graph Laplacians live here:
variables are nodes, off-diagonals are (minus) edge weights. In a Gaussian
graphical model this is the uniform “substitutes / competitive” sign pattern —
partial correlations that do not flip sign.

**SDD** (“symmetric diagonally dominant”). Same row-sum discipline, but
off-diagonals may mix signs. You can have both substitutes and complements in
the same precision matrix. That mixed-sign case is the one that can break
diminishing returns.

The question was: does diminishing returns of \(\mathcal{E}\) hold for every
such \(L\), or only for the Laplacian-like ones?

## What is now proved

**For SDDM, diminishing returns always holds.** If \(L\) is SDDM and
\(\gamma>0\), then for any landmark set \(A\) and any two distinct indices
\(i,j\) not already in \(A\),

\[
\mathcal{E}(A) + \mathcal{E}(A\cup\{i,j\})
\;\ge\;
\mathcal{E}(A\cup\{i\}) + \mathcal{E}(A\cup\{j\}).
\]

That is the four-point form of supermodularity; it implies the usual
set-function inequality. Greedy landmark selection is theoretically justified
on this class. The proof is not a computation on examples. It is a general
argument, machine-checked in Lean: SDDM plus a ridge \(\gamma I\) is a
Stieltjes matrix (positive definite, nonpositive off-diagonals); those have
entrywise-nonnegative inverses; a two-by-two Schur-complement identity then
makes the four-point defect a sum of two obviously nonnegative terms.

**For SDD, diminishing returns can fail — already at \(3\times 3\).** There is
an explicit rational matrix (Colbrook’s signed triangle \(L_0\)) with mixed
off-diagonal signs, \(\gamma=1\), and four exact error values

\[
\mathcal{E}(\emptyset)=\tfrac{47}{51},\quad
\mathcal{E}(\{0\})=\mathcal{E}(\{1\})=\tfrac{9}{16},\quad
\mathcal{E}(\{0,1\})=\tfrac{1}{5}.
\]

The four-point defect is \(\Delta=-7/2040<0\). Adding the *second* of \(\{0,1\}\)
helps *more* than adding the first did: increasing returns, not diminishing.
Greedy, which looks only at the next best single add, can therefore pick the
wrong pair: on this family it uniquely prefers the singleton \(\{2\}\), but
the unique best pair is \(\{0,1\}\), so the first greedy landmark lies in no
optimal pair. At \(t=2\) the resulting pair residual is \(5/4\) times the
optimum; the strictly dominant \(L^\sharp\) does the same (\(5/12<11/26\),
then \(1/5\) versus \(1/6\)). This is not a floating-point accident: the four traces are
ordinary 3×3 / 2×2 / 1×1 determinants. The same matrix is the \(t=2\) member
of a one-parameter family \(L(t)\). For that family, diminishing returns
fails if and only if the golden ratio is less than \(t\) and \(t\) is less
than \(1+\sqrt{2}\): the other empty-base pairs stay positive, and a nonempty
base cannot fail on three indices. So the obstruction is exactly that
interval, not just the single witness \(t=2\).

The nuclear number is not a definitional rewrite: the leftover of
\(M^{-1}\) is the padded inverse of the unselected block, that leftover is
positive semidefinite, and its nuclear norm is its trace. Adding any new
landmark strictly decreases the error for every positive-definite precision
matrix, and scaling the precision matrix by a nonzero constant just
rescales every error value (and every four-point defect) by the reciprocal.

So the sign pattern is doing real work. “Diagonally dominant” is not enough.
You need the M-matrix / Laplacian sign pattern as well — or a sign pattern
that can be *turned into* that one by flipping the signs of some variables
(a \(\{\pm 1\}\) signature). Principal inverse-traces are unchanged by that
flip, so the diminishing-returns guarantee survives. On a fully supported
triangle this is possible for every positive-definite realization if and
only if the unique 3-cycle has an even number of positive edges
(antibalanced). A single positive triangle edge is the obstruction: the
\(L^\sharp\) pattern has signs \(+,-,-\) and product \(+1\), so no signature
can make it Stieltjes. The failure is not an artifact of sitting on the
boundary of the SDD cone: Colbrook’s strictly diagonally dominant
perturbation \(L^\sharp\) (each row has a spare unit of dominance) still
has \(\Delta=-1/1092<0\).

Dimension two cannot fail, even without any sign or dominance hypothesis: once
only two indices remain unselected, the four-point defect is a square over a
positive quantity. So three is the smallest dimension at which mixed signs can
break greedy. If you already have at least one landmark and \(n\le 3\), the
same \(2\times 2\) identity rules out a negative defect. That lower bound is
sharp: a strictly diagonally dominant \(4\times 4\) matrix with every
off-diagonal filled in still fails after one landmark is already chosen
(\(\Delta=-7/20400\)).

Small exhaustive checks on path and cycle Laplacians of size \(n\le 5\) never
found an SDDM violation; that is what suggested the general proof. Those checks
are still in the library as sanity tests. They are not the theorem.

## How to read this if you use these methods

If your precision matrix comes from a weighted graph, a spatial GMRF with
positive weights, or any construction that forbids positive off-diagonals, you
are in the SDDM world. Landmark Nyström error has diminishing returns, and
greedy is on theoretically solid ground.

If you allow mixed-sign partial correlations — some complements, some
substitutes — diagonal dominance does **not** save you. A three-variable
example is already a counter-example, and greedy can pick a landmark that
is in no best pair. You would need extra structure (an antibalanced signed
support graph, so some signature restores the Laplacian pattern), or you
should not invoke the greedy guarantee. Laplacian signs can themselves be
flipped by a signature and greedy still has the guarantee.

The object being optimized is the nuclear leftover, not mean-squared
prediction error and not a Kullback–Leibler divergence. Those other losses
might behave differently; we did not prove anything about them.

## What the leftover threads now say

1. **Other losses.** Nuclear is not special to the obstruction: on \(M_0\)
   the squared-Frobenius residual and the all-ones residual quadratic
   (a prediction-risk surrogate) both have a negative empty-base
   \((0,1)\) defect. On a singleton complement the three numbers
   collapse to the same scalar.
2. **How common is the SDD failure?** On a seven-point rational grid of
   \(L(t)\), only \(t=2\) lies in the Colbrook interval. Among 64
   complete-support integer triangles with off-diagonals in
   \(\{\pm 1,\pm 2\}\) and strictly dominant diagonals, exactly four
   fail the empty-base \((0,1)\) test — the \(L^\sharp\) pattern and
   its signature orbit.
3. **Singular \(\gamma=0\).** Every SDDM matrix is positive semidefinite.
   The unshifted 3-path Laplacian annihilates the constants. Nyström
   error is still defined on proper complements; the nonempty-base
   four-point defect stays positive, and every positive ridge remains
   supermodular.
4. **Hermitian nuclear-norm / Schatten-1 API.** \(\sum_i|\lambda_i|\) via
   mathlib eigenvalues equals the trace on every PSD matrix, so it
   agrees with `nuclearNorm` and with `nystromError` on the complementary
   inverse. `matrixSingularValues` wraps `LinearMap.singularValues` on
   rectangular real matrices; `schattenOne` is their singular-value sum.
   On a Hermitian matrix that sum equals \(\sum_i|\lambda_i|\). Absolute
   homogeneity `schattenOne (c • A) = |c| * schattenOne A` holds, and
   `schattenOne !![a] = |a|`. Block-diagonal Hermitian nuclear mass
   adds (`hermitianNuclearNorm_fromBlocks_diagonal`).
5. **Mathlib extraction.** The linear-algebra core is packaged in
   `MathlibReady.lean` and `MATHLIB.md`. No PR has been opened on
   mathlib4.
6. **Neumann / walks.** A Stieltjes matrix splits as \(B=sI-M\ge 0\).
   Length-1 walk traces are modular; length-2 closed-walk traces are
   supermodular. If \(\|A\|_2<1\), then \((I-A)^{-1}=\sum_k A^k\).
   Every positive-definite matrix admits a splitting to which this
   applies; the \(1\times 1\) check \(A=1/2\) has both sides equal to
   \(2\).
7. **Perturbation.** \(M_0+\varepsilon I\) for
   \(\varepsilon\in\{0,1/10,1/2,1\}\) all have a negative defect.
   Scaling by \(c>0\) preserves the sign of every four-point defect.
8. **Approximate supermodularity ratio.** For any four-point pair the
   ratio \(\gamma=(\mathcal{E}(A)+\mathcal{E}(A\cup\{i,j\}))/(\mathcal{E}(A\cup\{i\})+\mathcal{E}(A\cup\{j\}))\)
   is at least \(1\) on a Stieltjes matrix. An arbitrary perturbation
   that keeps the matrix positive definite moves each Nyström value by
   at most a product of inverse entry-\(\ell^1\) masses times the
   complementary block of the perturbation, so a nonnegative defect can
   drop by at most that four-term slack. If each of the four errors
   moves by at most \(\varepsilon\le\mathrm{den}/2\), the perturbed
   ratio is at least \(1-4\varepsilon/(\mathrm{den}+2\varepsilon)\).
   On \(M_0\) the empty-base \((0,1)\) ratio is the certified
   \(2288/2295<1\), matching the defect \(-7/2040\).

9. **Application layer.** `graphnystrom` turns the certified inverse-trace
   into a Networkit-style greedy landmark selector. On SDDM Laplacians
   it reports the \((1-1/e)\) guarantee; on Colbrook’s \(M_0\) it
   reproduces \(\Delta=-7/2040\) and shows greedy picking the bad
   first landmark. See `APPLICATION.md`.

## What we still do not claim

An actual mathlib4 pull request. That is a deliberate non-claim: the
phase skill does not open upstream PRs. We also do not claim the
nuclear-norm triangle inequality or Ky Fan inequalities, a Networkit
C++ module, or a Rust + PyO3 wheel. The rectangular Schatten-1 API,
block-diagonal nuclear additivity, the infinite Neumann identity,
GitHub Actions CI, and the `graphnystrom` selector are now in the
repository.

Build the library with `lake build`. The headline theorems are
`nystromError_supermodular_of_isSDDM` and
`not_nystromError_supermodular_of_isSDD` in `NystromSubmodularity/Theorems.lean`.
The small exhaustive checks live in `SmallInstanceChecks.lean`; the signed
triangle is in `Counterexamples/SDDDim3.lean`; the nonempty-base \(4\times 4\)
witness is in `Counterexamples/SDDDim4.lean`; the sharp interval for \(L(t)\)
is in `Counterexamples/SDDFamily.lean`; greedy misselection is in
`Counterexamples/Greedy.lean`; signature switching is in `Signature.lean`;
the residual identity is in `Nystrom.lean`. Leftover-research modules
are listed in `RESEARCH.md`. `SPEC.md` is the original two-phase attack
plan plus the recorded completion.
