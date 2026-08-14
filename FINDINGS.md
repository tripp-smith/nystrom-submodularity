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
alone is not enough.

## The practical question

Suppose you have a large covariance (or precision) matrix for \(n\) variables,
and you can afford to treat only a subset \(S\) of those variables “exactly.”
Nyström approximation fills in the rest from the \(S\)-block. It is a standard
trick in Gaussian process regression, spatial statistics, and large-scale
graphical models: pick a few landmarks, invert a small matrix, and pretend you
have inverted the big one.

The leftover is an error matrix. We measure its size by the *nuclear* error
\(\mathcal{E}(S)\): the sum of the leftover singular values — a single number
that shrinks as you explain more of the matrix. (For the matrices we study
this is the same as a trace of a leftover inverse block, so we never need a
numerical SVD.) When \(S\) is empty you have explained nothing; when \(S\) is
everything the error is zero. Adding a landmark never hurts.

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
wrong pair. This is not a floating-point accident: the four traces are
ordinary 3×3 / 2×2 / 1×1 determinants.

So the sign pattern is doing real work. “Diagonally dominant” is not enough.
You need the M-matrix / Laplacian sign pattern as well. The failure is not an
artifact of sitting on the boundary of the SDD cone: Colbrook’s strictly
diagonally dominant perturbation \(L^\sharp\) (each row has a spare unit of
dominance) still has \(\Delta=-1/1092<0\).

Dimension two cannot fail, even without any sign or dominance hypothesis: once
only two indices remain unselected, the four-point defect is a square over a
positive quantity. So three is the smallest dimension at which mixed signs can
break greedy. If you already have at least one landmark and \(n\le 3\), the
same \(2\times 2\) identity rules out a negative defect.

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
example is already a counter-example. You would need extra structure, or you
should not invoke the greedy guarantee.

The object being optimized is the nuclear leftover, not mean-squared
prediction error and not a Kullback–Leibler divergence. Those other losses
might behave differently; we did not prove anything about them.

## What remains

These are genuine leftovers, not hidden holes in the two theorems above.

1. **Other losses.** Frobenius error, operator-norm error, and downstream
   prediction risk are open. Nuclear error was the question we were asked.
2. **How common is the SDD failure?** We have one sharp \(3\times 3\) family
   (and a strictly dominant perturbation), not a measure of how often
   mixed-sign SDD matrices violate diminishing returns in applied covariances.
   A nonempty-base counter-example at \(n=4\) is in Colbrook but not yet in
   this library.
3. **The \(\gamma\to 0\) limit.** The theorem is for \(\gamma>0\). Pure
   Laplacians (singular, kernel the constants) are not covered as written.
4. **A full SVD nuclear-norm API.** We use the trace identity that is valid
   for this residual, not a general singular-value definition.
5. **Mathlib extraction.** The Stieltjes and four-point lemmas could be
   upstreamed; they are not yet a mathlib PR.

Build the library with `lake build`. The two headline theorems are
`nystromError_supermodular_of_isSDDM` and
`not_nystromError_supermodular_of_isSDD` in `NystromSubmodularity/Theorems.lean`.
The small exhaustive checks live in `SmallInstanceChecks.lean`; the signed
triangle is in `Counterexamples/SDDDim3.lean`. `SPEC.md` is the original
two-phase attack plan plus a recorded outcome.
