# Specification: Two-Phase Attack on Problem 4.6

*(Submodularity of the nuclear-norm Nyström residual for SDDM / SDD matrices)*

**Primary environment:** Cursor + Lean 4 + mathlib4
**Python usage:** Only if absolutely necessary (explicitly justified below)

---

## Outcome (specification complete)

The plan below is the original two-phase attack. The formalization is
**finished**: both cases of the primary goal, the nuclear-norm justification
asked for in §2.1, and Colbrook’s resolution of Problem 4.6
(arXiv:2607.19282, Theorem 1(a)–(c) and the supporting results). Theorems
use the Wikipedia names (see `README.md` and `FINDINGS.md`).

### Success criteria (§0)

| Criterion | Delivery |
|-----------|----------|
| Sorry-free Lean 4 proof or counter-example, kernel-accepted | `lake build`; `rg sorry --glob '*.lean'` empty |
| Self-contained enough for a library | Dedicated repo; mathlib extraction remains optional (`FINDINGS.md`) |
| Intermediate checks machine-checked in Lean | Exact \(\mathbb{Q}\) Cramer traces; \(n\le 5\) exhaustive SDDM four-point checks; kernel `norm_num` on \(L_0\) |
| No unjustified Python | None used |

Public theorems print only the Lean defaults `propext`, `Classical.choice`,
`Quot.sound`.

### Primary goal (§0)

- **(a) SDDM.** `nystromError_supermodular_of_isSDDM`: for `IsSDDM L` and
  `γ > 0`, \(\mathcal{E}(S)=\operatorname{tr}((L+\gamma I)[S^{\mathsf{c}}]^{-1})\)
  is supermodular. Proof: Stieltjes inverse-nonnegativity (`Stieltjes.lean`)
  plus the Atamtürk–Gómez four-point identity (`InverseTrace.lean`).
- **(b) SDD.** `not_nystromError_supermodular_of_isSDD`: Colbrook’s
  \(3\times 3\) signed triangle \(L_0\) at \(\gamma=1\) has
  \(\Delta=-7/2040<0\). Traces and diagonal dominance are kernel proofs,
  not `native_decide`.
- **\(\gamma\to 0^+\).** The stated theorem is \(\gamma>0\). That, with
  `IsSDDM.quad_nonneg`, is the limit the goal asked for. Unshifted
  Laplacians (\(\gamma=0\), kernel the constants) are an intentional
  leftover, not a hole in (a).

### Definitional items (§2.1)

Nuclear norm was specified via singular values. Colbrook Theorem 2
(`nystromResidual_eq_padded_compl_inv`) identifies the residual of
\(M^{-1}\) with a padded complement inverse. That residual is PSD, so
`nuclearNystromError_eq_nystromError`: nuclear error equals inverse-trace.
There is no general SVD API; that identification is the justification
the specification required.

`exact_marginal` (Lemma 3) and `nystromError_strict_anti_monotone` hold
for every positive-definite precision matrix.
`nystromError_smul_scale` is Colbrook (30).

### Colbrook Theorem 1 (resolution of Problem 4.6)

- **(a)** SDDM \(\Rightarrow\) diminishing returns:
  `nystromError_supermodular_of_isSDDM`.
- **(b)** SDD can fail, including strictly SDD:
  `not_nystromError_supermodular_of_isSDD`,
  `not_nystromError_supermodular_of_isStrictSDD`,
  `Lfam_not_supermodular_iff` (Theorem 10: failure iff
  \(\varphi<t<1+\sqrt{2}\)).
- **(c)** Dimension three is minimal; with a nonempty base, four is
  minimal and may be strictly SDD with complete support:
  `nystromError_supermodular_of_card_le_two_posDef`,
  `nystromError_fourPoint_nonempty_of_card_le_three`,
  `exists_nystromError_fourPoint_neg_of_isStrictSDD_nonempty`.

Supporting results in the library: Theorem 2 (residual identity);
Propositions 7–8 and Corollary 13 (`Signature.lean`); greedy
misselection (`Lfam_greedy_misses_optimal_pair`,
`Lsharp_greedy_misses_optimal_pair`).

### Remaining research (see `RESEARCH.md`)

The leftover threads are now formalized: other losses on \(M_0\); a
finite SDD census; singular SDDM / path Laplacian; Hermitian nuclear
norm; mathlib packaging; Neumann splitting and walk traces; an explicit
ridge neighborhood of \(M_0\); and a general approximate-supermodularity
ratio with an entry-\(\ell^1\) Lipschitz bound
(`ApproxSubmodular.lean`, `M0_supermodularityRatio`). Still not
claimed: `LinearMap.singularValues`, the infinite Neumann identity, or
an actual mathlib4 PR. New phases follow
`.cursor/skills/nystrom-phase/SKILL.md`.

### Phase-1 / Phase-2 deliverables

Phase 1 (`SmallInstanceChecks.lean`): every tested SDDM instance with
\(n\le 5\) satisfies the four-point inequality; SDD already fails at
\(n=3\). Exhaustive search was restricted to \(n\le 5\) as the §4
fallback (not \(n=6\)).

Phase 2 (`Theorems.lean`): both the SDDM theorem and the SDD
counter-example, under the names above. `FINDINGS.md` is the
non-technical account; `README.md` is the module map.

**Directory (actual):**

```
README.md
FINDINGS.md
SPEC.md
RESEARCH.md
MATHLIB.md
NystromSubmodularity.lean
NystromSubmodularity/
├── Definitions.lean
├── PrincipalSubmatrix.lean
├── Computable.lean
├── Nystrom.lean
├── Stieltjes.lean
├── InverseTrace.lean
├── Minimality.lean
├── SmallInstanceChecks.lean
├── Theorems.lean
├── Counterexamples/SDDDim3.lean
├── Counterexamples/SDDDim4.lean
├── Counterexamples/SDDFamily.lean
├── Counterexamples/Greedy.lean
├── Signature.lean
├── OtherLosses.lean
├── Census.lean
├── Singular.lean
├── NuclearNormSVD.lean
├── Neumann.lean
├── Perturbation.lean
└── MathlibReady.lean
lakefile.toml
```

Historical names: `Phase1_Exploration.lean` is now `SmallInstanceChecks.lean`;
`Phase2_Proof.lean` is now `Theorems.lean`. Sections 0–5 below are the original
two-phase plan; filenames there are left as written. Parenthetical notes mark
the current names.

---

## 0. Overall Goals & Success Criteria

**Primary goal**
Prove or disprove:
$$
f(\mathcal{I}) := \bigl\| K - K_{:,\mathcal{I}}K_{\mathcal{I},\mathcal{I}}^{-1}K_{\mathcal{I},:} \bigr\|_{\{2,*\}}
$$
is a submodular set function of $\mathcal{I}\subseteq[n]$ when $K=(L+\gamma I)^{-1}$ ($\gamma>0$ or the appropriate limit $\gamma\to0^+$) and $L$ is
- (a) SDDM and positive-definite, or
- (b) SDD and positive-definite.

**Success criteria**
- A complete, `sorry`-free Lean 4 formalization of either a general proof or a concrete counter-example (matrix + two index sets) that Lean's kernel accepts.
- The formalization must be self-contained enough to be contributed to mathlib or a dedicated numerical-linear-algebra library.
- All intermediate computational checks that influence the direction of the proof must themselves be machine-checked in Lean whenever feasible.

**Non-goals**
- High-performance numerical libraries.
- Large-scale floating-point experiments beyond what is needed for orientation.

---

## 1. Environment Setup (Cursor-centric)

1. Create a new Lean 4 project with `lake`:
   ```
   lake new NystromSubmodularity
   cd NystromSubmodularity
   ```
2. Add the latest mathlib4 dependency in `lakefile.lean`.
3. Open the project folder in **Cursor**.
4. Install / enable:
   - Official Lean 4 extension
   - LeanCopilot (or equivalent LLM-in-Lean tactic server)
   - Any Cursor rules / custom instructions that force the AI to prefer mathlib lemmas and to keep proofs `sorry`-free.
5. Create the directory structure:
   ```
   NystromSubmodularity/
   ├── NystromSubmodularity.lean          -- main entry
   ├── Definitions.lean                   -- matrices, SDDM/SDD, Nyström residual, nuclear norm, submodularity
   ├── Phase1_Exploration.lean            -- (now SmallInstanceChecks.lean)
   ├── Phase2_Proof.lean                  -- (now Theorems.lean)
   ├── Counterexamples/                   -- concrete matrices if needed
   └── lakefile.lean
   ```

Cursor system prompt / rule (recommended):
> "You are a formalization assistant working exclusively in Lean 4 + mathlib. Prefer exact arithmetic and mathlib lemmas. Never introduce `sorry`. If a numerical check is required, first attempt it with exact `Rat` or `Int` matrices inside Lean. Only suggest Python when Lean's computational power is provably insufficient."

---

## 2. Phase 1 – Lean-Native Exploration & Counter-Example Search

**Objective**
Obtain rapid, machine-checked evidence that guides Phase 2, while staying inside Lean as long as possible.

### 2.1 Core Definitions (Definitions.lean)
Formalize (all exact):
- Symmetric, positive-definite matrices.
- SDDM and SDD predicates (`Matrix.IsSDDM`, `Matrix.IsSDD`).
- The resolvent $K = (L + \gamma\cdot 1)^{-1}$ (use `Matrix.inv` or `Matrix.posDef.inv`).
- Principal submatrix, Schur complement, Nyström residual matrix.
- Nuclear norm via sum of singular values (`Matrix.singularValues` + `List.sum` or the existing nuclear-norm API if present; otherwise define it).
- The set function $f : Finset (Fin n) \to \mathbb{R}$ (or `ℚ` when possible).
- Submodularity predicate:
  ```lean
  def Submodular (f : Finset α → ℝ) : Prop :=
    ∀ A B, f A + f B ≥ f (A ∪ B) + f (A ∩ B)
  ```

### 2.2 Exact Computational Search (`Phase1_Exploration.lean`, now `SmallInstanceChecks.lean`)
For small $n$ (target $n\le 6$, preferably $n\le 5$):

- Enumerate all pairs of `Finset (Fin n)` using `Finset.product` / `Finset.powerset`.
- Generate families of exact SDDM / SDD matrices over `ℚ` or `Int` (e.g., Laplacian of a small graph + positive diagonal perturbation, or random diagonally-dominant matrices with controlled off-diagonal signs).
- Evaluate $f$ exactly (or with a certified high-precision rational approximation that Lean can still decide).
- Assert the submodularity inequality for every pair; collect any violating pair into a concrete term.

Lean can decide these statements for $n\le 5$ in reasonable time because the number of subsets is $2^5=32$ and matrix operations stay tiny.

**Cursor interaction pattern**
- Ask Cursor to generate the generator functions and the exhaustive checker.
- Ask it to prove (or disprove) the inequalities for concrete small matrices.
- Any violation is immediately a formal counter-example candidate.

### 2.3 When (and only when) Python is permitted
Python is allowed solely for the following, and must be accompanied by a Lean comment justifying the necessity:

- Generating candidate floating-point matrices of size $n=7$–10 that are then *rounded to nearby rational SDDM/SDD matrices* and re-checked exactly in Lean.
- High-volume random sampling that would be impractically slow in pure Lean.

**Workflow if Python is used**
1. Cursor writes a minimal Python script that outputs a list of rational matrices + index sets in a Lean-readable format (e.g., a `.lean` snippet or a JSON that a Lean parser can ingest).
2. The output is immediately imported into `Phase1_Exploration.lean` (now `SmallInstanceChecks.lean`) and subjected to the same exact verification.
3. No Python result is trusted until Lean re-verifies it.

### 2.4 Phase-1 Deliverables
- A Lean file containing:
  - Confirmed submodularity on all tested SDDM instances of size $\le 5$.
  - Either a formal counter-example for SDD (or a large SDDM) or a statement "no counter-example found up to $n=6$".
- A short comment summarizing the empirical picture that will drive Phase 2 strategy.

**As delivered.** `SmallInstanceChecks.lean` confirms the four-point
inequality on path/cycle SDDM instances for \(n\le 5\). The SDD
counter-example is `L0` in `Counterexamples/SDDDim3.lean`. No \(n=6\)
exhaustive search was run (the §4 fallback). `FINDINGS.md` records the
empirical picture.

---

## 3. Phase 2 – Full Formalization in Lean 4

**Objective**
Produce a `sorry`-free theorem (or a machine-checked counter-example) for the general case.

### 3.1 Proof Strategy (guided by Phase 1)
- **If Phase 1 found a counter-example**
  Formalize that concrete matrix and the two index sets; prove that $f$ violates submodularity by direct computation of the four nuclear norms (Lean can do this with exact arithmetic or with a verified floating-point interval).

- **If no counter-example (expected for SDDM)**
  Follow the known Laplacian proof (Fornace–Lindsey) and lift it:
  1. Express the nuclear residual via Schur complements / positive-semidefinite order.
  2. Use the characterization of SDDM matrices (or the reduction "SDDM = Laplacian after adding a positive diagonal / dummy node").
  3. Replicate the combinatorial argument that appears in Theorem 5 of arXiv:2407.01698, replacing Laplacian-specific identities by the corresponding SDDM identities.
  4. For the SDD case, either
     - construct an explicit reduction to an SDDM / Laplacian instance, or
     - produce a counter-example (the more likely outcome if Phase 1 already suggested trouble).

### 3.2 AI-Assisted Development Loop inside Cursor
1. Write a high-level natural-language blueprint (or a `theorem … := by` skeleton with `sorry`s).
2. Use LeanCopilot / Cursor's agent mode to fill individual tactics, retrieve mathlib lemmas (`Matrix.schur_complement`, `PosDef`, `IsSymm`, singular-value lemmas, etc.).
3. After every successful sub-proof, ask Cursor to refactor for clarity and to remove any remaining `sorry`.
4. Maintain a "living blueprint" comment at the top of `Phase2_Proof.lean` (now `Theorems.lean`) that Cursor continually updates.

### 3.3 Key Lean Libraries / Lemmas to Leverage
- `Mathlib.LinearAlgebra.Matrix.*` (especially symmetric, positive-definite, Schur, singular values).
- `Mathlib.Data.Finset.*` and submodularity helpers if any exist (otherwise define them).
- Existing formalizations of nuclear norm or Schatten norms if present; otherwise a short definition via singular values is acceptable.

### 3.4 Phase-2 Deliverables
- `Phase2_Proof.lean` (now `Theorems.lean`) containing either
  ```lean
  theorem nystrom_residual_submodular_SDDM ...
  ```
  or
  ```lean
  def counterexample_SDD : ...
  theorem not_submodular_SDD : ¬ Submodular (f counterexample_SDD) := by ...
  ```
- A short README explaining the proof structure and any reductions used.
- (Optional) a PR-ready contribution to mathlib or a dedicated repository.

**As delivered.** Both: `nystromError_supermodular_of_isSDDM` in `Theorems.lean`
(positive SDDM theorem; the inequality is supermodularity of \(\mathcal{E}\),
not submodularity) and `not_nystromError_supermodular_of_isSDD` (SDD
counter-example), together with the Theorem 1(c) minimality statements,
Theorem 2, Theorem 10, Propositions 7–8, Corollary 13, and the greedy
example. `FINDINGS.md` is the non-technical account; `README.md` records
the Schur identity and module map. The optional mathlib PR was not
opened.

---

## 4. Risk Mitigation & Fall-backs

| Risk | Mitigation |
|------|------------|
| Lean too slow for $n=6$ exhaustive search | Restrict to $n\le5$; use random sampling of subset pairs; fall back to the justified Python generator only for candidate suggestion. |
| Nuclear-norm definition missing or slow | Define via sum of singular values; for small matrices compute the characteristic polynomial exactly. |
| Proof of SDDM case harder than expected | First formalize the known Laplacian theorem, then isolate the exact algebraic steps that fail for SDDM; feed those gaps back to Cursor. |
| SDD counter-example only appears at large $n$ | Accept that a negative result may require a hand-crafted matrix discovered with limited Python help, then verify exactly in Lean. |

---

## 5. Timeline Suggestion (Cursor-accelerated)

- Day 1: Project setup + complete `Definitions.lean`.
- Days 2–3: Phase 1 exhaustive / random exact search; decide the direction (proof vs counter-example).
- Days 4–10: Phase 2 formalization, iterating with Cursor/LeanCopilot.
- Final day: Clean-up, documentation, and (if positive) preparation for mathlib contribution.

---

This specification keeps Lean 4 and Cursor as the single source of truth. Python appears only as a temporary candidate generator whose output is immediately re-verified by Lean, satisfying the "only if absolutely necessary" constraint while still giving the practical benefits of computational exploration.
