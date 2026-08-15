---
name: nystrom-phase
description: >-
  Execute a specification, verification, documentation, and commit-to-main
  phase in the nystrom-submodularity repository. Use when starting or finishing
  a SPEC.md / RESEARCH.md leftover, a new formalization thread, a math phase,
  or when asked to specify, verify, document, and merge Lean work to main.
---

# Nyström phase cadence

Reusable pattern for one formalization phase in this repository. Do not
estimate calendar time. Scope the phase by public theorem names, files,
and verification obligations.

Wikipedia supermodularity names are used throughout: diminishing returns
of the Nyström error \(\mathcal{E}\) is **supermodularity** of \(\mathcal{E}\).

## When to use

- A leftover in `RESEARCH.md` / `FINDINGS.md` / `README.md` “still open”
- A new slice of Colbrook / Problem 4.6
- Any request to “run the phase cadence”, “spec then prove”, or
  “document and commit to main”

Do not reopen a phase whose public theorems are already on `main`
unless the user asks to extend them.

## 1. Specify

Write the contract **before** proving.

- Original Problem 4.6 / Colbrook Theorem 1: add or tighten an Outcome
  map in `SPEC.md` (public Lean names ↔ paper statements).
- Leftover or post-spec research: add a numbered thread to `RESEARCH.md`
  with a one-line delivery and the names you will publish.
- Record what you will **not** claim. Intentional non-claims are not holes.

Each public theorem needs:

| Field | Content |
| --- | --- |
| Name | Exact Lean identifier |
| Statement | Mathematical claim in Wikipedia names |
| File | New or existing `NystromSubmodularity/*.lean` |
| Witness / closed form | Rational identity to check independently, if any |

Branch from current `main`:

```bash
git checkout main
git pull origin main
git checkout -b cursor/<descriptive-name>-5cc8
```

Branch names are lowercase `cursor/<descriptive-name>-5cc8`.

## 2. Implement

- No `sorry` in the library target.
- Prefer exact `ℚ` / `ℝ` algebra and existing Cramer identities.
- `native_decide` is allowed only for the same class of finite Cramer /
  census checks already used for \(n\le 5\) SDDM instances.
- Do not `open Matrix` in InverseTrace-style files if `M i j` then fails
  with `function expected`. After `Stieltjes` opens `Matrix`, prefer
  `rfl` entry lemmas and explicit `(fun j => |M i j|)` for row sums.
- `card_sdiff` in this mathlib is `#(t \ s) = #t - #(s ∩ t)`.
- Use `pow_succ'`, not `pow_succ`.
- `IsDiag` is `i ≠ j → D i j = 0`.
- For `ℝ`, prefer `IsSymm.apply` / `isHermitian_iff_isSymm` over
  `IsHermitian.apply`.
- `Matrix.mul_nonsing_inv` / `nonsing_inv_mul` take `IsUnit A.det`.
- Do not `simp [hinv]` on block inverses (`Bᴴ` becomes `Bᵀ`).
- Wire new modules through `NystromSubmodularity.lean` and
  `NystromSubmodularity/Theorems.lean`.
- Re-export headline names from `Theorems.lean` when they are part of
  the public contract.

## 3. Verify

Run all four. A green `lake build` alone is not enough.

```bash
lake build
rg sorry --glob '*.lean'
```

The `sorry` scan must be empty.

Print axioms on every **structural** public theorem (not a Cramer
evaluation):

```bash
lake env lean --run <<'LEAN'
import NystromSubmodularity.Theorems
#print axioms <theorem_name>
LEAN
```

Allowed axioms: `propext`, `Classical.choice`, `Quot.sound`.

If a closed form is claimed (a rational defect, a ratio, a census
count), recompute it independently of Lean — a shell arithmetic check
or a second Cramer expansion — and keep the transcript.

## 4. Document (same commit as the math)

Update all of the following in the commit that lands the theorems:

- `README.md` — module map, status paragraph, “still open” list
- `FINDINGS.md` — non-technical account of what is now proved
- `SPEC.md` — Outcome / remaining-research paragraph
- `NystromSubmodularity.lean` and `Theorems.lean` module headers
- `RESEARCH.md` when the phase was a leftover thread

Do not leave “still not claimed” text that the new theorems settle.

## 5. Commit, PR, merge to main

One commit per logical change. The math and the documentation cadence
above are one logical change. The skill file, or an unrelated spec-only
edit, is a separate commit.

```bash
git add <files>
git commit -m "<imperative summary of the phase>"
git push -u origin cursor/<descriptive-name>-5cc8
```

Open a **draft** PR against `main` with `ManagePullRequest`
(`create_pr`, `draft: true`). Do not use `gh pr create`.

**Before testing:** commit, push, and open the draft PR.

**After testing:** if the proof or docs changed, commit, push, and
`update_pr`. Then fast-forward `main` locally — do not `gh pr merge`:

```bash
git checkout main
git merge --ff-only cursor/<descriptive-name>-5cc8
git push origin main
```

Close the PR with `ManagePullRequest` `set_pr_status` / `status: closed`
after `main` has the commits. Do not mention the PR unless the user
asks.

## Definition of done

- Specified names exist and match the paper / leftover contract
- `lake build` succeeds and `rg sorry --glob '*.lean'` is empty
- Structural `#print axioms` are the Lean defaults
- Closed forms have an independent check
- Docs no longer list the delivered claim as open
- `origin/main` contains the phase

## What this skill does not do

- Open a mathlib4 PR
- Introduce Python as a source of truth (candidate generation only,
  then re-check in Lean)
- Change Wikipedia vs workshop naming
