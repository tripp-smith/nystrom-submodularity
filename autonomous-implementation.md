# Autonomous implementation playbook

This is the operating manual for Cloud Agents working in
`nystrom-submodularity`. It does not replace
[`.cursor/skills/nystrom-phase/SKILL.md`](.cursor/skills/nystrom-phase/SKILL.md)
or [SPEC.md](SPEC.md). It tells an agent how to choose work, how to
set up the machine, and what not to claim.

Wikipedia supermodularity names are used throughout.

## Load these skills first

| Skill | When |
|-------|------|
| `.cursor/skills/nystrom-phase/SKILL.md` | Any math phase, leftover thread, or milestone |
| `.cursor/skills/autonomous-implementation/SKILL.md` | Multi-step unattended work across env + math |
| `env-setup` (Cursor Cloud) | Environment, install, snapshot, or build changes |

Do not invent a second cadence. The phase skill is the merge gate.

## Choose work

1. If a leftover in `RESEARCH.md` is specified but not delivered, that
   is the next phase.
2. If a milestone is specified and still open, deliver **one** of its
   allowed outcomes. Do not start the next milestone in the same
   commit.
3. If the user names a milestone, that overrides the leftover list.

Current post-Problem-4.6 milestones:

| Milestone | Status | Allowed outcomes |
|-----------|--------|------------------|
| A–D | Delivered | Problem 4.6, Schatten-1 bridge, application semantics |
| **E CPQR** | Delivered as the \(M_0\) first-column counterexample | A polynomial CPQR theorem **or** a machine-checked counterexample **or** a counterexample plus a stronger static class |
| **F CSSP** | Untouched | A Lean identification of nuclear Nyström error with a CSSP residual, or a certified separation |

Do **not** claim a polynomial CPQR approximation ratio unless it is a
sorry-free public theorem. A certified first-column misselection is a
valid Milestone E outcome.

## Environment

Repository config lives in `.cursor/environment.json` and
`.cursor/install.sh`. Install must be idempotent and must terminate.
It installs the pinned Lean toolchain, mathlib cache, and the Python
`graphnystrom` test extras. It does not run `pytest` or start servers.
This repository is the environment source of truth: there is no
dashboard-managed environment id to propose against.

Print axioms with `lake env lean --stdin`, not `--run`.

Cloud-specific commands are in `AGENTS.md`.

## Implementation loop

1. Write the RESEARCH.md / SPEC.md contract **before** proving.
2. Branch `cursor/<descriptive-name>-5cc8` from current `main`.
3. Implement the named theorems. No `sorry` in the library target.
4. Update README, FINDINGS, SPEC, RESEARCH, and the root / Theorems
   headers in the same commit as the math.
5. Commit, push, open a draft PR, then verify (`lake build`, sorry
   scan, `#print axioms`, independent rationals, `pytest`).
6. Fast-forward `main` and close the PR. Do not `gh pr merge`.

## Intentional non-claims

- mathlib4 PR
- nuclear-norm triangle inequality / Ky Fan
- Networkit C++ module / Rust + PyO3 wheel
- unbounded greedy or CPQR approximation ratio on the SDD class
- Wikipedia vs workshop naming change
- Milestone F, until that phase is specified **and** delivered
