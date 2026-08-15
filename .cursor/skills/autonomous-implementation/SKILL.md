---
name: autonomous-implementation
description: >-
  Run unattended nystrom-submodularity work: load the phase cadence,
  keep the Cloud Agent environment honest, and deliver one specified
  leftover or milestone at a time. Use when the user asks to continue
  autonomously, to follow autonomous-implementation.md, or to take the
  next milestone without further design discussion.
---

# Autonomous implementation

Read [`autonomous-implementation.md`](../../../autonomous-implementation.md)
and [`.cursor/skills/nystrom-phase/SKILL.md`](../nystrom-phase/SKILL.md)
before editing.

## Rules

- One leftover thread or one milestone outcome per phase.
- Specify names in `RESEARCH.md` before proving.
- Milestone E is closed by exactly one of: a polynomial CPQR theorem;
  a machine-checked CPQR counterexample; or a counterexample plus a
  stronger static class. Do not claim the other two.
- Milestone F (CSSP bridge) stays specified-only until that phase.
- Environment changes go in `.cursor/install.sh` /
  `.cursor/environment.json`. Install must terminate and be idempotent.
- Verification and merge follow the phase skill. No `sorry`. No
  over-claims.
