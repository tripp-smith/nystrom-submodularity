# Agent notes

Lean 4 / mathlib **v4.33.0**, pinned by `lean-toolchain` and
`lake-manifest.json`. Wikipedia supermodularity names are used
throughout. The merge cadence is
[`.cursor/skills/nystrom-phase/SKILL.md`](.cursor/skills/nystrom-phase/SKILL.md).
Unattended work follows [`autonomous-implementation.md`](autonomous-implementation.md).

## Commands

```bash
lake build
rg sorry --glob '*.lean' --glob '!.lake/**'   # must be empty
lake env lean --stdin                         # #print axioms; not --run
PYTHONPATH=. python3 -m pytest
scripts/verify.sh
```

`#print axioms` on structural theorems may list only `propext`,
`Classical.choice`, and `Quot.sound`. Finite Cramer / census checks
may use `native_decide`. Recurring independent checks: \(\lvert-3\rvert=3\),
\(2+3=5\), \(M_0\) \(\Delta=-7/2040\). After Milestone E also check
\(\|K_{:,0}\|_2^2=293/2601\), \(\|K_{:,2}\|_2^2=297/2601\), pair ratio
\(5/4\).

## Cursor Cloud specific instructions

- Bootstrap is `.cursor/install.sh` (elan, `lake exe cache get`,
  `lake build`, Python test extras). It is idempotent and must
  terminate. Do not put `pytest` or a Lean watch process in `install`.
- After changing Lean, run `lake build` and the sorry scan. After
  changing `graphnystrom/`, run `PYTHONPATH=. python3 -m pytest`.
- Do not kill unrelated processes by name. Leave test processes
  running unless they block the next step.
- Branch names are `cursor/<descriptive-name>-5cc8`. Open draft PRs
  with `ManagePullRequest`. Fast-forward `main`; do not `gh pr merge`.
