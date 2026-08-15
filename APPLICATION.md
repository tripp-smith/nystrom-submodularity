# Application specification: Nyström landmark selection

This note is the application-layer contract for turning the
machine-checked results in this repository into a usable landmark
selector. It is **not** a replacement for [SPEC.md](SPEC.md) (Problem
4.6 / Colbrook Theorem 1.1) or [RESEARCH.md](RESEARCH.md) (leftover Lean
threads). Lean remains the source of truth for every identity below.
Python is an operational layer: it must match the certified rationals
and must not introduce new mathematical claims.

Wikipedia supermodularity names are used throughout: diminishing
returns of \(\mathcal{E}\) is **supermodularity** of \(\mathcal{E}\).
The gain \(G(S)=\mathcal{E}(\emptyset)-\mathcal{E}(S)\) is then
submodular, so greedy maximisation of \(G\) has the classical
\((1-1/e)\) guarantee on SDDM instances.

Phase cadence: [`.cursor/skills/nystrom-phase/SKILL.md`](.cursor/skills/nystrom-phase/SKILL.md).

## Why this adaptation

The upstream sketch asked for a Networkit C++ module (or a Rust +
PyO3 crate) aimed at \(n=10^5\)–\(10^7\) and a contribution back to
Networkit. This repository is a Lean 4 / mathlib formalization with a
Python-optional application layer. Forking Networkit, adding Cython
bindings, and shipping manylinux wheels are out of scope here.

What this phase **does** deliver:

- A standalone Python package `graphnystrom` in this repo, with a
  Networkit-style `run()` / getter API.
- Exact residual and exact one-index increments from Colbrook Theorem
  2.1 / Lemma 2.2 (`nystromError`, `exact_marginal`).
- Pure greedy and lazy greedy (priority queue, using supermodularity
  of \(\mathcal{E}\) / submodularity of \(G\) for early acceptance).
- Stochastic and approximate (leverage) modes for larger sparse
  graphs, clearly labelled as heuristics.
- SciPy CSR / dense NumPy interop; optional NetworkX / Networkit
  conversion when those packages are installed.
- Unit tests that reproduce the Lean-certified rationals, including
  \(\Delta=-7/2040\) on \(M_0\).
- A deterministic synthetic demo.

What this phase **does not** claim:

- A Networkit fork, Cython module, or merged Networkit PR.
- A Rust + PyO3 wheel, Rayon kernels, or GPU offload.
- Production timings of \(k=1000\) on \(n=10^6\) in \(<30\) s (that
  is the Networkit / Rust target, not this delivery).
- Nuclear-norm triangle inequality / Ky Fan.
- An actual mathlib4 PR.
- A change of Wikipedia vs workshop names.
- Frobenius / prediction-risk selectors (Lean already shows those
  losses fail on \(M_0\); they stay future work).
- A polynomial CPQR approximation ratio (`cpqr_first_column` is a
  diagnostic; Lean certifies it misses the optimal pair on \(M_0\)).

Networkit remains the preferred *upstream* home for a C++ selector.
Rust + PyO3 remains the preferred *standalone* high-performance
kernel path. Both are recorded as follow-on work, not holes in this
contract.

## Mathematical interface

- Input: undirected weighted graph \(G\), or a real symmetric matrix
  treated as a Laplacian / precision matrix, and a ridge \(\gamma>0\).
- Precision: \(M=L+\gamma I\). Combinatorial Laplacians of undirected
  graphs are SDDM (off-diagonals \(\le 0\), weakly diagonally
  dominant, positive diagonal after a positive ridge).
- Error: \(\mathcal{E}(S)=\operatorname{tr}(M[S^{\mathsf{c}}]^{-1})\),
  with \(\mathcal{E}(V)=0\). This equals the nuclear norm of the
  Nyström residual (Colbrook Theorem 2 /
  `nystromResidual_eq_padded_compl_inv`).
- Landmark task: choose \(S\subset V\), \(|S|=k\), minimising
  \(\mathcal{E}(S)\) (equivalently maximising \(G(S)\)).
- Guarantee: if \(L\) is SDDM and \(\gamma>0\), then \(\mathcal{E}\)
  is supermodular (`nystromError_supermodular_of_isSDDM`), so exact and
  lazy greedy have factor \(1-1/e\). `getGuarantee()` returns that
  factor only for `mode in {"exact","lazy"}` on an SDDM matrix.
  Stochastic and approximate modes are heuristics and report `None`.
- Exact versus estimated residual: `nystrom_error` is always
  \(\operatorname{tr}(M[S^{\mathsf{c}}]^{-1})\). Hutchinson / CG lives
  in `estimate_nystrom_error` and is never a silent fallback.
- Incremental identity: if \(\operatorname{Inv}=M[S^{\mathsf{c}}]^{-1}\)
  and \(i\in S^{\mathsf{c}}\) has complement-local index \(j\), the
  exact reduction is
  \(\| \operatorname{Inv}_{:,j}\|_2^2 / \operatorname{Inv}_{jj}\).
  Updating \(\operatorname{Inv}\) is the Schur complement that
  deletes row/column \(j\). This is the computational form of
  `exact_marginal`.

## Public Python API

```python
from graphnystrom import (
    GreedyNystromLandmarks,
    NystromResolvent,
    evaluate_residual,
    four_point_defect,
    is_sddm,
    is_stieltjes,
    signature_switch,
    select_landmarks,
    combinatorial_laplacian,
)

selector = GreedyNystromLandmarks(
    G, k=8, gamma=1.0, mode="exact",  # exact | lazy | stochastic | approx
    criterion="nuclear", seed=42,
)
selector.run()
landmarks = selector.getLandmarks()
gains = selector.getMarginalGains()
bound = selector.getGuarantee()      # 1 - 1/e iff exact/lazy + SDDM

approx = NystromResolvent(G, landmarks, gamma=1.0)
y = approx.matvec(x)
residual = evaluate_residual(G, landmarks, gamma=1.0, norm="nuclear")
```

ASCII identifiers are the published names. `GreedyNyströmLandmarks`
is accepted as an alias.

| Name | Claim |
|------|--------|
| `evaluate_residual` / `nystrom_error` | exact \(\mathcal{E}(S)=\operatorname{tr}(M[S^{\mathsf{c}}]^{-1})\) |
| `estimate_nystrom_error` | Hutchinson estimator; not the mathematical residual |
| `four_point_defect` | \(\Delta(A;i,j)=\mathcal{E}(A)+\mathcal{E}(A\cup\{i,j\})-\mathcal{E}(A\cup\{i\})-\mathcal{E}(A\cup\{j\})\) |
| `exact_marginal_gain` | \(\mathcal{E}(S)-\mathcal{E}(S\cup\{i\})=\|v\|_2^2/v_i\) for the complement-inverse column |
| `cpqr_first_column` | first Golub–Businger column of \(K\); diagnostic, no ratio claim |
| `GreedyNystromLandmarks` | Networkit-style greedy / lazy / stochastic / approx selector |
| `NystromResolvent` | matvec \(X(X[S,:])^{-1}X^{\mathsf{T}}v\) after \(MX=E_S\) |
| `is_sddm` / `is_stieltjes` | Lean predicates on a dense or sparse matrix |
| `signature_switch` | \(DMD\) for a \(\{\pm 1\}\) diagonal |
| `M0_empty_zero_one` | certified \(\mathcal{E}\) values on Colbrook’s \(M_0\) |

Files: `graphnystrom/*.py`, `tests/test_*.py`,
`examples/synthetic_demo.py`.

## Modes

| Mode | Algorithm | When |
|------|-----------|------|
| `exact` | Dense inverse, then \(k\) Schur updates | Verification and \(n\lesssim 2\cdot 10^3\) |
| `lazy` | Same gains, lazy priority queue | SDDM instances; fewer score refreshes |
| `stochastic` | Exact gain on a random candidate subset | Larger \(n\); no \(1-1/e\) claim |
| `approx` | Hutchinson / CG diagonal of \(M^{-1}\) as a static score | Sparse large \(n\); heuristic |

`criterion` is `nuclear` only. Other residuals are rejected with an
explicit error pointing at `OtherLosses.lean`.

## Demonstration

`examples/synthetic_demo.py` (seeded):

1. Path / cycle / grid Laplacians (SDDM by construction).
2. Erdős–Rényi and Barabási–Albert graphs generated in-package
   (Networkit generators are optional, not required).
3. Greedy, lazy, uniform, and leverage-score selectors; records
   \(\mathcal{E}(S)\), wall-clock time, and (on small \(n\)) four-point
   defects.
4. Reproduces \(M_0\) (\(\Delta=-7/2040\)) and the path-Laplacian
   success case; shows a signature flip on the path that stays
   Stieltjes after congruence.
5. A moderate scalability sweep (\(n\) up to a few hundred in exact
   mode, a few thousand in approx mode).

All generation and metrics are deterministic given `seed`.

## Verification

- `pytest tests` : Lean-certified rationals, Schur/naive agreement,
  lazy ≡ exact on SDDM paths, \(L(t)\) greedy misselection, signature
  switch.
- Independent `fractions.Fraction` check of \(\Delta=-7/2040\).
- `lake build` and `rg sorry --glob '*.lean'` remain green (this
  phase adds no Lean theorems).
- Demo exits 0 and writes a metrics JSON.

## Follow-on (not this phase)

- Networkit `cpp/nystrom/` module + Cython, contribution PR.
- Rust + PyO3 kernels (`faer` / `sprs` + Rayon) and wheels.
- GPU offload; continuous / stochastic-greedy theory; DPP diversity.
- Frobenius / prediction-risk criteria.
