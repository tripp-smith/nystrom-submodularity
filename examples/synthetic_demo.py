#!/usr/bin/env python3
"""Deterministic synthetic demonstration of graphnystrom.

Reproduces the Lean-certified M0 defect, compares greedy to uniform /
leverage baselines on SDDM graphs, and records timings. Seeded.
"""

from __future__ import annotations

import json
import time
from pathlib import Path

import numpy as np

from graphnystrom import (
    GreedyNystromLandmarks,
    M0,
    evaluate_residual,
    four_point_defect,
    is_sddm,
    nystrom_error,
    path_laplacian,
    select_landmarks,
    signature_switch,
)
from graphnystrom.certified import M0_DELTA_EMPTY_ZERO_ONE, cycle_laplacian
from graphnystrom.laplacian import barabasi_albert, erdos_renyi, grid_laplacian
from graphnystrom.select import leverage_sample, uniform_sample
from graphnystrom.signature import is_stieltjes


def _time_select(L, k, mode, seed=0):
    t0 = time.perf_counter()
    S = select_landmarks(L, k=k, gamma=1.0, mode=mode, seed=seed)
    dt = time.perf_counter() - t0
    return S, evaluate_residual(L, S, gamma=1.0), dt


def main(out_path: Path | None = None) -> dict:
    rng_seed = 0
    report: dict = {"seed": rng_seed, "sections": {}}

    # --- Certified M0 ---
    delta = four_point_defect(M0, [], 0, 1)
    report["sections"]["m0"] = {
        "E_empty": nystrom_error(M0, []),
        "E_0": nystrom_error(M0, [0]),
        "E_1": nystrom_error(M0, [1]),
        "E_01": nystrom_error(M0, [0, 1]),
        "delta": delta,
        "certified_delta": M0_DELTA_EMPTY_ZERO_ONE,
        "sddm": is_sddm(M0),
    }
    assert abs(delta - M0_DELTA_EMPTY_ZERO_ONE) < 1e-12

    # --- Path success + signature flip ---
    P = path_laplacian(3)
    M = P + np.eye(3)
    flipped = signature_switch(M, [1, 1, -1])
    restored = signature_switch(flipped, [1, 1, -1])
    report["sections"]["path3"] = {
        "sddm": is_sddm(M),
        "delta_01": four_point_defect(M, [], 0, 1),
        "flip_preserves_empty": nystrom_error(flipped, []),
        "restored_stieltjes": is_stieltjes(restored),
    }

    # --- Path n=20: greedy vs baselines ---
    L = path_laplacian(21)
    gS, gE, gT = _time_select(L, 4, "exact")
    lazyS, lazyE, lazyT = _time_select(L, 4, "lazy")
    uni_errs = []
    lev_errs = []
    for s in range(5):
        uni = uniform_sample(21, 4, seed=s)
        lev = leverage_sample(L + np.eye(21), 4, seed=s)
        uni_errs.append(evaluate_residual(L, uni, gamma=1.0))
        lev_errs.append(evaluate_residual(L, lev, gamma=1.0))
    report["sections"]["path21"] = {
        "greedy_residual": gE,
        "lazy_residual": lazyE,
        "greedy_seconds": gT,
        "lazy_seconds": lazyT,
        "uniform_mean": float(np.mean(uni_errs)),
        "leverage_mean": float(np.mean(lev_errs)),
        "greedy_landmarks": gS,
        "lazy_matches_exact": gS == lazyS,
        "greedy_beats_uniform": gE <= min(uni_errs) + 1e-12 or gE < float(np.mean(uni_errs)),
    }

    # --- Grid ---
    G = grid_laplacian(6, 6)
    sel = GreedyNystromLandmarks(G, k=6, gamma=1.0, mode="lazy")
    t0 = time.perf_counter()
    sel.run()
    dt = time.perf_counter() - t0
    report["sections"]["grid6x6"] = {
        "n": 36,
        "k": 6,
        "residual": sel.getResidual(),
        "seconds": dt,
        "guarantee": sel.getGuarantee(),
        "sddm": is_sddm(G + np.eye(36)),
    }

    # --- ER / BA ---
    ER = erdos_renyi(40, 0.12, seed=rng_seed)
    BA = barabasi_albert(40, 2, seed=rng_seed)
    erS, erE, erT = _time_select(ER, 6, "exact", seed=rng_seed)
    baS, baE, baT = _time_select(BA, 6, "lazy", seed=rng_seed)
    report["sections"]["random40"] = {
        "er_residual": erE,
        "er_seconds": erT,
        "ba_residual": baE,
        "ba_seconds": baT,
        "cycle5_sddm": is_sddm(cycle_laplacian(5) + np.eye(5)),
    }

    # --- Approx sweep ---
    big = erdos_renyi(120, 0.04, seed=rng_seed)
    t0 = time.perf_counter()
    approx = select_landmarks(big, k=8, gamma=1.0, mode="approx", seed=rng_seed)
    dt = time.perf_counter() - t0
    report["sections"]["approx120"] = {
        "n": 120,
        "k": 8,
        "residual": evaluate_residual(big, approx, gamma=1.0),
        "seconds": dt,
        "landmarks_per_second": 8 / dt if dt > 0 else None,
    }

    text = json.dumps(report, indent=2)
    if out_path is not None:
        out_path.write_text(text + "\n")
    print(text)
    return report


if __name__ == "__main__":
    dest = Path(__file__).resolve().parent / "synthetic_demo_metrics.json"
    main(dest)
