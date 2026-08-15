"""Greedy / lazy / incremental Schur agreement and L(t) misselection."""

from __future__ import annotations

import numpy as np
import pytest

from graphnystrom import (
    GreedyNystromLandmarks,
    M0,
    MSHARP,
    NystromResolvent,
    evaluate_residual,
    nystrom_error,
    path_laplacian,
    select_landmarks,
)
from graphnystrom.certified import cycle_laplacian
from graphnystrom.laplacian import erdos_renyi, grid_laplacian
from graphnystrom.residual import all_marginal_gains, complement_inverse, schur_delete
from graphnystrom.select import greedy_exact, greedy_lazy, uniform_sample


def test_schur_matches_naive_inverse() -> None:
    M = path_laplacian(5) + np.eye(5)
    inv = np.linalg.inv(M)
    energy = float(np.trace(inv))
    remaining = list(range(5))
    S: list[int] = []
    for step in range(3):
        scores = all_marginal_gains(inv)
        j = int(np.argmax(scores))
        gain = float(scores[j])
        S.append(remaining.pop(j))
        inv = schur_delete(inv, j)
        energy -= gain
        naive = nystrom_error(M, S)
        assert energy == pytest.approx(naive, rel=1e-10, abs=1e-10)
        assert np.allclose(inv, complement_inverse(M, S), atol=1e-10)


def test_lazy_matches_exact_on_path() -> None:
    # Odd path: unique centre, so greedy ties do not split the sequences.
    M = path_laplacian(7) + np.eye(7)
    exact = greedy_exact(M, 3)
    lazy = greedy_lazy(M, 3)
    assert exact.landmarks == lazy.landmarks
    assert exact.gains == pytest.approx(lazy.gains, rel=1e-12)
    assert exact.residual == pytest.approx(lazy.residual, rel=1e-12)
    even = path_laplacian(8) + np.eye(8)
    assert greedy_exact(even, 3).residual == pytest.approx(
        greedy_lazy(even, 3).residual, rel=1e-10
    )


def test_greedy_beats_uniform_on_path() -> None:
    L = path_laplacian(12)
    greedy = select_landmarks(L, k=3, gamma=1.0, mode="exact")
    uni = uniform_sample(12, 3, seed=0)
    e_g = evaluate_residual(L, greedy, gamma=1.0)
    e_u = evaluate_residual(L, uni, gamma=1.0)
    assert e_g <= e_u + 1e-12


def test_m0_greedy_picks_index_two() -> None:
    sel = GreedyNystromLandmarks(M0, k=1, precision=M0, mode="exact")
    sel.run()
    assert sel.getLandmarks() == [2]
    assert sel.getGuarantee() is None  # M0 is not SDDM


def test_msharp_greedy_misses_optimal_pair() -> None:
    sel = GreedyNystromLandmarks(MSHARP, k=1, precision=MSHARP, mode="exact")
    sel.run()
    assert sel.getLandmarks() == [2]
    # After picking 2, the best completion is not the certified optimum {0,1}.
    e_opt = nystrom_error(MSHARP, [0, 1])
    e_g2 = nystrom_error(MSHARP, [0, 2])
    assert e_opt < e_g2


def test_sddm_path_has_guarantee() -> None:
    L = path_laplacian(6)
    sel = GreedyNystromLandmarks(L, k=2, gamma=1.0, mode="exact")
    sel.run()
    assert sel.getGuarantee() == pytest.approx(1.0 - 1.0 / np.e)
    assert len(sel.getLandmarks()) == 2
    assert len(sel.getMarginalGains()) == 2


def test_resolvent_matvec_shape() -> None:
    L = cycle_laplacian(5)
    S = select_landmarks(L, k=2, gamma=1.0)
    approx = NystromResolvent(L, S, gamma=1.0)
    x = np.ones(5)
    y = approx.matvec(x)
    assert y.shape == (5,)
    op = approx.as_linear_operator()
    assert op.shape == (5, 5)
    assert np.allclose(op @ x, y)


def test_grid_and_er_run() -> None:
    G = grid_laplacian(4, 4)
    sel = GreedyNystromLandmarks(G, k=3, gamma=1.0, mode="lazy")
    sel.run()
    assert len(sel.getLandmarks()) == 3
    er = erdos_renyi(20, 0.2, seed=1)
    marks = select_landmarks(er, k=4, gamma=1.0, mode="stochastic", seed=1)
    assert len(set(marks)) == 4


def test_approx_mode_returns_k() -> None:
    L = path_laplacian(15)
    marks = select_landmarks(L, k=4, gamma=1.0, mode="approx", seed=0)
    assert len(marks) == 4


def test_rejects_non_nuclear() -> None:
    with pytest.raises(ValueError, match="nuclear"):
        GreedyNystromLandmarks(path_laplacian(3), k=1, criterion="frobenius")
