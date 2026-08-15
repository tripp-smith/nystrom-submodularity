"""Boundary tests: Schatten-1 identity, guarantees, sparse SDDM, estimators."""

from __future__ import annotations

from collections.abc import Sequence

import numpy as np
import pytest
from scipy import sparse

from graphnystrom import (
    GreedyNystromLandmarks,
    estimate_nystrom_error,
    four_point_defect,
    is_sddm,
    nystrom_error,
    path_laplacian,
    signature_switch,
)
from graphnystrom.laplacian import combinatorial_laplacian
from graphnystrom.residual import as_dense, precision_matrix
from graphnystrom.signature import is_diag_dominant, is_sdd, is_stieltjes


def _nystrom_residual(K: np.ndarray, S: Sequence[int]) -> np.ndarray:
    if not S:
        return K
    idx = list(S)
    cols = K[:, idx]
    return K - cols @ np.linalg.inv(K[np.ix_(idx, idx)]) @ cols.T


def _schatten_one(A: np.ndarray) -> float:
    return float(np.linalg.svd(A, compute_uv=False).sum())


def _random_stieltjes(n: int, seed: int) -> np.ndarray:
    rng = np.random.default_rng(seed)
    weights = rng.uniform(0.2, 2.0, size=(n, n))
    weights = 0.5 * (weights + weights.T)
    np.fill_diagonal(weights, 0.0)
    deg = weights.sum(axis=1)
    L = np.diag(deg) - weights
    return L + np.eye(n)


def test_svd_nuclear_matches_inverse_trace() -> None:
    rng = np.random.default_rng(0)
    for n, seed in ((3, 1), (4, 2), (5, 3)):
        A = rng.normal(size=(n, n))
        M = A.T @ A + 0.3 * np.eye(n)
        K = np.linalg.inv(M)
        for S in ([], [0], list(range(n - 1)), list(range(n))):
            residual = _nystrom_residual(K, S)
            assert _schatten_one(residual) == pytest.approx(
                nystrom_error(M, S), rel=1e-9, abs=1e-10
            )


def test_residual_matches_padded_complement_inverse() -> None:
    M = path_laplacian(4) + np.eye(4)
    K = np.linalg.inv(M)
    S = [1]
    residual = _nystrom_residual(K, S)
    C = [0, 2, 3]
    block_inv = np.linalg.inv(M[np.ix_(C, C)])
    # After placing S first, the residual is diag(0, M[C]⁻¹).
    perm = S + C
    reindexed = residual[np.ix_(perm, perm)]
    padded = np.zeros((4, 4))
    padded[1:, 1:] = block_inv
    assert np.allclose(reindexed, padded, atol=1e-10)
    assert nystrom_error(M, S) == pytest.approx(np.trace(block_inv), rel=1e-12)


def test_random_stieltjes_four_point_nonneg() -> None:
    for n, seed in ((3, 0), (4, 1), (4, 7)):
        M = _random_stieltjes(n, seed)
        assert is_stieltjes(M)
        for A_mask in range(1 << n):
            A = [i for i in range(n) if A_mask & (1 << i)]
            rest = [i for i in range(n) if i not in A]
            for a, i in enumerate(rest):
                for j in rest[a + 1 :]:
                    assert four_point_defect(M, A, i, j) >= -1e-10


def test_signature_congruent_stieltjes_preserves_error() -> None:
    M = path_laplacian(4) + np.eye(4)
    signs = [1, -1, 1, -1]
    flipped = signature_switch(M, signs)
    for S in ([], [0], [0, 2], [1, 2, 3]):
        assert nystrom_error(flipped, S) == pytest.approx(nystrom_error(M, S), rel=1e-12)
    assert four_point_defect(flipped, [], 0, 1) >= -1e-12


def test_heuristic_modes_have_no_guarantee() -> None:
    L = path_laplacian(6)
    for mode in ("stochastic", "approx"):
        sel = GreedyNystromLandmarks(L, k=2, gamma=1.0, mode=mode, seed=0)
        sel.run()
        assert sel.getGuarantee() is None
    exact = GreedyNystromLandmarks(L, k=2, gamma=1.0, mode="exact")
    exact.run()
    assert exact.getGuarantee() == pytest.approx(1.0 - 1.0 / np.e)
    lazy = GreedyNystromLandmarks(L, k=2, gamma=1.0, mode="lazy")
    lazy.run()
    assert lazy.getGuarantee() == pytest.approx(1.0 - 1.0 / np.e)


def test_hutchinson_cg_nonconvergence_falls_back() -> None:
    n = 12
    M = sparse.csr_matrix(path_laplacian(n) + np.eye(n))
    # maxiter=1 makes SciPy CG return info > 0. The spsolve fallback must
    # reproduce the same Hutchinson probes as a fully converged CG run.
    est_fallback = estimate_nystrom_error(M, [0, 3], probes=4, maxiter=1, seed=0)
    est_converged = estimate_nystrom_error(M, [0, 3], probes=4, maxiter=400, seed=0)
    assert est_fallback == pytest.approx(est_converged, rel=1e-10, abs=1e-10)
    # An unconverged iterate is not a valid residual: it need not match ℰ(S).
    exact = nystrom_error(M, [0, 3])
    assert est_fallback != pytest.approx(exact, rel=1e-3)


def test_zero_degree_vertex_is_sddm() -> None:
    L = combinatorial_laplacian(3, [(0, 1)], sparse_output=True)
    assert abs(L[2, 2]) <= 1e-15
    assert is_sddm(L)
    dense = combinatorial_laplacian(3, [(0, 1)], sparse_output=False)
    assert is_sddm(dense)


def test_sparse_sddm_does_not_densify(monkeypatch: pytest.MonkeyPatch) -> None:
    L = combinatorial_laplacian(8, [(i, i + 1) for i in range(7)], sparse_output=True)
    assert sparse.issparse(L)

    def boom(M: object) -> np.ndarray:
        raise AssertionError("as_dense should not run on the sparse SDDM path")

    monkeypatch.setattr("graphnystrom.signature.as_dense", boom)
    monkeypatch.setattr("graphnystrom.residual.as_dense", boom)
    assert is_sdd(L)
    assert is_diag_dominant(L)
    assert is_sddm(L)
    M = precision_matrix(L, 1.0)
    assert is_sddm(M)


def test_nystrom_error_stays_exact_on_sparse() -> None:
    L = combinatorial_laplacian(6, [(i, i + 1) for i in range(5)], sparse_output=True)
    M = L + sparse.eye(6, format="csr")
    S = [1, 4]
    dense = nystrom_error(M.toarray(), S)
    assert nystrom_error(M, S) == pytest.approx(dense, rel=1e-12)
    est = estimate_nystrom_error(M, S, probes=32, seed=1)
    assert est == pytest.approx(dense, rel=0.15, abs=0.05)
