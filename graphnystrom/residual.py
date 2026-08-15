"""Nuclear Nyström residual via the complementary inverse-trace.

Implements ``nystromError`` (Colbrook Theorem 2) and the computational
form of ``exact_marginal``: if ``Inv = M[Sᶜ]⁻¹`` then the reduction
from selecting complement-local index ``j`` is
``‖Inv[:, j]‖² / Inv[j, j]``, and the updated inverse is the Schur
complement that deletes that row and column.
"""

from __future__ import annotations

from collections.abc import Sequence

import numpy as np
from numpy.typing import NDArray
from scipy import sparse
from scipy.sparse.linalg import cg, LinearOperator, spsolve

Array = NDArray[np.float64]


def as_dense(M: Array | sparse.spmatrix) -> Array:
    if sparse.issparse(M):
        return np.asarray(M.toarray(), dtype=np.float64)
    return np.asarray(M, dtype=np.float64)


def precision_matrix(
    laplacian: Array | sparse.spmatrix, gamma: float
) -> Array | sparse.spmatrix:
    if gamma <= 0:
        raise ValueError("ridge gamma must be positive")
    if sparse.issparse(laplacian):
        n = laplacian.shape[0]
        return laplacian.tocsr() + gamma * sparse.eye(n, format="csr")
    L = as_dense(laplacian)
    return L + gamma * np.eye(L.shape[0], dtype=np.float64)


def _complement(n: int, S: Sequence[int]) -> list[int]:
    selected = set(int(i) for i in S)
    return [i for i in range(n) if i not in selected]


def nystrom_error(M: Array | sparse.spmatrix, S: Sequence[int]) -> float:
    """Exact ``ℰ(S) = tr(M[Sᶜ]⁻¹)``, with the empty-complement convention 0.

    Densifies the complementary principal block when ``M`` is sparse. For a
    stochastic estimator use ``estimate_nystrom_error``.
    """
    n = M.shape[0]
    C = _complement(n, S)
    if not C:
        return 0.0
    if sparse.issparse(M):
        idx = np.asarray(C, dtype=int)
        block = np.asarray(M.tocsr()[idx][:, idx].toarray(), dtype=np.float64)
    else:
        block = as_dense(M)[np.ix_(C, C)]
    return float(np.trace(np.linalg.inv(block)))


def cpqr_first_column(K: Array) -> int:
    """First Golub–Businger CPQR column: argmax of Euclidean column norms.

    Exact greedy instead maximises ``‖K[:, j]‖² / K[j, j]``. On ``M0`` the
    two rules agree on index 2, which lies in no optimal pair.
    """
    A = as_dense(K)
    return int(np.argmax(np.sum(A * A, axis=0)))


def estimate_nystrom_error(
    M: Array | sparse.spmatrix,
    S: Sequence[int],
    *,
    probes: int = 8,
    rtol: float = 1e-6,
    maxiter: int | None = None,
    seed: int = 0,
) -> float:
    """Hutchinson estimator of ``ℰ(S)``. Not the mathematical residual."""
    n = M.shape[0]
    C = _complement(n, S)
    if not C:
        return 0.0
    if sparse.issparse(M):
        return _hutchinson_trace_inv(
            M, C, probes=probes, rtol=rtol, maxiter=maxiter, seed=seed
        )
    block = as_dense(M)[np.ix_(C, C)]
    rng = np.random.default_rng(seed)
    acc = 0.0
    for _ in range(probes):
        z = rng.choice(np.array([-1.0, 1.0]), size=len(C))
        x = np.linalg.solve(block, z)
        acc += float(np.dot(z, x))
    return acc / probes


def evaluate_residual(
    laplacian: Array | sparse.spmatrix,
    landmarks: Sequence[int],
    gamma: float = 1.0,
    norm: str = "nuclear",
) -> float:
    if norm != "nuclear":
        raise ValueError(
            "only criterion='nuclear' is implemented; see OtherLosses.lean"
        )
    return nystrom_error(precision_matrix(laplacian, gamma), landmarks)


def four_point_defect(
    M: Array | sparse.spmatrix, A: Sequence[int], i: int, j: int
) -> float:
    """``Δ(A; i, j)`` as in ``fourPointDefect``."""
    A_set = list(A)
    return (
        nystrom_error(M, A_set)
        + nystrom_error(M, A_set + [i, j])
        - nystrom_error(M, A_set + [i])
        - nystrom_error(M, A_set + [j])
    )


def complement_inverse(M: Array, S: Sequence[int]) -> Array:
    C = _complement(M.shape[0], S)
    if not C:
        return np.zeros((0, 0), dtype=np.float64)
    return np.linalg.inv(as_dense(M)[np.ix_(C, C)])


def exact_marginal_gain(inv: Array, j: int) -> float:
    """Reduction in ``ℰ`` from deleting complement-local index ``j``."""
    col = inv[:, j]
    return float(np.dot(col, col) / inv[j, j])


def schur_delete(inv: Array, j: int) -> Array:
    """Schur update of a complement inverse after selecting local ``j``."""
    p = inv[j, j]
    q = np.delete(inv[:, j], j)
    R = np.delete(np.delete(inv, j, axis=0), j, axis=1)
    updated = R - np.outer(q, q) / p
    return 0.5 * (updated + updated.T)


def all_marginal_gains(inv: Array) -> Array:
    col_sq = np.einsum("ij,ij->j", inv, inv)
    return col_sq / np.diag(inv)


def _hutchinson_trace_inv(
    M: sparse.spmatrix,
    C: Sequence[int],
    probes: int = 8,
    rtol: float = 1e-6,
    maxiter: int | None = None,
    seed: int = 0,
) -> float:
    """Unbiased Hutchinson estimate of ``tr(M[C]⁻¹)`` via CG."""
    idx = np.asarray(C, dtype=int)
    block = M.tocsr()[idx][:, idx]
    rng = np.random.default_rng(seed)
    n = len(C)
    iters = maxiter if maxiter is not None else max(50, 4 * n)
    acc = 0.0
    for _ in range(probes):
        z = rng.choice(np.array([-1.0, 1.0]), size=n)
        x, info = cg(block, z, rtol=rtol, maxiter=iters)
        if info != 0:
            x = np.asarray(spsolve(block, z), dtype=np.float64)
        acc += float(np.dot(z, x))
    return acc / probes


def sparse_column_gain(
    M: sparse.spmatrix, C: Sequence[int], local_j: int
) -> float:
    """Exact (CG) gain ``‖M[C]⁻¹ e_j‖² / (M[C]⁻¹ e_j)_j``."""
    idx = np.asarray(C, dtype=int)
    block = M.tocsr()[idx][:, idx]
    e = np.zeros(len(C), dtype=np.float64)
    e[local_j] = 1.0
    x, info = cg(block, e, rtol=1e-8, maxiter=max(80, 8 * len(C)))
    if info != 0:
        x = np.asarray(spsolve(block, e), dtype=np.float64)
    return float(np.dot(x, x) / x[local_j])


def hutchinson_diagonal(
    M: Array | sparse.spmatrix, probes: int = 12, seed: int = 0
) -> Array:
    """Hutchinson diagonal estimator of ``M⁻¹`` (approx leverage scores)."""
    n = M.shape[0]
    rng = np.random.default_rng(seed)
    acc = np.zeros(n, dtype=np.float64)
    if sparse.issparse(M):
        op: Array | sparse.spmatrix | LinearOperator = M.tocsr()
    else:
        op = as_dense(M)
    for _ in range(probes):
        z = rng.choice(np.array([-1.0, 1.0]), size=n)
        if sparse.issparse(op):
            x, info = cg(op, z, rtol=1e-5, maxiter=max(40, 4 * n))
            if info != 0:
                x = np.asarray(spsolve(op, z), dtype=np.float64)
        else:
            x = np.linalg.solve(op, z)
        acc += z * x
    return acc / probes
