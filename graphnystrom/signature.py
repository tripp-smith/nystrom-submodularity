"""SDDM / Stieltjes predicates and signature congruence.

Matches ``IsSDDM``, ``IsStieltjes``, and ``signatureCongr`` in
``Definitions.lean`` / ``Signature.lean``.
"""

from __future__ import annotations

from collections.abc import Sequence

import numpy as np
from numpy.typing import NDArray
from scipy import sparse

from graphnystrom.residual import as_dense

Array = NDArray[np.float64]


def is_symmetric(M: Array | sparse.spmatrix, atol: float = 1e-10) -> bool:
    if sparse.issparse(M):
        D = M - M.T
        if D.nnz == 0:
            return True
        return bool(np.all(np.abs(D.data) <= atol))
    A = as_dense(M)
    return bool(np.allclose(A, A.T, atol=atol))


def _row_abs_offdiag(M: Array | sparse.spmatrix) -> Array:
    """Row ℓ¹ mass of off-diagonal entries, without densifying a sparse matrix."""
    if sparse.issparse(M):
        A = M.tocsr()
        absA = A.copy()
        absA.data = np.abs(absA.data)
        row_sum = np.asarray(absA.sum(axis=1)).ravel()
        return row_sum - np.abs(A.diagonal())
    A = as_dense(M)
    return np.sum(np.abs(A), axis=1) - np.abs(np.diag(A))


def is_diag_dominant(M: Array | sparse.spmatrix, strict: bool = False) -> bool:
    diag = np.asarray(M.diagonal() if sparse.issparse(M) else np.diag(as_dense(M)))
    off = _row_abs_offdiag(M)
    if strict:
        return bool(np.all(off < diag - 1e-14))
    return bool(np.all(off <= diag + 1e-12))


def is_sdd(M: Array | sparse.spmatrix) -> bool:
    return is_symmetric(M) and is_diag_dominant(M)


def _offdiag_nonpos(M: Array | sparse.spmatrix, atol: float = 1e-12) -> bool:
    if sparse.issparse(M):
        A = M.tocsr()
        for i in range(A.shape[0]):
            start, end = A.indptr[i], A.indptr[i + 1]
            for j, v in zip(A.indices[start:end], A.data[start:end]):
                if i != j and v > atol:
                    return False
        return True
    A = as_dense(M)
    off = A.copy()
    np.fill_diagonal(off, 0.0)
    return bool(np.all(off <= atol))


def is_sddm(M: Array | sparse.spmatrix) -> bool:
    """``IsSDDM``: SDD with nonpositive off-diagonals.

    A zero diagonal (isolated vertex) is allowed; diagonal dominance already
    forces a nonnegative diagonal. Does not densify a CSR matrix.
    """
    n = M.shape[0]
    if n == 0:
        return False
    return is_sdd(M) and _offdiag_nonpos(M)


def is_stieltjes(M: Array | sparse.spmatrix) -> bool:
    """``IsStieltjes``: SPD with nonpositive off-diagonals."""
    A = as_dense(M)
    if not is_symmetric(A):
        return False
    off = A.copy()
    np.fill_diagonal(off, 0.0)
    if not np.all(off <= 1e-12):
        return False
    try:
        np.linalg.cholesky(A)
    except np.linalg.LinAlgError:
        return False
    return True


def signature_switch(
    M: Array | sparse.spmatrix, signs: Sequence[int] | Array
) -> Array:
    """``signatureCongr``: ``D M D`` for a ``{±1}`` diagonal."""
    A = as_dense(M)
    d = np.asarray(signs, dtype=np.float64)
    if d.shape != (A.shape[0],):
        raise ValueError("signs must have one entry per index")
    if not np.all(np.isin(d, (-1.0, 1.0))):
        raise ValueError("signature entries must be ±1")
    return (d[:, None] * A) * d[None, :]
