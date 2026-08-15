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
        return (M - M.T).nnz == 0 or np.allclose(M.toarray(), M.T.toarray(), atol=atol)
    A = as_dense(M)
    return bool(np.allclose(A, A.T, atol=atol))


def is_diag_dominant(M: Array | sparse.spmatrix, strict: bool = False) -> bool:
    A = as_dense(M)
    off = np.sum(np.abs(A), axis=1) - np.abs(np.diag(A))
    if strict:
        return bool(np.all(off < np.diag(A) - 1e-14))
    return bool(np.all(off <= np.diag(A) + 1e-12))


def is_sdd(M: Array | sparse.spmatrix) -> bool:
    return is_symmetric(M) and is_diag_dominant(M)


def is_sddm(M: Array | sparse.spmatrix) -> bool:
    """``IsSDDM``: SDD, positive diagonal, nonpositive off-diagonals."""
    A = as_dense(M)
    n = A.shape[0]
    if not is_sdd(A):
        return False
    if not np.all(np.diag(A) > 0):
        return False
    off = A.copy()
    np.fill_diagonal(off, 0.0)
    return bool(np.all(off <= 1e-12)) and n > 0


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
