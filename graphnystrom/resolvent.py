"""Nyström approximant of the resolvent ``K = M⁻¹``."""

from __future__ import annotations

from collections.abc import Sequence

import numpy as np
from numpy.typing import NDArray
from scipy import sparse
from scipy.sparse.linalg import spsolve

from graphnystrom.residual import as_dense, precision_matrix

Array = NDArray[np.float64]


class NystromResolvent:
    """Column Nyström of ``M⁻¹``: solve ``M X = E_S``, then
    ``N v = X (X[S, :])⁻¹ Xᵀ v``.
    """

    def __init__(
        self,
        laplacian: Array | sparse.spmatrix,
        landmarks: Sequence[int],
        gamma: float = 1.0,
    ) -> None:
        self.landmarks = [int(i) for i in landmarks]
        self.gamma = float(gamma)
        self.M = precision_matrix(laplacian, gamma)
        self.n = self.M.shape[0]
        S = self.landmarks
        if not S:
            self.X = np.zeros((self.n, 0), dtype=np.float64)
            self.small_inv = np.zeros((0, 0), dtype=np.float64)
            return
        E = np.zeros((self.n, len(S)), dtype=np.float64)
        for col, i in enumerate(S):
            E[i, col] = 1.0
        if sparse.issparse(self.M):
            self.X = np.column_stack(
                [np.asarray(spsolve(self.M, E[:, j]), dtype=np.float64) for j in range(len(S))]
            )
        else:
            self.X = np.linalg.solve(as_dense(self.M), E)
        small = self.X[np.ix_(S, range(len(S)))]
        self.small_inv = np.linalg.inv(0.5 * (small + small.T))

    def matvec(self, v: Array) -> Array:
        v = np.asarray(v, dtype=np.float64).reshape(-1)
        if self.X.shape[1] == 0:
            return np.zeros_like(v)
        return self.X @ (self.small_inv @ (self.X.T @ v))

    def as_linear_operator(self):
        from scipy.sparse.linalg import LinearOperator

        return LinearOperator(
            (self.n, self.n),
            matvec=self.matvec,
            rmatvec=self.matvec,
            dtype=np.float64,
        )
