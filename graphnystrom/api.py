"""Networkit-style public API."""

from __future__ import annotations

from collections.abc import Sequence

import numpy as np
from numpy.typing import NDArray
from scipy import sparse

from graphnystrom.laplacian import as_laplacian
from graphnystrom.residual import precision_matrix
from graphnystrom.resolvent import NystromResolvent
from graphnystrom.select import (
    SelectionResult,
    attach_guarantee,
    greedy_approx,
    greedy_exact,
    greedy_lazy,
    greedy_stochastic,
    leverage_sample,
    uniform_sample,
)

Array = NDArray[np.float64]


class GreedyNystromLandmarks:
    """Greedy landmark selector. Call ``run()``, then the getters."""

    def __init__(
        self,
        graph: Array | sparse.spmatrix | object,
        k: int,
        gamma: float = 1.0,
        mode: str = "exact",
        criterion: str = "nuclear",
        n_threads: int | None = None,
        seed: int = 42,
        precision: Array | sparse.spmatrix | None = None,
    ) -> None:
        if criterion != "nuclear":
            raise ValueError(
                "only criterion='nuclear' is implemented; see OtherLosses.lean"
            )
        if mode not in {"exact", "lazy", "stochastic", "approx"}:
            raise ValueError(f"unknown mode {mode!r}")
        self.k = int(k)
        self.gamma = float(gamma)
        self.mode = mode
        self.seed = int(seed)
        self.n_threads = n_threads
        if precision is not None:
            self.laplacian = None
            self.M = precision
        else:
            self.laplacian = as_laplacian(graph)
            self.M = precision_matrix(self.laplacian, gamma)
        self._result: SelectionResult | None = None

    def run(self) -> GreedyNystromLandmarks:
        M = self.M
        k = self.k
        if self.mode == "exact":
            result = greedy_exact(np.asarray(M if not sparse.issparse(M) else M.toarray()), k)
        elif self.mode == "lazy":
            result = greedy_lazy(np.asarray(M if not sparse.issparse(M) else M.toarray()), k)
        elif self.mode == "stochastic":
            result = greedy_stochastic(M, k, seed=self.seed)
        else:
            result = greedy_approx(M, k, seed=self.seed)
        self._result = attach_guarantee(result, M)
        return self

    def _need(self) -> SelectionResult:
        if self._result is None:
            raise RuntimeError("call run() before reading results")
        return self._result

    def getLandmarks(self) -> list[int]:
        return list(self._need().landmarks)

    def getMarginalGains(self) -> list[float]:
        return list(self._need().gains)

    def getGuarantee(self) -> float | None:
        return self._need().guarantee

    def getResidual(self) -> float:
        return self._need().residual


GreedyNyströmLandmarks = GreedyNystromLandmarks


def select_landmarks(
    graph: Array | sparse.spmatrix | object,
    k: int,
    gamma: float = 1.0,
    mode: str = "exact",
    seed: int = 42,
    baseline: str | None = None,
    precision: Array | sparse.spmatrix | None = None,
) -> list[int]:
    """Convenience wrapper. ``baseline`` is ``uniform`` or ``leverage``."""
    if precision is not None:
        M = precision
    else:
        M = precision_matrix(as_laplacian(graph), gamma)
    if baseline == "uniform":
        return uniform_sample(M.shape[0], k, seed=seed)
    if baseline == "leverage":
        return leverage_sample(M, k, seed=seed)
    sel = GreedyNystromLandmarks(
        graph, k, gamma=gamma, mode=mode, seed=seed, precision=precision
    )
    sel.run()
    return sel.getLandmarks()
