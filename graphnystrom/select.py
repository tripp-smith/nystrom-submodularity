"""Greedy, lazy, stochastic, and approximate landmark selectors."""

from __future__ import annotations

import heapq
from collections.abc import Sequence
from dataclasses import dataclass

import numpy as np
from numpy.typing import NDArray
from scipy import sparse

from graphnystrom.residual import (
    all_marginal_gains,
    as_dense,
    exact_marginal_gain,
    hutchinson_diagonal,
    nystrom_error,
    schur_delete,
    sparse_column_gain,
)
from graphnystrom.signature import is_sddm

Array = NDArray[np.float64]

ONE_MINUS_1_E = 1.0 - 1.0 / np.e


@dataclass
class SelectionResult:
    landmarks: list[int]
    gains: list[float]
    residual: float
    guarantee: float | None
    mode: str


def greedy_exact(M: Array, k: int) -> SelectionResult:
    n = M.shape[0]
    k = min(k, n)
    inv = np.linalg.inv(as_dense(M))
    inv = 0.5 * (inv + inv.T)
    remaining = list(range(n))
    landmarks: list[int] = []
    gains: list[float] = []
    energy = float(np.trace(inv))
    for _ in range(k):
        scores = all_marginal_gains(inv)
        j = int(np.argmax(scores))
        gain = float(scores[j])
        landmarks.append(remaining.pop(j))
        gains.append(gain)
        energy -= gain
        inv = schur_delete(inv, j)
    residual = max(energy, 0.0) if k < n else 0.0
    return SelectionResult(landmarks, gains, residual, None, "exact")


def greedy_lazy(M: Array, k: int) -> SelectionResult:
    """Lazy greedy: stale gains are upper bounds when ``ℰ`` is supermodular."""
    n = M.shape[0]
    k = min(k, n)
    inv = np.linalg.inv(as_dense(M))
    inv = 0.5 * (inv + inv.T)
    remaining = list(range(n))
    pos = {node: i for i, node in enumerate(remaining)}
    scores = all_marginal_gains(inv)
    heap = [(-float(scores[i]), node, 0) for i, node in enumerate(remaining)]
    heapq.heapify(heap)
    landmarks: list[int] = []
    gains: list[float] = []
    energy = float(np.trace(inv))
    version = 0
    for _ in range(k):
        while True:
            neg, node, ver = heapq.heappop(heap)
            if node not in pos:
                continue
            if ver == version:
                j = pos[node]
                gain = -neg
                break
            j = pos[node]
            gain = exact_marginal_gain(inv, j)
            heapq.heappush(heap, (-gain, node, version))
        landmarks.append(node)
        gains.append(float(gain))
        energy -= float(gain)
        inv = schur_delete(inv, j)
        remaining.pop(j)
        pos = {node2: i for i, node2 in enumerate(remaining)}
        version += 1
        # Refresh the new top if the heap is empty of live nodes.
        if remaining and not heap:
            scores = all_marginal_gains(inv)
            heap = [(-float(scores[i]), node2, version) for i, node2 in enumerate(remaining)]
            heapq.heapify(heap)
    residual = max(energy, 0.0) if k < n else 0.0
    return SelectionResult(landmarks, gains, residual, None, "lazy")


def greedy_stochastic(
    M: Array | sparse.spmatrix, k: int, *, sample: int = 16, seed: int = 0
) -> SelectionResult:
    """Exact gain on a random candidate subset (no 1-1/e claim)."""
    n = M.shape[0]
    k = min(k, n)
    rng = np.random.default_rng(seed)
    remaining = list(range(n))
    landmarks: list[int] = []
    gains: list[float] = []
    S: list[int] = []
    dense = not sparse.issparse(M)
    inv = np.linalg.inv(as_dense(M)) if dense else None
    if inv is not None:
        inv = 0.5 * (inv + inv.T)
    for _ in range(k):
        m = min(sample, len(remaining))
        cand_idx = rng.choice(len(remaining), size=m, replace=False)
        best_j = int(cand_idx[0])
        best_gain = -np.inf
        for loc in cand_idx:
            loc = int(loc)
            if inv is not None:
                gain = exact_marginal_gain(inv, loc)
            else:
                C = remaining
                gain = sparse_column_gain(M, C, loc)
            if gain > best_gain:
                best_gain = gain
                best_j = loc
        node = remaining.pop(best_j)
        landmarks.append(node)
        gains.append(float(best_gain))
        S.append(node)
        if inv is not None:
            inv = schur_delete(inv, best_j)
    residual = nystrom_error(M, landmarks)
    return SelectionResult(landmarks, gains, residual, None, "stochastic")


def greedy_approx(
    M: Array | sparse.spmatrix, k: int, *, probes: int = 12, seed: int = 0
) -> SelectionResult:
    """Static Hutchinson diagonal scores (leverage heuristic)."""
    n = M.shape[0]
    k = min(k, n)
    scores = hutchinson_diagonal(M, probes=probes, seed=seed)
    order = np.argsort(-scores)
    landmarks = [int(i) for i in order[:k]]
    residual = nystrom_error(M, landmarks)
    return SelectionResult(landmarks, [], residual, None, "approx")


def uniform_sample(n: int, k: int, seed: int = 0) -> list[int]:
    rng = np.random.default_rng(seed)
    k = min(k, n)
    return [int(i) for i in rng.choice(n, size=k, replace=False)]


def leverage_sample(
    M: Array | sparse.spmatrix, k: int, *, probes: int = 12, seed: int = 0
) -> list[int]:
    scores = np.maximum(hutchinson_diagonal(M, probes=probes, seed=seed), 0.0)
    if scores.sum() <= 0:
        return uniform_sample(M.shape[0], k, seed=seed)
    rng = np.random.default_rng(seed)
    k = min(k, M.shape[0])
    p = scores / scores.sum()
    return [int(i) for i in rng.choice(M.shape[0], size=k, replace=False, p=p)]


def attach_guarantee(result: SelectionResult, M: Array | sparse.spmatrix) -> SelectionResult:
    result.guarantee = ONE_MINUS_1_E if is_sddm(M) else None
    return result
