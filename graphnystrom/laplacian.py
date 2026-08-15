"""Graph Laplacians and lightweight generators (Networkit-free)."""

from __future__ import annotations

from collections.abc import Sequence

import numpy as np
from numpy.typing import NDArray
from scipy import sparse

Array = NDArray[np.float64]


def combinatorial_laplacian(
    n: int,
    edges: Sequence[tuple[int, int]] | Sequence[tuple[int, int, float]],
    *,
    sparse_output: bool = False,
) -> Array | sparse.spmatrix:
    """Undirected combinatorial Laplacian from an edge list."""
    rows: list[int] = []
    cols: list[int] = []
    data: list[float] = []
    deg = np.zeros(n, dtype=np.float64)
    for item in edges:
        if len(item) == 2:
            u, v = int(item[0]), int(item[1])
            w = 1.0
        else:
            u, v, w = int(item[0]), int(item[1]), float(item[2])
        if u == v:
            continue
        rows.extend([u, v])
        cols.extend([v, u])
        data.extend([-w, -w])
        deg[u] += w
        deg[v] += w
    off = sparse.csr_matrix((data, (rows, cols)), shape=(n, n))
    L = sparse.diags(deg) + off
    L = 0.5 * (L + L.T)
    if sparse_output:
        return L.tocsr()
    return np.asarray(L.toarray(), dtype=np.float64)


def from_edges(
    n: int, edges: Sequence[tuple[int, int]] | Sequence[tuple[int, int, float]]
) -> Array:
    return combinatorial_laplacian(n, edges, sparse_output=False)  # type: ignore[return-value]


def grid_laplacian(rows: int, cols: int) -> Array:
    """4-neighbour grid Laplacian."""
    n = rows * cols
    edges: list[tuple[int, int]] = []

    def vid(r: int, c: int) -> int:
        return r * cols + c

    for r in range(rows):
        for c in range(cols):
            if c + 1 < cols:
                edges.append((vid(r, c), vid(r, c + 1)))
            if r + 1 < rows:
                edges.append((vid(r, c), vid(r + 1, c)))
    return from_edges(n, edges)


def erdos_renyi(n: int, p: float, seed: int = 0) -> Array:
    rng = np.random.default_rng(seed)
    edges: list[tuple[int, int]] = []
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < p:
                edges.append((i, j))
    return from_edges(n, edges)


def barabasi_albert(n: int, m: int, seed: int = 0) -> Array:
    if m < 1 or n <= m:
        raise ValueError("need 1 <= m < n")
    rng = np.random.default_rng(seed)
    edges: list[tuple[int, int]] = []
    targets = list(range(m))
    for u in range(m, n):
        chosen = set()
        # Preferential attachment with replacement rejection.
        deg = np.ones(u, dtype=np.float64)
        for a, b in edges:
            deg[a] += 1.0
            deg[b] += 1.0
        probs = deg / deg.sum()
        while len(chosen) < m:
            v = int(rng.choice(u, p=probs))
            chosen.add(v)
        for v in chosen:
            edges.append((v, u))
        targets = list(chosen)
    _ = targets
    return from_edges(n, edges)


def as_laplacian(graph: Array | sparse.spmatrix | object) -> Array | sparse.spmatrix:
    """Accept a Laplacian matrix, adjacency matrix, or optional NetworkX graph."""
    nx = _try_networkx(graph)
    if nx is not None:
        return nx
    nk = _try_networkit(graph)
    if nk is not None:
        return nk
    if sparse.issparse(graph) or isinstance(graph, np.ndarray):
        M = graph
        dense = M.toarray() if sparse.issparse(M) else np.asarray(M, dtype=np.float64)
        off_pos = np.any(np.triu(dense, 1) > 1e-12)
        diag_dom = np.all(np.diag(dense) + 1e-12 >= np.sum(np.abs(dense), axis=1) - np.abs(np.diag(dense)))
        if off_pos and not diag_dom:
            # Treat as adjacency: L = D - A.
            A = 0.5 * (dense + dense.T)
            np.fill_diagonal(A, 0.0)
            deg = A.sum(axis=1)
            L = np.diag(deg) - A
            return L
        return M
    raise TypeError(f"unsupported graph type: {type(graph)!r}")


def _try_networkx(graph: object) -> Array | None:
    try:
        import networkx as nx  # type: ignore
    except ImportError:
        return None
    if isinstance(graph, nx.Graph):
        n = graph.number_of_nodes()
        nodes = list(graph.nodes())
        index = {u: i for i, u in enumerate(nodes)}
        edges = []
        for u, v, data in graph.edges(data=True):
            w = float(data.get("weight", 1.0))
            edges.append((index[u], index[v], w))
        return from_edges(n, edges)
    return None


def _try_networkit(graph: object) -> Array | None:
    try:
        import networkit as nk  # type: ignore
    except ImportError:
        return None
    if graph.__class__.__module__.startswith("networkit") and hasattr(graph, "iterEdges"):
        n = graph.numberOfNodes()
        edges = []
        weighted = graph.isWeighted()
        for u, v, w in graph.iterEdgesWeights() if weighted else (
            (a, b, 1.0) for a, b in graph.iterEdges()
        ):
            edges.append((int(u), int(v), float(w)))
        return from_edges(n, edges)
    return None
