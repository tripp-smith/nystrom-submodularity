"""Lean-certified matrices from ``Counterexamples/SDDDim3.lean`` and
``SmallInstanceChecks.lean``. Values are exact rationals as floats;
tests re-check them with ``fractions.Fraction``.
"""

from __future__ import annotations

import numpy as np

# Colbrook L(2) and M = L + I (SDDDim3.lean).
L0 = np.array(
    [[3.0, 1.0, -2.0], [1.0, 3.0, -2.0], [-2.0, -2.0, 4.0]],
    dtype=np.float64,
)
M0 = np.array(
    [[4.0, 1.0, -2.0], [1.0, 4.0, -2.0], [-2.0, -2.0, 5.0]],
    dtype=np.float64,
)
LSHARP = np.array(
    [[4.0, 1.0, -2.0], [1.0, 4.0, -2.0], [-2.0, -2.0, 5.0]],
    dtype=np.float64,
)
MSHARP = np.array(
    [[5.0, 1.0, -2.0], [1.0, 5.0, -2.0], [-2.0, -2.0, 6.0]],
    dtype=np.float64,
)

# Certified nystromError values on M0 (γ = 1 already baked in).
M0_E_EMPTY = 47 / 51
M0_E_ZERO = 9 / 16
M0_E_ONE = 9 / 16
M0_E_ZERO_ONE = 1 / 5
M0_E_ZERO_TWO = 1 / 4
M0_E_ONE_TWO = 1 / 4
M0_CPQR_COL0_NORMSQ = 293 / 2601
M0_CPQR_COL2_NORMSQ = 297 / 2601
M0_CPQR_PAIR_RATIO = 5 / 4
M0_DELTA_EMPTY_ZERO_ONE = -7 / 2040
M0_RATIO_EMPTY_ZERO_ONE = 2288 / 2295

# L^sharp + I certified pair / singleton residuals (Theorems.lean).
MSHARP_E_TWO = 5 / 12
MSHARP_E_ZERO = 11 / 26
MSHARP_E_ZERO_ONE = 1 / 6
MSHARP_E_ZERO_TWO = 1 / 5


def lfam(t: float) -> np.ndarray:
    """Colbrook signed-triangle family ``Lfam t``."""
    return np.array(
        [[t + 1.0, 1.0, -t], [1.0, t + 1.0, -t], [-t, -t, 2.0 * t]],
        dtype=np.float64,
    )


def path_laplacian(n: int) -> np.ndarray:
    """Combinatorial path Laplacian on ``n`` vertices (``pathLap3/4/5``)."""
    if n < 2:
        raise ValueError("path Laplacian needs n >= 2")
    L = np.zeros((n, n), dtype=np.float64)
    for i in range(n - 1):
        L[i, i] += 1.0
        L[i + 1, i + 1] += 1.0
        L[i, i + 1] -= 1.0
        L[i + 1, i] -= 1.0
    return L


def cycle_laplacian(n: int) -> np.ndarray:
    """Combinatorial cycle Laplacian on ``n`` vertices."""
    if n < 3:
        raise ValueError("cycle Laplacian needs n >= 3")
    L = path_laplacian(n)
    L[0, 0] += 1.0
    L[n - 1, n - 1] += 1.0
    L[0, n - 1] -= 1.0
    L[n - 1, 0] -= 1.0
    return L
