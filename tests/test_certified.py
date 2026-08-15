"""Lean-certified rationals. Independent Fraction check included."""

from __future__ import annotations

from fractions import Fraction

import numpy as np
import pytest

from graphnystrom import (
    M0,
    L0,
    MSHARP,
    four_point_defect,
    is_sddm,
    nystrom_error,
    path_laplacian,
    signature_switch,
)
from graphnystrom.certified import (
    M0_DELTA_EMPTY_ZERO_ONE,
    M0_E_EMPTY,
    M0_E_ONE,
    M0_E_ZERO,
    M0_E_ZERO_ONE,
    M0_RATIO_EMPTY_ZERO_ONE,
    MSHARP_E_TWO,
    MSHARP_E_ZERO,
    MSHARP_E_ZERO_ONE,
    MSHARP_E_ZERO_TWO,
    lfam,
)
from graphnystrom.signature import is_sdd as is_sdd_sig
from graphnystrom.signature import is_stieltjes


def _inv_trace_fraction(M: list[list[int]], S: set[int]) -> Fraction:
    n = len(M)
    C = [i for i in range(n) if i not in S]
    if not C:
        return Fraction(0)
    A = [[Fraction(M[i][j]) for j in C] for i in C]
    # 1×1 / 2×2 / 3×3 inverse-trace via adjugate.
    m = len(C)
    if m == 1:
        return 1 / A[0][0]
    if m == 2:
        det = A[0][0] * A[1][1] - A[0][1] * A[1][0]
        return (A[0][0] + A[1][1]) / det
    if m == 3:
        det = (
            A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1])
            - A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0])
            + A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0])
        )
        # tr(adj)/det
        c00 = A[1][1] * A[2][2] - A[1][2] * A[2][1]
        c11 = A[0][0] * A[2][2] - A[0][2] * A[2][0]
        c22 = A[0][0] * A[1][1] - A[0][1] * A[1][0]
        return (c00 + c11 + c22) / det
    raise NotImplementedError


def test_m0_certified_values() -> None:
    assert nystrom_error(M0, []) == pytest.approx(M0_E_EMPTY, rel=1e-12)
    assert nystrom_error(M0, [0]) == pytest.approx(M0_E_ZERO, rel=1e-12)
    assert nystrom_error(M0, [1]) == pytest.approx(M0_E_ONE, rel=1e-12)
    assert nystrom_error(M0, [0, 1]) == pytest.approx(M0_E_ZERO_ONE, rel=1e-12)
    delta = four_point_defect(M0, [], 0, 1)
    assert delta == pytest.approx(M0_DELTA_EMPTY_ZERO_ONE, rel=1e-12)
    assert delta < 0
    num = nystrom_error(M0, []) + nystrom_error(M0, [0, 1])
    den = nystrom_error(M0, [0]) + nystrom_error(M0, [1])
    assert num / den == pytest.approx(M0_RATIO_EMPTY_ZERO_ONE, rel=1e-12)


def test_m0_independent_fraction() -> None:
    M = [[4, 1, -2], [1, 4, -2], [-2, -2, 5]]
    empty = _inv_trace_fraction(M, set())
    e0 = _inv_trace_fraction(M, {0})
    e1 = _inv_trace_fraction(M, {1})
    e01 = _inv_trace_fraction(M, {0, 1})
    assert empty == Fraction(47, 51)
    assert e0 == Fraction(9, 16)
    assert e1 == Fraction(9, 16)
    assert e01 == Fraction(1, 5)
    delta = empty + e01 - e0 - e1
    assert delta == Fraction(-7, 2040)
    assert empty + e01 == Fraction(2288, 2295) * (e0 + e1)


def test_l0_is_sdd_not_sddm() -> None:
    assert is_sdd_sig(L0)
    assert not is_sddm(L0)
    assert not is_sddm(M0)


def test_msharp_certified() -> None:
    assert nystrom_error(MSHARP, [2]) == pytest.approx(MSHARP_E_TWO, rel=1e-12)
    assert nystrom_error(MSHARP, [0]) == pytest.approx(MSHARP_E_ZERO, rel=1e-12)
    assert nystrom_error(MSHARP, [0, 1]) == pytest.approx(MSHARP_E_ZERO_ONE, rel=1e-12)
    assert nystrom_error(MSHARP, [0, 2]) == pytest.approx(MSHARP_E_ZERO_TWO, rel=1e-12)


def test_lfam_matches_l0_at_two() -> None:
    assert np.allclose(lfam(2.0), L0)


def test_path_is_sddm_and_stieltjes_after_ridge() -> None:
    L = path_laplacian(3)
    assert is_sddm(L + np.eye(3))
    assert is_stieltjes(L + np.eye(3))
    M = L + np.eye(3)
    assert four_point_defect(M, [], 0, 1) >= -1e-12


def test_signature_flip_path() -> None:
    M = path_laplacian(3) + np.eye(3)
    flipped = signature_switch(M, [1, 1, -1])
    # Congruence preserves principal inverse-traces.
    assert nystrom_error(flipped, []) == pytest.approx(nystrom_error(M, []), rel=1e-12)
    assert nystrom_error(flipped, [0]) == pytest.approx(nystrom_error(M, [0]), rel=1e-12)
    # A second flip restores the Stieltjes matrix (Signature.lean sanity).
    restored = signature_switch(flipped, [1, 1, -1])
    assert np.allclose(restored, M)
    assert is_stieltjes(restored)
