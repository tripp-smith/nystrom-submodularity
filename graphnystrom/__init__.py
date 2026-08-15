"""Operational Nyström landmark selection for the Lean formalization.

Lean remains the source of truth. The identities implemented here are
``nystromError``, ``exact_marginal``, and the SDDM / Stieltjes
predicates from ``NystromSubmodularity``.
"""

from graphnystrom.api import (
    GreedyNystromLandmarks,
    GreedyNyströmLandmarks,
    NystromResolvent,
    select_landmarks,
)
from graphnystrom.certified import M0, L0, LSHARP, MSHARP, path_laplacian
from graphnystrom.laplacian import combinatorial_laplacian, from_edges
from graphnystrom.residual import (
    estimate_nystrom_error,
    evaluate_residual,
    exact_marginal_gain,
    four_point_defect,
    nystrom_error,
    precision_matrix,
)
from graphnystrom.signature import is_sddm, is_stieltjes, signature_switch

__all__ = [
    "GreedyNystromLandmarks",
    "GreedyNyströmLandmarks",
    "NystromResolvent",
    "select_landmarks",
    "M0",
    "L0",
    "LSHARP",
    "MSHARP",
    "path_laplacian",
    "combinatorial_laplacian",
    "from_edges",
    "estimate_nystrom_error",
    "evaluate_residual",
    "exact_marginal_gain",
    "four_point_defect",
    "nystrom_error",
    "precision_matrix",
    "is_sddm",
    "is_stieltjes",
    "signature_switch",
]
