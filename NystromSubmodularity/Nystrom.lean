import NystromSubmodularity.PrincipalSubmatrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Nyström approximation and nuclear residual

The nuclear-norm Nyström error of \(K=M^{-1}\) is defined in
`PrincipalSubmatrix.nystromError` via Colbrook's identity
\(\mathcal{E}(S)=\operatorname{tr}(M[S^{\mathsf{c}}]^{-1})\). For a
positive-semidefinite residual the nuclear (Schatten-1) norm equals the
trace, so this is exactly \(\|K-\mathcal{N}_S(K)\|_*\).
-/

namespace NystromSubmodularity

open Matrix

/-- Column-selected Nyström approximation \(\mathcal{N}_S(K)=K_{:,S}K_{S,S}^{-1}K_{S,:}\).
The empty-index case is the zero matrix. -/
noncomputable def nystromApprox {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (K : Matrix ι ι R) (S : Finset ι) : Matrix ι ι R :=
  K.submatrix id (Subtype.val : PrincipalIndex S → ι) *
    (principalSubmatrix K S)⁻¹ *
    K.submatrix (Subtype.val : PrincipalIndex S → ι) id

/-- Nyström residual \(K-\mathcal{N}_S(K)\). -/
noncomputable def nystromResidual {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (K : Matrix ι ι R) (S : Finset ι) : Matrix ι ι R :=
  K - nystromApprox K S

/-- Nuclear (Schatten-1) norm. On a positive-semidefinite matrix this equals the
trace (singular values = eigenvalues). All residuals arising from a
positive-definite precision matrix `M` are PSD by Colbrook Theorem 2, so the
identification is the one used throughout the development. -/
noncomputable def nuclearNorm {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) : ℝ :=
  A.trace

theorem nystromApprox_empty {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (K : Matrix ι ι R) : nystromApprox K ∅ = 0 := by
  ext i j
  simp [nystromApprox, Matrix.mul_apply]

theorem nystromResidual_empty {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (K : Matrix ι ι R) : nystromResidual K ∅ = K := by
  simp [nystromResidual, nystromApprox_empty]

/-- SVD-style nuclear error of the residual of \(K=M^{-1}\). Equals `nystromError M`
on the PSD residual of a positive-definite precision matrix. -/
noncomputable def nuclearNystromError {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (S : Finset ι) : ℝ :=
  nuclearNorm (nystromResidual M⁻¹ S)

theorem nuclearNystromError_empty {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) : nuclearNystromError M ∅ = M⁻¹.trace := by
  simp [nuclearNystromError, nuclearNorm, nystromResidual_empty]

theorem trace_reindex_self {ι κ R : Type*} [Fintype ι] [Fintype κ] [AddCommMonoid R]
    (e : ι ≃ κ) (M : Matrix κ κ R) :
    (M.submatrix e e).trace = M.trace := by
  simp [Matrix.trace, Matrix.diag]
  exact Fintype.sum_equiv e (fun i => M (e i) (e i)) (fun k => M k k) fun _ => rfl

end NystromSubmodularity
