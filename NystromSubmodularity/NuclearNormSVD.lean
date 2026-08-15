import NystromSubmodularity.Nystrom
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Hermitian nuclear-norm API

Mathlib’s spectral theorem supplies eigenvalues of a Hermitian matrix.
The nuclear (Schatten-1) norm of a Hermitian matrix is
\(\sum_i|\lambda_i|\). On a positive-semidefinite matrix the eigenvalues
are nonnegative, so this coincides with the trace — the identification
used by `nuclearNorm` throughout the library.
-/

namespace NystromSubmodularity

open Matrix Finset

/-- Nuclear (Schatten-1) norm of a Hermitian matrix: sum of absolute
eigenvalues. -/
noncomputable def hermitianNuclearNorm {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) : ℝ :=
  ∑ i : n, |hA.eigenvalues i|

/-- On a PSD matrix the Hermitian nuclear norm equals the trace. -/
theorem hermitianNuclearNorm_eq_trace_of_posSemidef {n : Type*} [Fintype n]
    [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    hermitianNuclearNorm A hA.1 = A.trace := by
  unfold hermitianNuclearNorm
  have htr := Matrix.IsHermitian.trace_eq_sum_eigenvalues (𝕜 := ℝ) hA.1
  rw [htr]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact abs_of_nonneg (hA.eigenvalues_nonneg i)

/-- The library `nuclearNorm` (trace) agrees with the eigenvalue definition
on every PSD matrix. -/
theorem nuclearNorm_eq_hermitianNuclearNorm {n : Type*} [Fintype n]
    [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    nuclearNorm A = hermitianNuclearNorm A hA.1 :=
  (hermitianNuclearNorm_eq_trace_of_posSemidef hA).symm

/-- Nyström error is the Hermitian nuclear norm of the complementary
principal inverse. -/
theorem nystromError_eq_hermitianNuclearNorm_compl {ι : Type*} [Fintype ι]
    [DecidableEq ι] {M : Matrix ι ι ℝ} (hM : M.PosDef) (S : Finset ι) :
    nystromError M S =
      hermitianNuclearNorm (principalSubmatrix M (compl S))⁻¹
        (hM.submatrix Subtype.val_injective).inv.isHermitian := by
  have hP : (principalSubmatrix M (compl S)).PosDef :=
    hM.submatrix Subtype.val_injective
  have hInv : ((principalSubmatrix M (compl S))⁻¹).PosSemidef := hP.inv.posSemidef
  rw [nystromError, traceInv, ← hermitianNuclearNorm_eq_trace_of_posSemidef hInv]

end NystromSubmodularity
