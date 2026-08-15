import NystromSubmodularity.Nystrom
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.Data.Multiset.Sort
import Mathlib.Tactic.Linarith

/-!
# Hermitian nuclear-norm API

Mathlib’s spectral theorem supplies eigenvalues of a Hermitian matrix.
The nuclear (Schatten-1) norm of a Hermitian matrix is
\(\sum_i|\lambda_i|\). On a positive-semidefinite matrix the eigenvalues
are nonnegative, so this coincides with the trace — the identification
used by `nuclearNorm` throughout the library.

`matrixSingularValues` wraps `LinearMap.singularValues` on
`toEuclideanLin`. For a PSD matrix the singular-value sum equals that
Hermitian nuclear norm, so Nyström error is a singular-value sum.
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

/-! ## `LinearMap.singularValues` wrapper -/

open Polynomial

/-- Singular values of a real square matrix, via mathlib’s
`LinearMap.singularValues` on `toEuclideanLin`. -/
noncomputable def matrixSingularValues {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : ℕ →₀ ℝ :=
  A.toEuclideanLin.singularValues

theorem matrixSingularValues_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (i : ℕ) : 0 ≤ matrixSingularValues A i :=
  A.toEuclideanLin.singularValues_nonneg i

theorem matrixSingularValues_eq_zero_of_card_le {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) {i : ℕ} (hi : Fintype.card n ≤ i) :
    matrixSingularValues A i = 0 := by
  have : Module.finrank ℝ (EuclideanSpace ℝ n) ≤ i := by
    simpa [finrank_euclideanSpace] using hi
  exact A.toEuclideanLin.singularValues_of_finrank_le this

/-- For a real symmetric map the Gram characteristic polynomial is
the product over squared eigenvalues. -/
lemma charpoly_adjoint_comp_self_of_isSymmetric {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E}
    (hT : T.IsSymmetric) {n : ℕ} (hn : Module.finrank ℝ E = n) :
    (T.adjoint ∘ₗ T).charpoly =
      ∏ j : Fin n, (X - C ((hT.eigenvalues hn j) ^ 2 : ℝ)) := by
  have hcomp : T.adjoint ∘ₗ T = T.comp T := by rw [hT.adjoint_eq]
  let b := (hT.eigenvectorBasis hn).toBasis
  have hmat : LinearMap.toMatrix b b (T.comp T) =
      diagonal fun j : Fin n => (hT.eigenvalues hn j : ℝ) ^ 2 := by
    rw [LinearMap.toMatrix_comp (v₁ := b) (v₂ := b) (v₃ := b),
      hT.toMatrix_eigenvectorBasis, diagonal_mul_diagonal]
    ext i j
    simp [pow_two]
  rw [hcomp, ← LinearMap.charpoly_toMatrix (T.comp T) b, hmat, charpoly_diagonal]

/-- Gram eigenvalues and squared eigenvalues agree as multisets. -/
lemma multiset_eigenvalues_adjoint_comp_self {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E}
    (hT : T.IsSymmetric) {n : ℕ} (hn : Module.finrank ℝ E = n) :
    Finset.univ.val.map (T.isSymmetric_adjoint_comp_self.eigenvalues hn) =
      Finset.univ.val.map fun i : Fin n => (hT.eigenvalues hn i) ^ 2 := by
  have hchar := charpoly_adjoint_comp_self_of_isSymmetric hT hn
  have hrMu := T.isSymmetric_adjoint_comp_self.roots_charpoly_eq_eigenvalues hn
  have hrSq : (T.adjoint ∘ₗ T).charpoly.roots =
      Finset.univ.val.map fun i : Fin n => ((hT.eigenvalues hn i) ^ 2 : ℝ) := by
    rw [hchar, Finset.prod_eq_multiset_prod]
    have hmap : (Finset.univ.val.map fun j : Fin n =>
        (X - C ((hT.eigenvalues hn j) ^ 2 : ℝ))) =
        (Finset.univ.val.map fun j : Fin n => (hT.eigenvalues hn j) ^ 2).map
          fun a : ℝ => X - C a := by
      rw [Multiset.map_map]
      rfl
    rw [hmap, roots_multiset_prod_X_sub_C]
  have hReμ : ((T.adjoint ∘ₗ T).charpoly.roots.map RCLike.re) =
      Finset.univ.val.map (T.isSymmetric_adjoint_comp_self.eigenvalues hn) := by
    rw [hrMu, Multiset.map_map]
    simp [Function.comp]
  have hReSq : ((T.adjoint ∘ₗ T).charpoly.roots.map RCLike.re) =
      Finset.univ.val.map fun i : Fin n => (hT.eigenvalues hn i) ^ 2 := by
    rw [hrSq, Multiset.map_map]
    simp [Function.comp]
  exact hReμ.symm.trans hReSq

/-- On a positive map the Gram eigenvalues are the squares of the
already nonnegative, decreasing eigenvalues. -/
lemma eigenvalues_adjoint_comp_self_eq_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E}
    (hT : T.IsPositive) {n : ℕ} (hn : Module.finrank ℝ E = n) (i : Fin n) :
    T.isSymmetric_adjoint_comp_self.eigenvalues hn i =
      (hT.isSymmetric.eigenvalues hn i) ^ 2 := by
  have hanti : Antitone fun j : Fin n => (hT.isSymmetric.eigenvalues hn j) ^ 2 := by
    intro a c hac
    exact (sq_le_sq₀ (hT.nonneg_eigenvalues hn c) (hT.nonneg_eigenvalues hn a)).mpr
      (hT.isSymmetric.eigenvalues_antitone hn hac)
  have hchar := charpoly_adjoint_comp_self_of_isSymmetric hT.isSymmetric hn
  have hlist :
      List.ofFn (T.isSymmetric_adjoint_comp_self.eigenvalues hn) =
        List.ofFn fun j : Fin n => (hT.isSymmetric.eigenvalues hn j) ^ 2 := by
    rw [← T.isSymmetric_adjoint_comp_self.sort_roots_charpoly_eq_eigenvalues hn, hchar]
    have hroots := roots_multiset_prod_X_sub_C
      (Finset.univ.val.map fun j : Fin n => (hT.isSymmetric.eigenvalues hn j) ^ 2)
    have hprod : (∏ j : Fin n, (X - C ((hT.isSymmetric.eigenvalues hn j) ^ 2 : ℝ))) =
        (Finset.univ.val.map fun j : Fin n =>
          (X - C ((hT.isSymmetric.eigenvalues hn j) ^ 2 : ℝ))).prod :=
      Finset.prod_eq_multiset_prod _ _
    have hmap : (Finset.univ.val.map fun j : Fin n =>
        (X - C ((hT.isSymmetric.eigenvalues hn j) ^ 2 : ℝ))) =
        (Finset.univ.val.map fun j : Fin n =>
          (hT.isSymmetric.eigenvalues hn j) ^ 2).map fun a : ℝ => X - C a := by
      rw [Multiset.map_map]
      rfl
    rw [hprod, hmap, hroots, Fin.univ_val_map, Multiset.map_coe, List.map_ofFn, Multiset.coe_sort]
    exact List.mergeSort_eq_self (r := (· ≥ ·))
      (List.sortedGE_iff_pairwise.mp hanti.sortedGE_ofFn)
  exact congrFun (List.ofFn_inj.mp hlist) i

theorem matrixSingularValues_eq_abs_eigenvalue_of_posSemidef {n : Type*}
    [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosSemidef)
    (i : Fin (Fintype.card n)) :
    matrixSingularValues A i = |hA.1.eigenvalues₀ i| := by
  have hT : A.toEuclideanLin.IsPositive := Matrix.isPositive_toEuclideanLin_iff.mpr hA
  have hn : Module.finrank ℝ (EuclideanSpace ℝ n) = Fintype.card n := finrank_euclideanSpace
  have hsq := eigenvalues_adjoint_comp_self_eq_sq hT hn i
  have hσ := A.toEuclideanLin.singularValues_fin hn i
  have hEig0 : hA.1.eigenvalues₀ i = hT.isSymmetric.eigenvalues hn i := rfl
  have hnonneg := hT.nonneg_eigenvalues hn i
  rw [matrixSingularValues, hσ, hsq, hEig0, Real.sqrt_sq hnonneg, abs_of_nonneg hnonneg]

/-- On every real Hermitian matrix the singular-value sum equals the
sum of absolute eigenvalues. -/
theorem sum_matrixSingularValues_eq_hermitianNuclearNorm {n : Type*}
    [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    ∑ i ∈ Finset.range (Fintype.card n), matrixSingularValues A i =
      hermitianNuclearNorm A hA := by
  unfold hermitianNuclearNorm
  have hT : A.toEuclideanLin.IsSymmetric := isSymmetric_toEuclideanLin_iff.mpr hA
  have hn : Module.finrank ℝ (EuclideanSpace ℝ n) = Fintype.card n := finrank_euclideanSpace
  have hμ := multiset_eigenvalues_adjoint_comp_self hT finrank_euclideanSpace
  rw [Finset.sum_range]
  have hσsum :
      ∑ i : Fin (Fintype.card n), matrixSingularValues A i =
        ∑ i : Fin (Fintype.card n),
          Real.sqrt
            (A.toEuclideanLin.isSymmetric_adjoint_comp_self.eigenvalues
              finrank_euclideanSpace i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [matrixSingularValues, A.toEuclideanLin.singularValues_fin finrank_euclideanSpace]
  rw [hσsum]
  have hsumSq :
      ∑ i : Fin (Fintype.card n),
          Real.sqrt
            (A.toEuclideanLin.isSymmetric_adjoint_comp_self.eigenvalues
              finrank_euclideanSpace i) =
        ∑ i : Fin (Fintype.card n), |hA.eigenvalues₀ i| := by
    rw [Finset.sum_eq_multiset_sum, Finset.sum_eq_multiset_sum]
    refine congrArg Multiset.sum ?_
    have hL :
        (Finset.univ.val.map fun i : Fin (Fintype.card n) =>
            Real.sqrt
              (A.toEuclideanLin.isSymmetric_adjoint_comp_self.eigenvalues
                finrank_euclideanSpace i)) =
          (Finset.univ.val.map
              (A.toEuclideanLin.isSymmetric_adjoint_comp_self.eigenvalues
                finrank_euclideanSpace)).map
            Real.sqrt := by
      rw [Multiset.map_map]
      rfl
    rw [hL, hμ]
    have hR :
        (Finset.univ.val.map fun i : Fin (Fintype.card n) =>
            (hT.eigenvalues finrank_euclideanSpace i) ^ 2).map Real.sqrt =
          Finset.univ.val.map fun i : Fin (Fintype.card n) => |hA.eigenvalues₀ i| := by
      rw [Multiset.map_map]
      simp [Function.comp, Real.sqrt_sq_eq_abs, IsHermitian.eigenvalues₀]
    exact hR
  rw [hsumSq]
  let e := Fintype.equivOfCardEq (α := Fin (Fintype.card n)) (β := n) (Fintype.card_fin _)
  refine Fintype.sum_equiv e (fun i => |hA.eigenvalues₀ i|)
    (fun j => |hA.eigenvalues j|) ?_
  intro i
  simp [IsHermitian.eigenvalues, e]

/-- On a PSD matrix the library nuclear norm is the singular-value sum. -/
theorem nuclearNorm_eq_sum_matrixSingularValues {n : Type*} [Fintype n]
    [DecidableEq n] {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    nuclearNorm A = ∑ i ∈ Finset.range (Fintype.card n), matrixSingularValues A i := by
  rw [nuclearNorm_eq_hermitianNuclearNorm hA,
    sum_matrixSingularValues_eq_hermitianNuclearNorm hA.1]

/-- Nyström error is the singular-value sum of the complementary inverse. -/
theorem nystromError_eq_sum_matrixSingularValues_compl {ι : Type*} [Fintype ι]
    [DecidableEq ι] {M : Matrix ι ι ℝ} (hM : M.PosDef) (S : Finset ι) :
    nystromError M S =
      ∑ i ∈ Finset.range (Fintype.card (PrincipalIndex (compl S))),
        matrixSingularValues (principalSubmatrix M (compl S))⁻¹ i := by
  have hP : (principalSubmatrix M (compl S)).PosDef :=
    hM.submatrix Subtype.val_injective
  have hInv : ((principalSubmatrix M (compl S))⁻¹).PosSemidef := hP.inv.posSemidef
  rw [nystromError, traceInv, ← nuclearNorm_eq_sum_matrixSingularValues hInv]
  rfl

end NystromSubmodularity
