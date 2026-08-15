import NystromSubmodularity.NuclearNormSVD
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

/-!
# Schur complements and block-diagonal nuclear norms

Schur positivity (`schurComplement_posDef`, `schurComplement₂₂_posDef`)
lives in `Stieltjes.lean`. The inverse-block identity
`schur_of_inv_eq_compl_inv` lives in `Nystrom.lean`. This module
re-exports those names and adds the block-diagonal nuclear identities
that sit next to them: a Hermitian (resp. PSD) pair of blocks remains
Hermitian (resp. PSD) on the diagonal embedding, and the nuclear /
Schatten-1 mass adds.
-/

namespace NystromSubmodularity

open Matrix Finset Polynomial

/-- Re-export: the Schur complement of a PD block matrix is PD. -/
abbrev schurComplement_posDef_reexport := @schurComplement_posDef

/-- Re-export: the complementary Schur complement is PD. -/
abbrev schurComplement₂₂_posDef_reexport := @schurComplement₂₂_posDef

/-- Re-export: the Schur complement of \(M^{-1}\) recovers \(D^{-1}\). -/
abbrev schur_of_inv_eq_compl_inv_reexport := @schur_of_inv_eq_compl_inv

theorem isHermitian_fromBlocks_diagonal {m n : Type*}
    {A : Matrix m m ℝ} {D : Matrix n n ℝ}
    (hA : A.IsHermitian) (hD : D.IsHermitian) :
    (fromBlocks A (0 : Matrix m n ℝ) 0 D).IsHermitian :=
  IsHermitian.fromBlocks hA (by simp) hD

lemma star_dotProduct_sumElim {m n : Type*} [Fintype m] [Fintype n]
    (x : m ⊕ n → ℝ) (u : m → ℝ) (v : n → ℝ) :
    star x ⬝ᵥ Sum.elim u v =
      star (x ∘ Sum.inl) ⬝ᵥ u + star (x ∘ Sum.inr) ⬝ᵥ v := by
  simp [dotProduct, Fintype.sum_sum_type]

theorem fromBlocks_diagonal_posSemidef {m n : Type*} [Fintype m] [Fintype n]
    {A : Matrix m m ℝ} {D : Matrix n n ℝ}
    (hA : A.PosSemidef) (hD : D.PosSemidef) :
    (fromBlocks A (0 : Matrix m n ℝ) 0 D).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg
    (isHermitian_fromBlocks_diagonal hA.1 hD.1) fun x => ?_
  rw [fromBlocks_mulVec, star_dotProduct_sumElim]
  simp only [zero_mulVec, add_zero, zero_add]
  exact add_nonneg (hA.dotProduct_mulVec_nonneg _) (hD.dotProduct_mulVec_nonneg _)

lemma abs_roots_eq_sum_abs_eigenvalues {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (Multiset.map (fun t : ℝ => |t|) (A.charpoly.roots.map RCLike.re)).sum =
      ∑ i : n, |hA.eigenvalues i| := by
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.map_map, Multiset.map_map,
    Finset.sum_eq_multiset_sum]
  simp [Function.comp]

theorem hermitianNuclearNorm_fromBlocks_diagonal {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {A : Matrix m m ℝ} {D : Matrix n n ℝ}
    (hA : A.IsHermitian) (hD : D.IsHermitian) :
    hermitianNuclearNorm (fromBlocks A (0 : Matrix m n ℝ) 0 D)
      (isHermitian_fromBlocks_diagonal hA hD) =
      hermitianNuclearNorm A hA + hermitianNuclearNorm D hD := by
  let hBlk := isHermitian_fromBlocks_diagonal hA hD
  unfold hermitianNuclearNorm
  have hchar :
      (fromBlocks A (0 : Matrix m n ℝ) 0 D).charpoly = A.charpoly * D.charpoly :=
    charpoly_fromBlocks_zero₁₂ A 0 D
  have hmul : A.charpoly * D.charpoly ≠ 0 :=
    mul_ne_zero A.charpoly_monic.ne_zero D.charpoly_monic.ne_zero
  rw [← abs_roots_eq_sum_abs_eigenvalues hBlk, ← abs_roots_eq_sum_abs_eigenvalues hA,
    ← abs_roots_eq_sum_abs_eigenvalues hD, hchar, roots_mul hmul, Multiset.map_add,
    Multiset.map_add, Multiset.sum_add]

theorem schattenOne_fromBlocks_diagonal_of_posSemidef {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {A : Matrix m m ℝ} {D : Matrix n n ℝ}
    (hA : A.PosSemidef) (hD : D.PosSemidef) :
    schattenOne (fromBlocks A (0 : Matrix m n ℝ) 0 D) = A.trace + D.trace := by
  have hBlk := fromBlocks_diagonal_posSemidef hA hD
  rw [schattenOne_eq_trace_of_posSemidef hBlk, trace_fromBlocks]

lemma posSemidef_fin_one_of_nonneg {a : ℝ} (ha : 0 ≤ a) :
    (!![a] : Matrix (Fin 1) (Fin 1) ℝ).PosSemidef := by
  have hdiag : (!![a] : Matrix (Fin 1) (Fin 1) ℝ) = diagonal fun _ => a := by
    rw [diagonal_fin_one]
  rw [hdiag, posSemidef_diagonal_iff]
  exact fun _ => ha

/-- Certified block-diagonal check: \(\operatorname{diag}(2,3)\) has
Schatten-1 mass \(5\). -/
theorem schattenOne_fromBlocks_two_three :
    schattenOne
      (fromBlocks (!![2] : Matrix (Fin 1) (Fin 1) ℝ) 0 0
        (!![3] : Matrix (Fin 1) (Fin 1) ℝ)) = 5 := by
  rw [schattenOne_fromBlocks_diagonal_of_posSemidef
    (posSemidef_fin_one_of_nonneg (by norm_num : (0 : ℝ) ≤ 2))
    (posSemidef_fin_one_of_nonneg (by norm_num : (0 : ℝ) ≤ 3))]
  simp [trace_fin_one_of]
  norm_num

end NystromSubmodularity
