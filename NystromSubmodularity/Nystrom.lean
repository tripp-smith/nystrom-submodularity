import NystromSubmodularity.PrincipalSubmatrix
import NystromSubmodularity.Stieltjes
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Ring

/-!
# Nyström approximation and nuclear residual

The nuclear-norm Nyström error of \(K=M^{-1}\) is defined in
`PrincipalSubmatrix.nystromError` via Colbrook's identity
\(\mathcal{E}(S)=\operatorname{tr}(M[S^{\mathsf{c}}]^{-1})\). Colbrook
Theorem 2 identifies the residual, after reindexing by
`Equiv.sumCompl (· ∈ S)`, with the block matrix that is zero on \(S\)
and \(M[S^{\mathsf{c}}]^{-1}\) on the complement. The residual is
positive semidefinite, so the nuclear (Schatten-1) norm equals the
trace and `nuclearNystromError` agrees with `nystromError`.
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

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Identify `{x // x ∉ S}` with the principal index of `compl S`. -/
def complSubtypeEquiv (S : Finset ι) :
    { x : ι // x ∉ S } ≃ PrincipalIndex (compl S) where
  toFun x := ⟨x.1, mem_compl.mpr x.2⟩
  invFun x := ⟨x.1, mem_compl.mp x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma toBlock_eq_principal_compl (M : Matrix ι ι ℝ) (S : Finset ι) :
    M.toBlock (fun x => x ∉ S) (fun x => x ∉ S) =
      (principalSubmatrix M (compl S)).submatrix
        (complSubtypeEquiv S) (complSubtypeEquiv S) := by
  ext i j
  rfl

lemma nystromApprox_apply (K : Matrix ι ι ℝ) (S : Finset ι) (i j : ι) :
    nystromApprox K S i j =
      ∑ q : PrincipalIndex S, ∑ p : PrincipalIndex S,
        K i p.1 * (principalSubmatrix K S)⁻¹ p q * K q.1 j := by
  unfold nystromApprox
  simp only [Matrix.mul_apply, submatrix_apply, id_eq]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_mul]

lemma nystromApprox_toBlock_compl (K : Matrix ι ι ℝ) (S : Finset ι) :
    (nystromApprox K S).toBlock (fun x => x ∉ S) (fun x => x ∉ S) =
      K.toBlock (fun x => x ∉ S) (fun x => x ∈ S) *
        (principalSubmatrix K S)⁻¹ *
        K.toBlock (fun x => x ∈ S) (fun x => x ∉ S) := by
  ext i j
  simp [toBlock, nystromApprox_apply, Matrix.mul_apply, principalSubmatrix]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_mul]

lemma nystromApprox_apply_mem_right (K : Matrix ι ι ℝ) (S : Finset ι)
    (hK : IsUnit (principalSubmatrix K S)) (i : ι) {s : ι} (hs : s ∈ S) :
    nystromApprox K S i s = K i s := by
  have hdet : IsUnit (principalSubmatrix K S).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hK
  have hid : (principalSubmatrix K S)⁻¹ * principalSubmatrix K S = 1 :=
    Matrix.nonsing_inv_mul _ hdet
  rw [nystromApprox_apply]
  have hsum :
      (∑ q : PrincipalIndex S, ∑ p : PrincipalIndex S,
          K i p.1 * (principalSubmatrix K S)⁻¹ p q * K q.1 s) =
        ∑ p : PrincipalIndex S,
          K i p.1 * ((principalSubmatrix K S)⁻¹ * principalSubmatrix K S) p ⟨s, hs⟩ := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [Matrix.mul_apply, principalSubmatrix, mul_assoc]
    rw [Finset.mul_sum]
  rw [hsum, hid]
  simp [Matrix.one_apply]

lemma nystromApprox_apply_mem_left (K : Matrix ι ι ℝ) (S : Finset ι)
    (hK : IsUnit (principalSubmatrix K S)) {s : ι} (hs : s ∈ S) (j : ι) :
    nystromApprox K S s j = K s j := by
  have hdet : IsUnit (principalSubmatrix K S).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hK
  have hid : principalSubmatrix K S * (principalSubmatrix K S)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hdet
  rw [nystromApprox_apply]
  have hsum :
      (∑ q : PrincipalIndex S, ∑ p : PrincipalIndex S,
          K s p.1 * (principalSubmatrix K S)⁻¹ p q * K q.1 j) =
        ∑ q : PrincipalIndex S,
          (principalSubmatrix K S * (principalSubmatrix K S)⁻¹) ⟨s, hs⟩ q * K q.1 j := by
    refine Finset.sum_congr rfl fun q _ => ?_
    simp [Matrix.mul_apply, principalSubmatrix, mul_assoc]
    rw [Finset.sum_mul]
    simp [mul_assoc]
  rw [hsum, hid]
  simp [Matrix.one_apply]

lemma nystromResidual_apply_mem_right (K : Matrix ι ι ℝ) (S : Finset ι)
    (hK : IsUnit (principalSubmatrix K S)) (i : ι) {s : ι} (hs : s ∈ S) :
    nystromResidual K S i s = 0 := by
  simp [nystromResidual, nystromApprox_apply_mem_right K S hK i hs]

lemma nystromResidual_apply_mem_left (K : Matrix ι ι ℝ) (S : Finset ι)
    (hK : IsUnit (principalSubmatrix K S)) {s : ι} (hs : s ∈ S) (j : ι) :
    nystromResidual K S s j = 0 := by
  simp [nystromResidual, nystromApprox_apply_mem_left K S hK hs j]


lemma nystromResidual_toBlock_compl (K : Matrix ι ι ℝ) (S : Finset ι) :
    (nystromResidual K S).toBlock (fun x => x ∉ S) (fun x => x ∉ S) =
      K.toBlock (fun x => x ∉ S) (fun x => x ∉ S) -
        K.toBlock (fun x => x ∉ S) (fun x => x ∈ S) *
          (principalSubmatrix K S)⁻¹ *
          K.toBlock (fun x => x ∈ S) (fun x => x ∉ S) := by
  ext i j
  have h := congrArg (fun A => A i j) (nystromApprox_toBlock_compl K S)
  simp [nystromResidual, toBlock, Matrix.sub_apply] at h ⊢
  exact h

/-- The Schur complement of the (1,1) block of M⁻¹ is D⁻¹. -/
lemma schur_of_inv_eq_compl_inv {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n]
    {A : Matrix m m ℝ} {B : Matrix m n ℝ} {D : Matrix n n ℝ}
    (hA : (fromBlocks A B Bᴴ D).PosDef) (hD : D.PosDef) :
    (fromBlocks A B Bᴴ D)⁻¹.toBlocks₂₂ -
        (fromBlocks A B Bᴴ D)⁻¹.toBlocks₂₁ *
          ((fromBlocks A B Bᴴ D)⁻¹.toBlocks₁₁)⁻¹ *
          (fromBlocks A B Bᴴ D)⁻¹.toBlocks₁₂ =
      D⁻¹ := by
  have hS : (A - B * D⁻¹ * Bᴴ).PosDef := schurComplement₂₂_posDef hD hA
  have hinv := inv_fromBlocks₂₂_eq A B Bᴴ D hD.isUnit hS.isUnit hA.isUnit
  have h11 : (fromBlocks A B Bᴴ D)⁻¹.toBlocks₁₁ = (A - B * D⁻¹ * Bᴴ)⁻¹ := by
    rw [hinv]; exact toBlocks_fromBlocks₁₁ _ _ _ _
  have h12 : (fromBlocks A B Bᴴ D)⁻¹.toBlocks₁₂ =
      -((A - B * D⁻¹ * Bᴴ)⁻¹ * B * D⁻¹) := by
    rw [hinv]; exact toBlocks_fromBlocks₁₂ _ _ _ _
  have h21 : (fromBlocks A B Bᴴ D)⁻¹.toBlocks₂₁ =
      -(D⁻¹ * Bᴴ * (A - B * D⁻¹ * Bᴴ)⁻¹) := by
    rw [hinv]; exact toBlocks_fromBlocks₂₁ _ _ _ _
  have h22 : (fromBlocks A B Bᴴ D)⁻¹.toBlocks₂₂ =
      D⁻¹ + D⁻¹ * Bᴴ * (A - B * D⁻¹ * Bᴴ)⁻¹ * B * D⁻¹ := by
    rw [hinv]; exact toBlocks_fromBlocks₂₂ _ _ _ _
  have hKinv : ((fromBlocks A B Bᴴ D)⁻¹.toBlocks₁₁)⁻¹ = A - B * D⁻¹ * Bᴴ := by
    rw [h11]
    exact Matrix.nonsing_inv_nonsing_inv (A := A - B * D⁻¹ * Bᴴ)
      ((Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit)
  have hSdet : IsUnit (A - B * D⁻¹ * Bᴴ).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit
  rw [h22, h21, h12, hKinv]
  -- `(-X) * S * (-Y) = X * S * Y`, then cancel `S⁻¹ * S`.
  have hneg :
      (-(D⁻¹ * Bᴴ * (A - B * D⁻¹ * Bᴴ)⁻¹)) * (A - B * D⁻¹ * Bᴴ) *
          (-((A - B * D⁻¹ * Bᴴ)⁻¹ * B * D⁻¹)) =
        D⁻¹ * Bᴴ * (A - B * D⁻¹ * Bᴴ)⁻¹ * B * D⁻¹ := by
    have hx :
        (-(D⁻¹ * Bᴴ * (A - B * D⁻¹ * Bᴴ)⁻¹)) * (A - B * D⁻¹ * Bᴴ) *
            (-((A - B * D⁻¹ * Bᴴ)⁻¹ * B * D⁻¹)) =
          (D⁻¹ * Bᴴ * (A - B * D⁻¹ * Bᴴ)⁻¹) * (A - B * D⁻¹ * Bᴴ) *
            ((A - B * D⁻¹ * Bᴴ)⁻¹ * B * D⁻¹) := by
      ext i j
      simp [Matrix.mul_apply, Matrix.neg_apply]
    rw [hx]
    have hy :
        (D⁻¹ * Bᴴ * (A - B * D⁻¹ * Bᴴ)⁻¹) * (A - B * D⁻¹ * Bᴴ) *
            ((A - B * D⁻¹ * Bᴴ)⁻¹ * B * D⁻¹) =
          D⁻¹ * Bᴴ * ((A - B * D⁻¹ * Bᴴ)⁻¹ * (A - B * D⁻¹ * Bᴴ) *
            ((A - B * D⁻¹ * Bᴴ)⁻¹ * B * D⁻¹)) := by
      simp [Matrix.mul_assoc]
    rw [hy, Matrix.nonsing_inv_mul _ hSdet, Matrix.one_mul]
    simp [Matrix.mul_assoc]
  rw [hneg]
  abel

lemma toBlocks_of_reindex_inv (M : Matrix ι ι ℝ) (S : Finset ι) :
    (M.reindex (Equiv.sumCompl (fun x => x ∈ S)).symm
        (Equiv.sumCompl (fun x => x ∈ S)).symm)⁻¹.toBlocks₁₁ =
      M⁻¹.toBlock (fun x => x ∈ S) (fun x => x ∈ S) ∧
    (M.reindex (Equiv.sumCompl (fun x => x ∈ S)).symm
        (Equiv.sumCompl (fun x => x ∈ S)).symm)⁻¹.toBlocks₁₂ =
      M⁻¹.toBlock (fun x => x ∈ S) (fun x => x ∉ S) ∧
    (M.reindex (Equiv.sumCompl (fun x => x ∈ S)).symm
        (Equiv.sumCompl (fun x => x ∈ S)).symm)⁻¹.toBlocks₂₁ =
      M⁻¹.toBlock (fun x => x ∉ S) (fun x => x ∈ S) ∧
    (M.reindex (Equiv.sumCompl (fun x => x ∈ S)).symm
        (Equiv.sumCompl (fun x => x ∈ S)).symm)⁻¹.toBlocks₂₂ =
      M⁻¹.toBlock (fun x => x ∉ S) (fun x => x ∉ S) := by
  have h := inv_reindex (Equiv.sumCompl (fun x => x ∈ S)).symm
    (Equiv.sumCompl (fun x => x ∈ S)).symm M
  rw [h]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> rfl

omit [Fintype ι] [DecidableEq ι] in
lemma herm_off_block (M : Matrix ι ι ℝ) (hM : M.IsHermitian) (S : Finset ι) :
    M.toBlock (fun x => x ∉ S) (fun x => x ∈ S) =
      (M.toBlock (fun x => x ∈ S) (fun x => x ∉ S))ᴴ := by
  ext i j
  simp [toBlock, conjTranspose_apply, star_trivial]
  exact ((isHermitian_iff_isSymm (α := ℝ)).mp hM).apply j.1 i.1

lemma residual_compl_block_eq_inv {M : Matrix ι ι ℝ} (hM : M.PosDef) (S : Finset ι) :
    (nystromResidual M⁻¹ S).toBlock (fun x => x ∉ S) (fun x => x ∉ S) =
      (M.toBlock (fun x => x ∉ S) (fun x => x ∉ S))⁻¹ := by
  set e := Equiv.sumCompl (fun x => x ∈ S)
  have hC := herm_off_block M hM.isHermitian S
  have hMe : M.reindex e.symm e.symm =
      fromBlocks (M.toBlock (fun x => x ∈ S) (fun x => x ∈ S))
        (M.toBlock (fun x => x ∈ S) (fun x => x ∉ S))
        (M.toBlock (fun x => x ∈ S) (fun x => x ∉ S))ᴴ
        (M.toBlock (fun x => x ∉ S) (fun x => x ∉ S)) := by
    rw [reindex_sumCompl_eq_fromBlocks, hC]
  have hfrom : (fromBlocks (M.toBlock (fun x => x ∈ S) (fun x => x ∈ S))
      (M.toBlock (fun x => x ∈ S) (fun x => x ∉ S))
      (M.toBlock (fun x => x ∈ S) (fun x => x ∉ S))ᴴ
      (M.toBlock (fun x => x ∉ S) (fun x => x ∉ S))).PosDef := by
    rw [← hMe]
    exact (posDef_submatrix_equiv e).mpr hM
  have hD : (M.toBlock (fun x => x ∉ S) (fun x => x ∉ S)).PosDef :=
    hM.submatrix Subtype.val_injective
  have hschur := schur_of_inv_eq_compl_inv hfrom hD
  have ⟨h11, h12, h21, h22⟩ := toBlocks_of_reindex_inv M S
  rw [← hMe] at hschur
  rw [h11, h12, h21, h22] at hschur
  rw [nystromResidual_toBlock_compl, principalSubmatrix_eq_toBlock]
  exact hschur

/-- Colbrook Theorem 2: after reindexing by `S ⊕ Sᶜ`, the Nyström residual of
\(M^{-1}\) is zero on \(S\) and \(M[S^{\mathsf{c}}]^{-1}\) on the complement. -/
theorem nystromResidual_eq_padded_compl_inv {M : Matrix ι ι ℝ} (hM : M.PosDef)
    (S : Finset ι) :
    (nystromResidual M⁻¹ S).reindex
        (Equiv.sumCompl (fun x => x ∈ S)).symm
        (Equiv.sumCompl (fun x => x ∈ S)).symm =
      fromBlocks 0 0 0 (M.toBlock (fun x => x ∉ S) (fun x => x ∉ S))⁻¹ := by
  have hK : IsUnit (principalSubmatrix M⁻¹ S) :=
    (hM.inv.submatrix Subtype.val_injective).isUnit
  have hcompl := residual_compl_block_eq_inv hM S
  rw [reindex_sumCompl_eq_fromBlocks]
  ext i j
  cases i with
  | inl a =>
    cases j with
    | inl b =>
      simp [fromBlocks, nystromResidual_apply_mem_right (M⁻¹) S hK a.1 b.2]
    | inr b =>
      simp [fromBlocks, nystromResidual_apply_mem_left (M⁻¹) S hK a.2 b.1]
  | inr a =>
    cases j with
    | inl b =>
      simp [fromBlocks, nystromResidual_apply_mem_right (M⁻¹) S hK a.1 b.2]
    | inr b =>
      have := congrArg (fun A => A a b) hcompl
      simpa [fromBlocks, toBlock] using this

theorem nuclearNystromError_eq_nystromError {M : Matrix ι ι ℝ} (hM : M.PosDef)
    (S : Finset ι) : nuclearNystromError M S = nystromError M S := by
  have hre := nystromResidual_eq_padded_compl_inv hM S
  have htr :
      (nystromResidual M⁻¹ S).trace =
        (fromBlocks (0 : Matrix (PrincipalIndex S) (PrincipalIndex S) ℝ) 0 0
          (M.toBlock (fun x => x ∉ S) (fun x => x ∉ S))⁻¹).trace := by
    have := congrArg Matrix.trace hre
    rwa [trace_reindex] at this
  rw [nuclearNystromError, nuclearNorm, htr, trace_fromBlocks, trace_zero, zero_add]
  have hconv := toBlock_eq_principal_compl M S
  have : (M.toBlock (fun x => x ∉ S) (fun x => x ∉ S))⁻¹.trace =
      (principalSubmatrix M (compl S))⁻¹.trace := by
    rw [hconv, inv_submatrix_equiv, trace_submatrix_equiv]
  simpa [nystromError, traceInv] using this

end NystromSubmodularity
