import NystromSubmodularity.PrincipalSubmatrix
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Ring.Rat

/-!
# Computable inverse-trace checks over `ℚ`

Small-instance searches go through `cramerTraceInv` (adjugate / det), which is a
genuine `def` rather than mathlib's `noncomputable` `Inv`. Exhaustive pair
checks on \(n\le 5\) are `native_decide`d in `SmallInstanceChecks`.
-/

namespace NystromSubmodularity

open Matrix Finset

/-- Four-point supermodularity defect of `cramerTraceInv` (nonnegative iff the
inverse-trace is supermodular on the pair `A, B`). -/
def cramerSupermodularDiff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (A B : Finset (Fin n)) : ℚ :=
  cramerTraceInv M (A ∪ B) + cramerTraceInv M (A ∩ B) -
    cramerTraceInv M A - cramerTraceInv M B

/-- Four-point supermodularity defect of the Nyström error. -/
def cramerNystromSupermodularDiff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (A B : Finset (Fin n)) : ℚ :=
  cramerNystromError M (A ∪ B) + cramerNystromError M (A ∩ B) -
    cramerNystromError M A - cramerNystromError M B

theorem cramerInv_submatrix_equiv {ι κ R : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Field R]
    (M : Matrix ι ι R) (e : κ ≃ ι) :
    cramerInv (M.submatrix e e) = (cramerInv M).submatrix e e := by
  ext i j
  simp [cramerInv, Matrix.smul_apply, det_submatrix_equiv_self, adjugate_submatrix_equiv_self]

theorem cramerTraceInv_submatrix_equiv {ι κ R : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Field R]
    (M : Matrix ι ι R) (T : Finset ι) (e : κ ≃ PrincipalIndex T) :
    cramerTraceInv M T = (cramerInv ((principalSubmatrix M T).submatrix e e)).trace := by
  rw [cramerTraceInv, ← trace_submatrix_equiv e, cramerInv_submatrix_equiv]

theorem cramerTraceInv_univ {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (M : Matrix ι ι R) : cramerTraceInv M Finset.univ = (cramerInv M).trace := by
  rw [cramerTraceInv_submatrix_equiv M Finset.univ (principalIndexUnivEquiv (ι := ι)).symm]
  have h :
      (principalSubmatrix M Finset.univ).submatrix
        (principalIndexUnivEquiv (ι := ι)).symm
        (principalIndexUnivEquiv (ι := ι)).symm = M := by
    ext i j
    simp [principalSubmatrix, principalIndexUnivEquiv]
  rw [h]

theorem cramerTraceInv_singleton {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (M : Matrix ι ι R) (i : ι) :
    cramerTraceInv M {i} = (M i i)⁻¹ := by
  let e : Fin 1 ≃ PrincipalIndex ({i} : Finset ι) :=
    { toFun := fun _ => ⟨i, Finset.mem_singleton_self i⟩
      invFun := fun _ => 0
      left_inv := fun k => Subsingleton.elim _ _
      right_inv := fun x => Subtype.ext (Finset.mem_singleton.mp x.2).symm }
  have hmat : (principalSubmatrix M {i}).submatrix e e = !![M i i] := by
    ext a b
    fin_cases a
    fin_cases b
    simp [principalSubmatrix, e]
  rw [cramerTraceInv_submatrix_equiv M {i} e, hmat, cramerInv, det_fin_one]
  simp [Matrix.trace, Matrix.smul_apply, adjugate_subsingleton]

/-- Map a rational matrix into `ℝ` (for `PosDef` / `IsStieltjes`). -/
def toReal {ι : Type*} (M : Matrix ι ι ℚ) : Matrix ι ι ℝ :=
  M.map (fun q : ℚ => (q : ℝ))

@[simp]
theorem toReal_apply {ι : Type*} (M : Matrix ι ι ℚ) (i j : ι) :
    toReal M i j = (M i j : ℝ) :=
  rfl

theorem toReal_one {ι : Type*} [DecidableEq ι] :
    toReal (1 : Matrix ι ι ℚ) = (1 : Matrix ι ι ℝ) := by
  ext i j
  simp [toReal, Matrix.one_apply]
  split_ifs <;> simp

theorem toReal_add {ι : Type*} (A B : Matrix ι ι ℚ) :
    toReal (A + B) = toReal A + toReal B := by
  ext i j
  simp [toReal]

theorem toReal_smul {ι : Type*} (c : ℚ) (A : Matrix ι ι ℚ) :
    toReal (c • A) = (c : ℝ) • toReal A := by
  ext i j
  simp [toReal]

theorem toReal_isSymm {ι : Type*} {M : Matrix ι ι ℚ} (h : M.IsSymm) :
    (toReal M).IsSymm :=
  h.map _

theorem toReal_isDiagDominant {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℚ} (h : IsDiagDominant M) : IsDiagDominant (toReal M) := by
  intro i
  have hi := h i
  have hsum :
      ∑ j ∈ univ.erase i, |toReal M i j| =
        ((∑ j ∈ univ.erase i, |M i j| : ℚ) : ℝ) := by
    simp only [toReal_apply]
    conv_lhs => arg 2; intro j; rw [← Rat.cast_abs (K := ℝ)]
    exact (Rat.cast_sum (univ.erase i) (fun j => |M i j|)).symm
  rw [hsum, toReal_apply]
  exact (Rat.cast_le (K := ℝ)).mpr hi

theorem toReal_isSDD {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℚ} (h : IsSDD M) : IsSDD (toReal M) :=
  ⟨toReal_isSymm h.1, toReal_isDiagDominant h.2⟩

theorem toReal_isSDDM {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι ℚ} (h : IsSDDM M) : IsSDDM (toReal M) := by
  refine ⟨toReal_isSDD h.1, ?_, ?_⟩
  · intro i
    simpa [toReal_apply] using (Rat.cast_pos (K := ℝ)).mpr (h.2.1 i)
  · intro i j hij
    simpa [toReal_apply] using (Rat.cast_nonpos (K := ℝ)).mpr (h.2.2 i j hij)

theorem toReal_principalSubmatrix {ι : Type*} (M : Matrix ι ι ℚ) (T : Finset ι) :
    principalSubmatrix (toReal M) T = toReal (principalSubmatrix M T) :=
  rfl

theorem toReal_cramerInv {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℚ) :
    toReal (cramerInv A) = cramerInv (toReal A) := by
  ext i j
  simp only [toReal, cramerInv, map_apply, Matrix.smul_apply]
  have hdet : (A.map (fun q : ℚ => (q : ℝ))).det = (A.det : ℝ) :=
    ((Rat.castHom ℝ).map_det A).symm
  have hadj : (A.map (fun q : ℚ => (q : ℝ))).adjugate i j = (A.adjugate i j : ℝ) := by
    have h := (Rat.castHom ℝ).map_adjugate A
    simpa [RingHom.mapMatrix, map_apply] using
      congrArg (fun M : Matrix ι ι ℝ => M i j) h.symm
  rw [hdet, hadj]
  simp [smul_eq_mul]

theorem toReal_cramerTraceInv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ) (T : Finset ι) :
    ((cramerTraceInv (R := ℚ) M T : ℚ) : ℝ) = cramerTraceInv (toReal M) T := by
  unfold cramerTraceInv
  rw [toReal_principalSubmatrix, ← toReal_cramerInv]
  simp [toReal, Matrix.trace, Matrix.diag]

theorem toReal_nystromError {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ) (S : Finset ι) :
    ((cramerNystromError (R := ℚ) M S : ℚ) : ℝ) = nystromError (toReal M) S := by
  rw [← cramerNystromError_eq_nystromError]
  unfold cramerNystromError
  exact toReal_cramerTraceInv M (compl S)

end NystromSubmodularity
