import NystromSubmodularity.Definitions
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Fintype.Sum

/-!
# Principal submatrices and inverse traces

`traceInv M T` is \(\operatorname{tr}(M[T]^{-1})\), with the empty-matrix
convention that the unique \(0\times 0\) matrix is invertible and has trace
zero. By Colbrook Theorem 2 this is the nuclear Nyström error of \(M^{-1}\)
evaluated at the complement of `T`.
-/

namespace NystromSubmodularity

open Matrix

/-- Row/column type of the principal submatrix indexed by `T`. -/
abbrev PrincipalIndex {ι : Type*} (T : Finset ι) := { x : ι // x ∈ T }

/-- The principal submatrix of `M` with rows and columns in `T`. -/
def principalSubmatrix {ι R : Type*} (M : Matrix ι ι R) (T : Finset ι) :
    Matrix (PrincipalIndex T) (PrincipalIndex T) R :=
  M.submatrix Subtype.val Subtype.val

@[simp]
theorem principalSubmatrix_apply {ι R : Type*} (M : Matrix ι ι R) (T : Finset ι)
    (i j : PrincipalIndex T) :
    principalSubmatrix M T i j = M i.1 j.1 :=
  rfl

/-- Inverse-trace of a principal submatrix. The \(0\times 0\) case is `0`
because `det` of the empty matrix is `1` and the empty inverse has trace `0`. -/
noncomputable def traceInv {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (M : Matrix ι ι R) (T : Finset ι) : R :=
  (principalSubmatrix M T)⁻¹.trace

/-- Computable inverse via Cramer's rule. Agrees with `⁻¹` whenever `det ≠ 0`,
and is usable in `#eval` / `native_decide` (mathlib's `Inv` instance is
marked `noncomputable`). -/
def cramerInv {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (A : Matrix ι ι R) : Matrix ι ι R :=
  A.det⁻¹ • A.adjugate

theorem cramerInv_eq_inv {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (A : Matrix ι ι R) : cramerInv A = A⁻¹ := by
  rw [cramerInv, inv_def, Ring.inverse_eq_inv]

/-- Computable counterpart of `traceInv`. -/
def cramerTraceInv {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (M : Matrix ι ι R) (T : Finset ι) : R :=
  (cramerInv (principalSubmatrix M T)).trace

theorem cramerTraceInv_eq_traceInv {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (M : Matrix ι ι R) (T : Finset ι) :
    cramerTraceInv M T = traceInv M T := by
  simp [cramerTraceInv, traceInv, cramerInv_eq_inv]

theorem cramerTraceInv_empty {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (M : Matrix ι ι R) : cramerTraceInv M ∅ = 0 := by
  simp [cramerTraceInv, cramerInv, Matrix.trace]

theorem traceInv_empty {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (M : Matrix ι ι R) : traceInv M ∅ = 0 := by
  rw [← cramerTraceInv_eq_traceInv, cramerTraceInv_empty]

theorem principalSubmatrix_eq_toBlock {ι R : Type*} (M : Matrix ι ι R) (T : Finset ι) :
    principalSubmatrix M T = M.toBlock (· ∈ T) (· ∈ T) :=
  rfl

/-- The Nyström error, via Colbrook's Schur-complement identity
\(\mathcal{E}(S)=\operatorname{tr}(M[S^{\mathsf{c}}]^{-1})\).
For positive-definite `M` this equals the nuclear norm of the Nyström residual
of \(K=M^{-1}\) (see `Nystrom.lean`). -/
noncomputable def nystromError {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (M : Matrix ι ι R) (S : Finset ι) : R :=
  traceInv M (compl S)

def cramerNystromError {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (M : Matrix ι ι R) (S : Finset ι) : R :=
  cramerTraceInv M (compl S)

theorem cramerNystromError_eq_nystromError {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (M : Matrix ι ι R) (S : Finset ι) :
    cramerNystromError M S = nystromError M S :=
  cramerTraceInv_eq_traceInv _ _

/-- Colbrook's computational rewrite: the Nyström error is the inverse-trace of
the complementary principal submatrix. -/
theorem nystromError_eq_traceInv_compl {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (M : Matrix ι ι R) (S : Finset ι) :
    nystromError M S = traceInv M (compl S) :=
  rfl

theorem nystromError_univ {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (M : Matrix ι ι R) : nystromError M Finset.univ = 0 := by
  simp [nystromError, traceInv_empty]

theorem nystromError_empty {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (M : Matrix ι ι R) : nystromError M ∅ = traceInv M Finset.univ := by
  simp [nystromError]

/-- Reindexing by `S ⊕ Sᶜ` recovers the four principal blocks. -/
theorem reindex_sumCompl_eq_fromBlocks {ι R : Type*} [DecidableEq ι]
    (M : Matrix ι ι R) (S : Finset ι) :
    M.reindex (Equiv.sumCompl (· ∈ S)).symm (Equiv.sumCompl (· ∈ S)).symm =
      fromBlocks (M.toBlock (· ∈ S) (· ∈ S)) (M.toBlock (· ∈ S) (· ∉ S))
        (M.toBlock (· ∉ S) (· ∈ S)) (M.toBlock (· ∉ S) (· ∉ S)) := by
  ext i j
  cases i <;> cases j <;> rfl

theorem trace_submatrix_equiv {ι κ R : Type*} [Fintype ι] [Fintype κ] [AddCommMonoid R]
    (e : ι ≃ κ) (M : Matrix κ κ R) :
    (M.submatrix e e).trace = M.trace := by
  simp [Matrix.trace, Matrix.diag]
  exact Fintype.sum_equiv e (fun i => M (e i) (e i)) (fun k => M k k) fun _ => rfl

/-- Canonical identification of the full principal submatrix with the original matrix. -/
def principalIndexUnivEquiv {ι : Type*} [Fintype ι] :
    PrincipalIndex (Finset.univ : Finset ι) ≃ ι where
  toFun x := x.1
  invFun i := ⟨i, Finset.mem_univ i⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv _ := rfl

theorem traceInv_univ {ι R : Type*} [Fintype ι] [DecidableEq ι] [Field R]
    (M : Matrix ι ι R) : traceInv M Finset.univ = M⁻¹.trace := by
  let e := principalIndexUnivEquiv (ι := ι)
  have hsub : principalSubmatrix M Finset.univ = M.submatrix e e := by
    ext i j
    simp [principalSubmatrix]
    have hi : e i = i.1 := rfl
    have hj : e j = j.1 := rfl
    rw [hi, hj]
  rw [traceInv, hsub, inv_submatrix_equiv, trace_submatrix_equiv]

theorem trace_fromBlocks {m n R : Type*} [Fintype m] [Fintype n] [AddCommMonoid R]
    (A : Matrix m m R) (B : Matrix m n R) (C : Matrix n m R) (D : Matrix n n R) :
    (fromBlocks A B C D).trace = A.trace + D.trace := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

/-- Identify `A ∪ {i}` with `A ⊕ Fin 1`. -/
def insert₁Equiv {ι : Type*} [DecidableEq ι] {A : Finset ι} {i : ι} (hi : i ∉ A) :
    PrincipalIndex A ⊕ Fin 1 ≃ PrincipalIndex (insert i A) where
  toFun
    | .inl a => ⟨a.1, by simp [a.2]⟩
    | .inr _ => ⟨i, by simp⟩
  invFun x :=
    if hxi : x.1 = i then .inr 0
    else .inl ⟨x.1, by
      have hx := x.2
      simp only [Finset.mem_insert, hxi, false_or] at hx
      exact hx⟩
  left_inv := by
    intro x
    cases x with
    | inl a =>
      have : a.1 ≠ i := fun h => hi (h ▸ a.2)
      simp [this]
    | inr k =>
      fin_cases k
      simp
  right_inv := by
    intro x
    by_cases hxi : x.1 = i
    · apply Subtype.ext
      simp [hxi]
    · simp [hxi]

/-- Column of `M` from `A` into a single index `i`, as a `|A|×1` block. -/
def colBlock {ι R : Type*} (M : Matrix ι ι R) (A : Finset ι) (i : ι) :
    Matrix (PrincipalIndex A) (Fin 1) R :=
  fun a _ => M a.1 i

/-- The `1×1` principal block on `{i}`. -/
def scalarBlock {ι R : Type*} (M : Matrix ι ι R) (i : ι) : Matrix (Fin 1) (Fin 1) R :=
  fun _ _ => M i i

/-- Forward map of `insert₂Equiv`. -/
def insert₂ToFun {ι : Type*} [DecidableEq ι] {A : Finset ι} {i j : ι}
    (_hi : i ∉ A) (_hj : j ∉ A) (_hij : i ≠ j) :
    PrincipalIndex A ⊕ Fin 2 → PrincipalIndex (insert j (insert i A))
  | .inl a => ⟨a.1, by simp [a.2]⟩
  | .inr k => if k = 0 then ⟨i, by simp⟩ else ⟨j, by simp⟩

/-- Inverse map of `insert₂Equiv`. -/
def insert₂InvFun {ι : Type*} [DecidableEq ι] {A : Finset ι} {i j : ι}
    (_hi : i ∉ A) (_hj : j ∉ A) (_hij : i ≠ j) :
    PrincipalIndex (insert j (insert i A)) → PrincipalIndex A ⊕ Fin 2 :=
  fun x =>
    if hxA : x.1 ∈ A then .inl ⟨x.1, hxA⟩
    else if _hxi : x.1 = i then .inr 0
    else .inr 1

lemma insert₂ToFun_left_inv {ι : Type*} [DecidableEq ι] {A : Finset ι} {i j : ι}
    (hi : i ∉ A) (hj : j ∉ A) (hij : i ≠ j) :
    Function.LeftInverse (insert₂InvFun hi hj hij) (insert₂ToFun hi hj hij) := by
  intro x
  cases x with
  | inl a =>
    simp [insert₂ToFun, insert₂InvFun, a.2]
  | inr k =>
    fin_cases k
    · simp [insert₂ToFun, insert₂InvFun, hi]
    · have hji : j ≠ i := hij.symm
      simp [insert₂ToFun, insert₂InvFun, hj, hji]

lemma insert₂ToFun_right_inv {ι : Type*} [DecidableEq ι] {A : Finset ι} {i j : ι}
    (hi : i ∉ A) (hj : j ∉ A) (hij : i ≠ j) :
    Function.RightInverse (insert₂InvFun hi hj hij) (insert₂ToFun hi hj hij) := by
  intro x
  unfold insert₂InvFun insert₂ToFun
  split_ifs with hA hxi <;> apply Subtype.ext
  · rfl
  · exact hxi.symm
  · have hxj : x.1 = j := by
      have hx : x.1 = j ∨ x.1 ∈ insert i A := Finset.mem_insert.mp x.2
      rcases hx with (h | hx)
      · exact h
      · have hx' : x.1 = i ∨ x.1 ∈ A := Finset.mem_insert.mp hx
        rcases hx' with (h | h)
        · exact (hxi h).elim
        · exact (hA h).elim
    exact hxj.symm

/-- Identify `A ∪ {i,j}` with `A ⊕ Fin 2`, sending `i ↦ 0` and `j ↦ 1`. -/
def insert₂Equiv {ι : Type*} [DecidableEq ι] {A : Finset ι} {i j : ι}
    (hi : i ∉ A) (hj : j ∉ A) (hij : i ≠ j) :
    PrincipalIndex A ⊕ Fin 2 ≃ PrincipalIndex (insert j (insert i A)) :=
  ⟨insert₂ToFun hi hj hij, insert₂InvFun hi hj hij,
    insert₂ToFun_left_inv hi hj hij, insert₂ToFun_right_inv hi hj hij⟩

/-- Off-diagonal block of `M` from `A` into the ordered pair `(i,j)`. -/
def pairOffBlock {ι R : Type*} (M : Matrix ι ι R) (A : Finset ι) (i j : ι) :
    Matrix (PrincipalIndex A) (Fin 2) R :=
  fun a k => if k = 0 then M a.1 i else M a.1 j

/-- The `2×2` principal block on `{i,j}`. -/
def pairDiagBlock {ι R : Type*} (M : Matrix ι ι R) (i j : ι) : Matrix (Fin 2) (Fin 2) R :=
  fun k l =>
    if k = 0 then (if l = 0 then M i i else M i j)
    else (if l = 0 then M j i else M j j)

end NystromSubmodularity
