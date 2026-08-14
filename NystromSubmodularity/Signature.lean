import NystromSubmodularity.InverseTrace
import NystromSubmodularity.Computable
import NystromSubmodularity.Counterexamples.SDDDim3
import NystromSubmodularity.SmallInstanceChecks
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.List.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Star.Real

/-!
# Signature switching

Colbrook Propositions 7–8 and Corollary 13: inverse-trace supermodularity
is a property of the *signed* support graph. Conjugation by a \(\{\pm 1\}\)
diagonal leaves principal inverse-traces unchanged, so a positive-definite
matrix is supermodular as soon as some signature makes it Stieltjes.
On a fully supported triangle that happens for every positive-definite
realization if and only if the sign pattern is antibalanced (even number
of positive edges on the unique simple cycle).
-/

namespace NystromSubmodularity

open Finset Counterexamples SmallInstance

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable section

/-- A signature matrix: diagonal with entries in \(\{\pm 1\}\). -/
def IsSignature (D : Matrix ι ι ℝ) : Prop :=
  D.IsDiag ∧ ∀ i, D i i = 1 ∨ D i i = -1

/-- Signature congruence \(DMD\). -/
def signatureCongr (D M : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  D * M * D

def signum (x : ℝ) : ℝ :=
  if 0 < x then 1 else if x < 0 then -1 else 0

lemma signum_pos {x : ℝ} (hx : 0 < x) : signum x = 1 := by
  simp [signum, hx]

lemma signum_neg {x : ℝ} (hx : x < 0) : signum x = -1 := by
  simp [signum, hx, not_lt_of_gt hx]

lemma signum_eq_pm {x : ℝ} (hx : x ≠ 0) : signum x = 1 ∨ signum x = -1 := by
  by_cases hp : 0 < x
  · exact Or.inl (signum_pos hp)
  · have hn : x < 0 := lt_of_le_of_ne (le_of_not_gt hp) hx
    exact Or.inr (signum_neg hn)

lemma pos_of_signum_one {x : ℝ} (h : signum x = 1) : 0 < x := by
  by_contra hn
  have hx0 : x ≤ 0 := le_of_not_gt hn
  by_cases hz : x = 0
  · subst hz; simp [signum] at h
  · have hneg : x < 0 := lt_of_le_of_ne hx0 hz
    rw [signum_neg hneg] at h
    norm_num at h

lemma neg_of_signum_neg_one {x : ℝ} (h : signum x = -1) : x < 0 := by
  by_contra hn
  have hx0 : 0 ≤ x := le_of_not_gt hn
  by_cases hz : x = 0
  · subst hz; simp [signum] at h
  · have hpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hz)
    rw [signum_pos hpos] at h
    norm_num at h

lemma IsSignature.sq_eq_one {D : Matrix ι ι ℝ} (hD : IsSignature D) (i : ι) :
    D i i * D i i = 1 := by
  rcases hD.2 i with h | h <;> simp [h]

lemma IsSignature.ne_zero {D : Matrix ι ι ℝ} (hD : IsSignature D) (i : ι) :
    D i i ≠ 0 := by
  rcases hD.2 i with h | h <;> simp [h]

lemma IsSignature.mul_apply {D M : Matrix ι ι ℝ} (hD : IsSignature D) (i j : ι) :
    (D * M) i j = D i i * M i j := by
  rw [Matrix.mul_apply]
  refine (Finset.sum_eq_single i ?_ ?_).trans ?_
  · intro k _ hki
    rw [hD.1 (Ne.symm hki), zero_mul]
  · intro hi
    exact (hi (mem_univ i)).elim
  · rfl

lemma IsSignature.congr_apply {D M : Matrix ι ι ℝ} (hD : IsSignature D) (i j : ι) :
    signatureCongr D M i j = D i i * M i j * D j j := by
  have h : (D * M * D) i j = (D * M) i j * D j j := by
    rw [Matrix.mul_apply]
    refine (Finset.sum_eq_single j ?_ ?_).trans ?_
    · intro k _ hkj
      rw [hD.1 hkj, mul_zero]
    · intro hj
      exact (hj (mem_univ j)).elim
    · rfl
  rw [signatureCongr, h, IsSignature.mul_apply hD]

lemma IsSignature.mul_self {D : Matrix ι ι ℝ} (hD : IsSignature D) : D * D = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [IsSignature.mul_apply hD, IsSignature.sq_eq_one hD]
  · simp [IsSignature.mul_apply hD, hD.1 hij, hij]

lemma IsSignature.congr_congr {D M : Matrix ι ι ℝ} (hD : IsSignature D) :
    signatureCongr D (signatureCongr D M) = M := by
  have hDD : D * D = 1 := hD.mul_self
  calc
    signatureCongr D (signatureCongr D M) = D * (D * M * D) * D := rfl
    _ = ((D * D) * M) * (D * D) := by simp [mul_assoc]
    _ = (1 * M) * 1 := by simp [hDD]
    _ = M := by simp

lemma isSignature_diagonal {d : ι → ℝ} (hd : ∀ i, d i = 1 ∨ d i = -1) :
    IsSignature (Matrix.diagonal d) :=
  ⟨fun i j hij => Matrix.diagonal_apply_ne d hij, fun i => by
    rw [Matrix.diagonal_apply_eq]
    exact hd i⟩

lemma IsSignature.mulVec_apply {D : Matrix ι ι ℝ} (hD : IsSignature D)
    (x : ι → ℝ) (i : ι) : Matrix.mulVec D x i = D i i * x i := by
  change (∑ j, D i j * x j) = D i i * x i
  refine (Finset.sum_eq_single i ?_ ?_).trans ?_
  · intro j _ hji
    rw [hD.1 (Ne.symm hji), zero_mul]
  · intro hi
    exact (hi (mem_univ i)).elim
  · rfl

lemma IsSignature.mulVec_injective {D : Matrix ι ι ℝ} (hD : IsSignature D) :
    Function.Injective D.mulVec := by
  intro x y hxy
  funext i
  have := congrArg (fun z => z i) hxy
  simp only [IsSignature.mulVec_apply hD] at this
  exact mul_left_cancel₀ (hD.ne_zero i) this

lemma IsSignature.transpose_eq {D : Matrix ι ι ℝ} (hD : IsSignature D) :
    Matrix.transpose D = D := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rfl
  · rw [Matrix.transpose_apply, hD.1 hij, hD.1 (Ne.symm hij)]

lemma IsSignature.conjTranspose_eq {D : Matrix ι ι ℝ} (hD : IsSignature D) :
    Matrix.conjTranspose D = D := by
  ext i j
  simp [Matrix.conjTranspose_apply, star_trivial]
  by_cases hij : i = j
  · subst hij
    rfl
  · rw [hD.1 (Ne.symm hij), hD.1 hij]

lemma signatureCongr_posDef {D M : Matrix ι ι ℝ} (hD : IsSignature D) (hM : M.PosDef) :
    (signatureCongr D M).PosDef := by
  have : Matrix.conjTranspose D * M * D = signatureCongr D M := by
    rw [hD.conjTranspose_eq]
    rfl
  rw [← this]
  exact hM.conjTranspose_mul_mul_same hD.mulVec_injective

lemma signatureCongr_principal {D M : Matrix ι ι ℝ} (hD : IsSignature D) (T : Finset ι) :
    principalSubmatrix (signatureCongr D M) T =
      signatureCongr (principalSubmatrix D T) (principalSubmatrix M T) := by
  have hDT : IsSignature (principalSubmatrix D T) :=
    ⟨fun a b hab => hD.1 (fun h => hab (Subtype.ext h)), fun a => hD.2 a.1⟩
  ext i j
  rw [principalSubmatrix_apply, IsSignature.congr_apply hD,
    IsSignature.congr_apply hDT, principalSubmatrix_apply, principalSubmatrix_apply,
    principalSubmatrix_apply]

lemma signatureCongr_inv {D A : Matrix ι ι ℝ} (hD : IsSignature D) (hA : IsUnit A.det) :
    (signatureCongr D A)⁻¹ = signatureCongr D A⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  have hDD : D * D = 1 := hD.mul_self
  have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hA
  have hassoc : signatureCongr D A * signatureCongr D A⁻¹ =
      D * A * (D * D) * A⁻¹ * D := by
    simp [signatureCongr, mul_assoc]
  rw [hassoc, hDD]
  simp [mul_assoc, hAA, hDD]

lemma signatureCongr_inv_diag {D A : Matrix ι ι ℝ} (hD : IsSignature D)
    (hA : IsUnit A.det) (i : ι) :
    (signatureCongr D A)⁻¹ i i = A⁻¹ i i := by
  rw [signatureCongr_inv hD hA, IsSignature.congr_apply hD]
  have hsq := hD.sq_eq_one i
  calc
    D i i * A⁻¹ i i * D i i = A⁻¹ i i * (D i i * D i i) := by ring
    _ = A⁻¹ i i * 1 := by rw [hsq]
    _ = A⁻¹ i i := by ring

/-- Principal inverse-traces are invariant under signature congruence. -/
theorem traceInv_signatureCongr {D M : Matrix ι ι ℝ} (hD : IsSignature D)
    (hM : M.PosDef) (T : Finset ι) :
    traceInv (signatureCongr D M) T = traceInv M T := by
  have hP : (principalSubmatrix M T).PosDef := hM.submatrix Subtype.val_injective
  have hDT : IsSignature (principalSubmatrix D T) :=
    ⟨fun a b hab => hD.1 (fun h => hab (Subtype.ext h)), fun a => hD.2 a.1⟩
  have hunit : IsUnit (principalSubmatrix M T).det :=
    (Matrix.isUnit_iff_isUnit_det (principalSubmatrix M T)).mp hP.isUnit
  unfold traceInv
  rw [signatureCongr_principal hD]
  simp only [Matrix.trace, Matrix.diag]
  refine Fintype.sum_congr _ _ fun i => ?_
  exact signatureCongr_inv_diag hDT hunit i

theorem nystromError_signatureCongr {D M : Matrix ι ι ℝ} (hD : IsSignature D)
    (hM : M.PosDef) (S : Finset ι) :
    nystromError (signatureCongr D M) S = nystromError M S :=
  traceInv_signatureCongr hD hM (compl S)

/-- Colbrook Proposition 7: a signature that produces a Stieltjes matrix
implies supermodularity of the Nyström error. -/
theorem nystromError_supermodular_of_signature_stieltjes {D M : Matrix ι ι ℝ}
    (hD : IsSignature D) (hS : IsStieltjes (signatureCongr D M)) (hM : M.PosDef) :
    Supermodular (nystromError M) := by
  have hfun : nystromError M = nystromError (signatureCongr D M) :=
    funext fun S => (nystromError_signatureCongr hD hM S).symm
  rw [hfun]
  exact supermodular_compl (traceInv_supermodular_of_isStieltjes hS)

/-! ## Cycle product / antibalance on enumerated cycles -/

/-- A simple cycle on `Fin n`, represented as a nodup list of length at least 3. -/
def IsSimpleCycle {n : ℕ} (c : List (Fin n)) : Prop :=
  3 ≤ c.length ∧ c.Nodup

/-- Consecutive pairs along a cycle, including the closing edge. -/
def cyclePairs {n : ℕ} (c : List (Fin n)) : List (Fin n × Fin n) :=
  c.zip (c.tail ++ c.take 1)

/-- Even number of positive edges on an enumerated cycle. -/
def evenPositiveSupport {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : List (Fin n)) : Prop :=
  Even ((cyclePairs c).countP fun p => decide (0 < A p.1 p.2))

/-- Antibalance on an enumerated list of simple cycles (Prop. 8 packaging). -/
def IsAntibalancedOn {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (cycles : List (List (Fin n))) : Prop :=
  ∀ c ∈ cycles, evenPositiveSupport A c

def FullySupportedTriangle (A : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ i j : Fin 3, i ≠ j → A i j ≠ 0

def triangleCycleProduct (A : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  signum (A 0 1) * signum (A 1 2) * signum (A 2 0)

/-- Antibalanced triangle: the unique 3-cycle has sign product \(-1\). -/
def IsAntibalancedTriangle (A : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  triangleCycleProduct A = -1

def SameSignPattern (A B : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ i j : Fin 3, i ≠ j → signum (A i j) = signum (B i j)

lemma triangle_cyclePairs :
    cyclePairs ([0, 1, 2] : List (Fin 3)) = [(0, 1), (1, 2), (2, 0)] :=
  rfl

lemma FullySupportedTriangle.signum_pm {A : Matrix (Fin 3) (Fin 3) ℝ}
    (h : FullySupportedTriangle A) (i j : Fin 3) (hij : i ≠ j) :
    signum (A i j) = 1 ∨ signum (A i j) = -1 :=
  signum_eq_pm (h i j hij)

lemma signum_pm {s : ℝ} (hs : s = 1 ∨ s = -1) : signum s = s := by
  rcases hs with hs | hs <;> simp [hs, signum]

lemma signum_two_mul_pm {s : ℝ} (hs : s = 1 ∨ s = -1) : signum (2 * s) = s := by
  rcases hs with hs | hs
  · rw [hs]; simp [signum]
  · rw [hs]; simp [signum]

/-- Signature that pushes a fully supported triangle toward nonpositive off-diagonals. -/
def reducingSignature (A : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal fun i =>
    if i = 0 then 1 else if i = 1 then -signum (A 0 1) else -signum (A 0 2)

lemma reducingSignature_isSignature {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hfull : FullySupportedTriangle A) : IsSignature (reducingSignature A) := by
  refine isSignature_diagonal fun i => ?_
  fin_cases i
  · simp
  · simp
    rcases hfull.signum_pm 0 1 (by decide) with h | h <;> simp [h]
  · simp
    rcases hfull.signum_pm 0 2 (by decide) with h | h <;> simp [h]

lemma reducingSignature_apply {A : Matrix (Fin 3) (Fin 3) ℝ} :
    (reducingSignature A) 0 0 = 1 ∧
    (reducingSignature A) 1 1 = -signum (A 0 1) ∧
    (reducingSignature A) 2 2 = -signum (A 0 2) := by
  simp [reducingSignature]

lemma signum_mul_self_of_ne {x : ℝ} (hx : x ≠ 0) : (-signum x) * x = -|x| := by
  rcases signum_eq_pm hx with h | h
  · have hp : 0 < x := pos_of_signum_one h
    rw [h, abs_of_pos hp]; ring
  · have hn : x < 0 := neg_of_signum_neg_one h
    rw [h, abs_of_neg hn]; ring

lemma reducing_pair_nonpos {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.PosDef)
    (hfull : FullySupportedTriangle A) (hanti : IsAntibalancedTriangle A) :
    signatureCongr (reducingSignature A) A 0 1 ≤ 0 ∧
    signatureCongr (reducingSignature A) A 0 2 ≤ 0 ∧
    signatureCongr (reducingSignature A) A 1 0 ≤ 0 ∧
    signatureCongr (reducingSignature A) A 1 2 ≤ 0 ∧
    signatureCongr (reducingSignature A) A 2 0 ≤ 0 ∧
    signatureCongr (reducingSignature A) A 2 1 ≤ 0 := by
  have hD := reducingSignature_isSignature hfull
  have ⟨h00, h11, h22⟩ := reducingSignature_apply (A := A)
  have hsym : A.IsSymm := (Matrix.isHermitian_iff_isSymm (α := ℝ)).mp hA.isHermitian
  have hne01 : A 0 1 ≠ 0 := hfull 0 1 (by decide)
  have hne02 : A 0 2 ≠ 0 := hfull 0 2 (by decide)
  have h20 : signum (A 2 0) = signum (A 0 2) := by
    rw [(hsym.apply 2 0).symm]
  have hprod : signum (A 0 1) * signum (A 0 2) * signum (A 1 2) = -1 := by
    have := hanti
    simp [IsAntibalancedTriangle, triangleCycleProduct] at this
    rw [h20] at this
    convert this using 1
    ring
  have h12le : signum (A 0 1) * signum (A 0 2) * A 1 2 ≤ 0 := by
    rcases hfull.signum_pm 1 2 (by decide) with h12 | h12
    · have hp : 0 < A 1 2 := pos_of_signum_one h12
      have : signum (A 0 1) * signum (A 0 2) = -1 := by
        rw [h12] at hprod; nlinarith
      nlinarith
    · have hn : A 1 2 < 0 := neg_of_signum_neg_one h12
      have : signum (A 0 1) * signum (A 0 2) = 1 := by
        rw [h12] at hprod; nlinarith
      nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [IsSignature.congr_apply hD, h00, h11]
    have : (-signum (A 0 1)) * A 0 1 = -|A 0 1| := signum_mul_self_of_ne hne01
    nlinarith [abs_nonneg (A 0 1)]
  · rw [IsSignature.congr_apply hD, h00, h22]
    have : (-signum (A 0 2)) * A 0 2 = -|A 0 2| := signum_mul_self_of_ne hne02
    nlinarith [abs_nonneg (A 0 2)]
  · rw [IsSignature.congr_apply hD, h11, h00, (hsym.apply 1 0).symm]
    have : (-signum (A 0 1)) * A 0 1 = -|A 0 1| := signum_mul_self_of_ne hne01
    nlinarith [abs_nonneg (A 0 1)]
  · rw [IsSignature.congr_apply hD, h11, h22]
    convert h12le using 1
    ring
  · rw [IsSignature.congr_apply hD, h22, h00, (hsym.apply 2 0).symm]
    have : (-signum (A 0 2)) * A 0 2 = -|A 0 2| := signum_mul_self_of_ne hne02
    nlinarith [abs_nonneg (A 0 2)]
  · rw [IsSignature.congr_apply hD, h22, h11, (hsym.apply 2 1).symm]
    convert h12le using 1
    ring

/-- Colbrook Proposition 8, \(n=3\): antibalance yields a Stieltjes signature. -/
theorem exists_signature_stieltjes_of_antibalanced_triangle
    {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.PosDef) (hfull : FullySupportedTriangle A)
    (hanti : IsAntibalancedTriangle A) :
    ∃ D, IsSignature D ∧ IsStieltjes (signatureCongr D A) := by
  refine ⟨reducingSignature A, reducingSignature_isSignature hfull, ?_⟩
  have hD := reducingSignature_isSignature hfull
  have hPD := signatureCongr_posDef hD hA
  refine ⟨hPD, ?_⟩
  intro i j hij
  have h := reducing_pair_nonpos hA hfull hanti
  fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
  · simpa using h.1
  · simpa using h.2.1
  · simpa using h.2.2.1
  · simpa using h.2.2.2.1
  · simpa using h.2.2.2.2.1
  · simpa using h.2.2.2.2.2

theorem nystromError_supermodular_of_antibalanced_triangle
    {A : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.PosDef) (hfull : FullySupportedTriangle A)
    (hanti : IsAntibalancedTriangle A) :
    Supermodular (nystromError A) := by
  obtain ⟨D, hD, hS⟩ := exists_signature_stieltjes_of_antibalanced_triangle hA hfull hanti
  exact nystromError_supermodular_of_signature_stieltjes hD hS hA

lemma Msharp_toReal_posDef : (toReal Msharp).PosDef := by
  rw [Msharp_toReal_eq]
  have hL := Lsharp_posDef
  have hI : (1 : Matrix (Fin 3) (Fin 3) ℝ).PosDef := Matrix.PosDef.one
  exact hL.add hI

lemma Msharp_fullySupported : FullySupportedTriangle (toReal Msharp) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | simp [toReal, Msharp]

lemma Msharp_not_antibalanced : ¬ IsAntibalancedTriangle (toReal Msharp) := by
  simp [IsAntibalancedTriangle, triangleCycleProduct, toReal, Msharp, signum]
  norm_num

lemma Msharp_cycle_product : triangleCycleProduct (toReal Msharp) = 1 := by
  simp [triangleCycleProduct, toReal, Msharp, signum]
  norm_num

/-- Signature matching a target (non-antibalanced) pattern to \(M^\sharp\). -/
def matchingSignature (A : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal fun i =>
    if i = 0 then 1
    else if i = 1 then signum (A 0 1)
    else -signum (A 0 2)

lemma matchingSignature_isSignature {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hfull : FullySupportedTriangle A) : IsSignature (matchingSignature A) := by
  refine isSignature_diagonal fun i => ?_
  fin_cases i
  · simp
  · simp
    exact hfull.signum_pm 0 1 (by decide)
  · simp
    rcases hfull.signum_pm 0 2 (by decide) with h | h <;> simp [h]

lemma matching_diag (A : Matrix (Fin 3) (Fin 3) ℝ) :
    (matchingSignature A) 0 0 = 1 ∧
    (matchingSignature A) 1 1 = signum (A 0 1) ∧
    (matchingSignature A) 2 2 = -signum (A 0 2) := by
  simp [matchingSignature]

lemma triangleCycleProduct_eq_pm {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hfull : FullySupportedTriangle A) :
    triangleCycleProduct A = 1 ∨ triangleCycleProduct A = -1 := by
  rcases hfull.signum_pm 0 1 (by decide) with a | a <;>
    rcases hfull.signum_pm 1 2 (by decide) with b | b <;>
      rcases hfull.signum_pm 2 0 (by decide) with c | c <;>
        simp [triangleCycleProduct, a, b, c]

lemma signum_one_mul {s x : ℝ} (hs : s = 1 ∨ s = -1) (hx : 0 < x) :
    signum (s * x) = s := by
  rcases hs with hs | hs
  · rw [hs, one_mul, signum_pos hx]
  · rw [hs, signum_neg (by nlinarith [hx])]

lemma signum_neg_one_mul {s x : ℝ} (hs : s = 1 ∨ s = -1) (hx : x < 0) :
    signum (s * x) = -s := by
  rcases hs with hs | hs
  · rw [hs, one_mul, signum_neg hx]
  · rw [hs, signum_pos (by nlinarith [hx])]; norm_num

lemma matchingSignature_same_pattern {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hfull : FullySupportedTriangle A) (hsym : A.IsSymm)
    (hnot : ¬ IsAntibalancedTriangle A) :
    SameSignPattern A (signatureCongr (matchingSignature A) (toReal Msharp)) := by
  have hD := matchingSignature_isSignature hfull
  have ⟨h00, h11, h22⟩ := matching_diag A
  have hprod : triangleCycleProduct A = 1 :=
    (triangleCycleProduct_eq_pm hfull).resolve_right hnot
  have h20 : signum (A 2 0) = signum (A 0 2) := by
    rw [(hsym.apply 2 0).symm]
  have h12sign : signum (A 1 2) = signum (A 0 1) * signum (A 0 2) := by
    have : signum (A 0 1) * signum (A 1 2) * signum (A 2 0) = 1 := hprod
    rw [h20] at this
    rcases hfull.signum_pm 0 1 (by decide) with a | a <;>
      rcases hfull.signum_pm 0 2 (by decide) with b | b <;>
        rcases hfull.signum_pm 1 2 (by decide) with c | c <;>
          simp [a, b, c] at this ⊢ <;> linarith
  have hs01 := hfull.signum_pm 0 1 (by decide)
  have hs02 := hfull.signum_pm 0 2 (by decide)
  have hs12 := hfull.signum_pm 1 2 (by decide)
  have hs10 : signum (A 1 0) = signum (A 0 1) := by rw [(hsym.apply 1 0).symm]
  have hs21 : signum (A 2 1) = signum (A 1 2) := by rw [(hsym.apply 2 1).symm]
  have e01 : signum (A 0 1) =
      signum (signatureCongr (matchingSignature A) (toReal Msharp) 0 1) := by
    rw [IsSignature.congr_apply hD, h00, h11]
    simp [toReal, Msharp]
    exact (signum_pm hs01).symm
  have e02 : signum (A 0 2) =
      signum (signatureCongr (matchingSignature A) (toReal Msharp) 0 2) := by
    rw [IsSignature.congr_apply hD, h00, h22]
    simp [toReal, Msharp]
    exact (signum_two_mul_pm hs02).symm
  have e10 : signum (A 1 0) =
      signum (signatureCongr (matchingSignature A) (toReal Msharp) 1 0) := by
    rw [IsSignature.congr_apply hD, h11, h00]
    simp [toReal, Msharp, hs10]
    exact (signum_pm hs01).symm
  have e12 : signum (A 1 2) =
      signum (signatureCongr (matchingSignature A) (toReal Msharp) 1 2) := by
    rw [IsSignature.congr_apply hD, h11, h22]
    have hM : toReal Msharp 1 2 = -2 := by simp [toReal, Msharp]
    rw [hM, h12sign]
    have hre : signum (A 0 1) * (-2) * (-signum (A 0 2)) =
        2 * (signum (A 0 1) * signum (A 0 2)) := by ring
    rw [hre]
    have hs : signum (A 0 1) * signum (A 0 2) = 1 ∨
        signum (A 0 1) * signum (A 0 2) = -1 := by
      rcases hs01 with a | a <;> rcases hs02 with b | b <;> simp [a, b]
    exact (signum_two_mul_pm hs).symm
  have e20 : signum (A 2 0) =
      signum (signatureCongr (matchingSignature A) (toReal Msharp) 2 0) := by
    rw [IsSignature.congr_apply hD, h22, h00]
    simp [toReal, Msharp, h20]
    rw [mul_comm]
    exact (signum_two_mul_pm hs02).symm
  have e21 : signum (A 2 1) =
      signum (signatureCongr (matchingSignature A) (toReal Msharp) 2 1) := by
    rw [IsSignature.congr_apply hD, h22, h11]
    have hM : toReal Msharp 2 1 = -2 := by simp [toReal, Msharp]
    rw [hM, hs21, h12sign]
    have hre : (-signum (A 0 2)) * (-2) * signum (A 0 1) =
        2 * (signum (A 0 1) * signum (A 0 2)) := by ring
    rw [hre]
    have hs : signum (A 0 1) * signum (A 0 2) = 1 ∨
        signum (A 0 1) * signum (A 0 2) = -1 := by
      rcases hs01 with a | a <;> rcases hs02 with b | b <;> simp [a, b]
    exact (signum_two_mul_pm hs).symm
  intro i j hij
  fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
  · simpa using e01
  · simpa using e02
  · simpa using e10
  · simpa using e12
  · simpa using e20
  · simpa using e21

theorem exists_not_supermodular_of_triangle_not_antibalanced
    {A : Matrix (Fin 3) (Fin 3) ℝ} (hfull : FullySupportedTriangle A)
    (hsym : A.IsSymm) (hnot : ¬ IsAntibalancedTriangle A) :
    ∃ A' : Matrix (Fin 3) (Fin 3) ℝ, A'.PosDef ∧ SameSignPattern A A' ∧
      ¬ Supermodular (nystromError A') := by
  refine ⟨signatureCongr (matchingSignature A) (toReal Msharp), ?_, ?_, ?_⟩
  · exact signatureCongr_posDef (matchingSignature_isSignature hfull) Msharp_toReal_posDef
  · exact matchingSignature_same_pattern hfull hsym hnot
  · have hD := matchingSignature_isSignature hfull
    have hfun : nystromError (signatureCongr (matchingSignature A) (toReal Msharp)) =
        nystromError (toReal Msharp) :=
      funext fun S => nystromError_signatureCongr hD Msharp_toReal_posDef S
    simpa [hfun] using not_supermodular_nystromError_Msharp

/-- Colbrook Corollary 13: on a fully supported triangle, every
positive-definite realization has supermodular inverse-trace if and only
if the sign pattern is antibalanced. -/
theorem triangle_pd_nystrom_supermodular_iff_antibalanced
    {A : Matrix (Fin 3) (Fin 3) ℝ} (hfull : FullySupportedTriangle A)
    (hsym : A.IsSymm) :
    (∀ A' : Matrix (Fin 3) (Fin 3) ℝ, A'.PosDef → SameSignPattern A A' →
      Supermodular (nystromError A')) ↔
    IsAntibalancedTriangle A := by
  constructor
  · intro hall
    by_contra hnot
    obtain ⟨A', hPD, hpat, hns⟩ :=
      exists_not_supermodular_of_triangle_not_antibalanced hfull hsym hnot
    exact hns (hall A' hPD hpat)
  · intro hanti A' hPD hpat
    have hfull' : FullySupportedTriangle A' := by
      intro i j hij
      have h := hpat i j hij
      have hA : signum (A i j) = 1 ∨ signum (A i j) = -1 := hfull.signum_pm i j hij
      intro hz
      have hz0 : signum (A' i j) = 0 := by rw [hz]; simp [signum]
      rw [hz0] at h
      rcases hA with hA | hA <;> (rw [hA] at h; norm_num at h)
    have hanti' : IsAntibalancedTriangle A' := by
      have : triangleCycleProduct A' = triangleCycleProduct A := by
        simp [triangleCycleProduct, hpat 0 1 (by decide), hpat 1 2 (by decide),
          hpat 2 0 (by decide)]
      simpa [IsAntibalancedTriangle, this] using hanti
    exact nystromError_supermodular_of_antibalanced_triangle hPD hfull' hanti'

/-! ## Sanity checks -/

def signFlip2 : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, 1, 0; 0, 0, -1]

lemma signFlip2_isSignature : IsSignature signFlip2 := by
  refine ⟨?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | simp [signFlip2]
  · intro i
    fin_cases i <;> simp [signFlip2]

lemma pathM3_isSymm : pathM3.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pathM3, pathLap3]

lemma pathM3_quadratic (x : Fin 3 → ℝ) :
    dotProduct (star x) (Matrix.mulVec (toReal pathM3) x) =
      (x 0 - x 1) ^ 2 + (x 1 - x 2) ^ 2 + x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  simp [dotProduct, Matrix.mulVec, toReal, pathM3, pathLap3, Fin.sum_univ_three,
    Pi.star_apply]
  ring

lemma pathM3_toReal_isStieltjes : IsStieltjes (toReal pathM3) := by
  refine ⟨?_, ?_⟩
  · refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
    · rw [Matrix.isHermitian_iff_isSymm]
      exact toReal_isSymm pathM3_isSymm
    · intro x hx
      have hform := pathM3_quadratic x
      have hsq : 0 ≤ (x 0 - x 1) ^ 2 + (x 1 - x 2) ^ 2 + x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
        nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 1 - x 2),
          sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
      have hpos :
          0 < (x 0 - x 1) ^ 2 + (x 1 - x 2) ^ 2 + x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
        by_contra h
        have hz :
            (x 0 - x 1) ^ 2 + (x 1 - x 2) ^ 2 + x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 0 :=
          le_antisymm (le_of_not_gt h) hsq
        have hx0 : x 0 = 0 := by
          nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 1 - x 2),
            sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
        have hx1 : x 1 = 0 := by
          nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 1 - x 2),
            sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
        have hx2 : x 2 = 0 := by
          nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 1 - x 2),
            sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
        apply hx
        funext k
        fin_cases k <;> assumption
      rw [hform]
      exact hpos
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim |
      simp [toReal, pathM3, pathLap3]

lemma pathM3_toReal_posDef : (toReal pathM3).PosDef :=
  pathM3_toReal_isStieltjes.posDef

/-- Flipping the sign of index 2 on a path Laplacian stays supermodular. -/
theorem pathM3_signature_flip_supermodular :
    Supermodular (nystromError (signatureCongr signFlip2 (toReal pathM3))) := by
  have hD := signFlip2_isSignature
  have hM : signatureCongr signFlip2 (signatureCongr signFlip2 (toReal pathM3)) =
      toReal pathM3 := hD.congr_congr
  have hS : IsStieltjes (signatureCongr signFlip2
      (signatureCongr signFlip2 (toReal pathM3))) := by
    rw [hM]
    exact pathM3_toReal_isStieltjes
  refine nystromError_supermodular_of_signature_stieltjes hD hS ?_
  exact signatureCongr_posDef hD pathM3_toReal_posDef

theorem Lsharp_not_antibalanced_pattern : ¬ IsAntibalancedTriangle (toReal Msharp) :=
  Msharp_not_antibalanced

end
end NystromSubmodularity
