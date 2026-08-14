import NystromSubmodularity.Computable
import NystromSubmodularity.Counterexamples.SDDDim3
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

/-!
# Phase 1 — Lean-native exploration

Hand-written exact `ℚ` SDDM instances (path/cycle graph Laplacians plus a
positive diagonal shift) and certified exhaustive four-point checks of
`cramerTraceInv` supermodularity. The SDD signed triangle is imported from
`Counterexamples.SDDDim3`.

Module comment (SPEC §2.4): SDDM held on all tested \(n\le 5\); SDD fails at
\(n=3\) with a signed triangle. Phase 2 packages that obstruction and proves
inverse-trace supermodularity on Stieltjes matrices in general.
-/

namespace NystromSubmodularity
namespace Phase1

open Matrix Finset Counterexamples

/-! ## SDDM instances -/

/-- Path Laplacian on 3 vertices. -/
def pathLap3 : Matrix (Fin 3) (Fin 3) ℚ :=
  !![1, -1, 0; -1, 2, -1; 0, -1, 1]

/-- Cycle Laplacian on 3 vertices. -/
def cycleLap3 : Matrix (Fin 3) (Fin 3) ℚ :=
  !![2, -1, -1; -1, 2, -1; -1, -1, 2]

/-- Path Laplacian on 4 vertices. -/
def pathLap4 : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1, -1, 0, 0; -1, 2, -1, 0; 0, -1, 2, -1; 0, 0, -1, 1]

/-- Cycle Laplacian on 4 vertices. -/
def cycleLap4 : Matrix (Fin 4) (Fin 4) ℚ :=
  !![2, -1, 0, -1; -1, 2, -1, 0; 0, -1, 2, -1; -1, 0, -1, 2]

/-- Path Laplacian on 5 vertices. -/
def pathLap5 : Matrix (Fin 5) (Fin 5) ℚ :=
  !![1, -1, 0, 0, 0;
     -1, 2, -1, 0, 0;
     0, -1, 2, -1, 0;
     0, 0, -1, 2, -1;
     0, 0, 0, -1, 1]

/-- Cycle Laplacian on 5 vertices. -/
def cycleLap5 : Matrix (Fin 5) (Fin 5) ℚ :=
  !![2, -1, 0, 0, -1;
     -1, 2, -1, 0, 0;
     0, -1, 2, -1, 0;
     0, 0, -1, 2, -1;
     -1, 0, 0, -1, 2]

/-- A strictly diagonally dominant Stieltjes matrix. -/
def strictStieltjes3 : Matrix (Fin 3) (Fin 3) ℚ :=
  !![3, -1, -1; -1, 3, -1; -1, -1, 3]

def pathM3 : Matrix (Fin 3) (Fin 3) ℚ := pathLap3 + 1
def cycleM3 : Matrix (Fin 3) (Fin 3) ℚ := cycleLap3 + 1
def pathM4 : Matrix (Fin 4) (Fin 4) ℚ := pathLap4 + 1
def cycleM4 : Matrix (Fin 4) (Fin 4) ℚ := cycleLap4 + 1
def pathM5 : Matrix (Fin 5) (Fin 5) ℚ := pathLap5 + 1
def cycleM5 : Matrix (Fin 5) (Fin 5) ℚ := cycleLap5 + 1

theorem pathLap3_isSDDM : IsSDDM pathLap3 := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [pathLap3]
  · intro i; fin_cases i <;> native_decide
  · intro i; fin_cases i <;> native_decide
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | native_decide

theorem cycleLap3_isSDDM : IsSDDM cycleLap3 := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [cycleLap3]
  · intro i; fin_cases i <;> native_decide
  · intro i; fin_cases i <;> native_decide
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | native_decide

theorem pathLap4_isSDDM : IsSDDM pathLap4 := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [pathLap4]
  · intro i; fin_cases i <;> native_decide
  · intro i; fin_cases i <;> native_decide
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | native_decide

theorem cycleLap4_isSDDM : IsSDDM cycleLap4 := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [cycleLap4]
  · intro i; fin_cases i <;> native_decide
  · intro i; fin_cases i <;> native_decide
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | native_decide

theorem pathLap5_isSDDM : IsSDDM pathLap5 := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [pathLap5]
  · intro i; fin_cases i <;> native_decide
  · intro i; fin_cases i <;> native_decide
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | native_decide

theorem cycleLap5_isSDDM : IsSDDM cycleLap5 := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [cycleLap5]
  · intro i; fin_cases i <;> native_decide
  · intro i; fin_cases i <;> native_decide
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | native_decide

theorem strictStieltjes3_isSDDM : IsSDDM strictStieltjes3 := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [strictStieltjes3]
  · intro i; fin_cases i <;> native_decide
  · intro i; fin_cases i <;> native_decide
  · intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | native_decide

/-! ## Exhaustive inverse-trace supermodularity (SDDM) -/

theorem pathM3_traceInv_supermodular :
    ∀ A B : Finset (Fin 3), 0 ≤ cramerSupermodularDiff pathM3 A B := by
  native_decide

theorem cycleM3_traceInv_supermodular :
    ∀ A B : Finset (Fin 3), 0 ≤ cramerSupermodularDiff cycleM3 A B := by
  native_decide

theorem strictStieltjes3_traceInv_supermodular :
    ∀ A B : Finset (Fin 3), 0 ≤ cramerSupermodularDiff strictStieltjes3 A B := by
  native_decide

theorem pathM4_traceInv_supermodular :
    ∀ A B : Finset (Fin 4), 0 ≤ cramerSupermodularDiff pathM4 A B := by
  native_decide

theorem cycleM4_traceInv_supermodular :
    ∀ A B : Finset (Fin 4), 0 ≤ cramerSupermodularDiff cycleM4 A B := by
  native_decide

-- n=5: 32² = 1024 pairs. Kept as a native check; if this is too slow in CI,
-- the n≤4 theorems already certify the pattern.
theorem pathM5_traceInv_supermodular :
    ∀ A B : Finset (Fin 5), 0 ≤ cramerSupermodularDiff pathM5 A B := by
  native_decide

theorem cycleM5_traceInv_supermodular :
    ∀ A B : Finset (Fin 5), 0 ≤ cramerSupermodularDiff cycleM5 A B := by
  native_decide

/-! ## SDD failure (re-exported discovery) -/

theorem L0_isSDD_phase1 : IsSDD L0 := L0_isSDD

theorem L0_delta_neg_phase1 :
    cramerNystromError M0 (∅ : Finset (Fin 3)) +
        cramerNystromError M0 ({0, 1} : Finset (Fin 3)) <
      cramerNystromError M0 ({0} : Finset (Fin 3)) +
        cramerNystromError M0 ({1} : Finset (Fin 3)) :=
  M0_delta_neg

theorem L0_delta_eq : cramerNystromSupermodularDiff M0 ({0} : Finset (Fin 3)) {1} = -7 / 2040 :=
  M0_delta

end Phase1
end NystromSubmodularity
