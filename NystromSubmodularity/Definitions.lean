import Mathlib

/-!
# Core definitions for Problem 4.6

This file collects the basic definitions used throughout the project:
submodular set functions and the diagonal-dominance predicates `IsSDD` /
`IsSDDM` on real matrices. These are intentionally lightweight scaffolding
definitions; the analytic objects (resolvent, Schur complement, Nyström
residual, nuclear norm) are developed on top of them in later phases.
-/

namespace NystromSubmodularity

open scoped BigOperators

variable {α : Type*}

/-- A real-valued set function `f` is *submodular* when for all sets `A`, `B`
we have `f A + f B ≥ f (A ∪ B) + f (A ∩ B)`. -/
def Submodular [DecidableEq α] (f : Finset α → ℝ) : Prop :=
  ∀ A B : Finset α, f A + f B ≥ f (A ∪ B) + f (A ∩ B)

/-- Constant set functions are (trivially) submodular. A tiny sanity lemma that
also exercises the mathlib-backed build end to end. -/
theorem submodular_const [DecidableEq α] (c : ℝ) :
    Submodular (fun _ : Finset α => c) := by
  intro A B
  simp

namespace Matrix

variable {n : ℕ}

/-- `M` is (weakly) diagonally dominant: each diagonal entry dominates the sum
of the absolute values of the off-diagonal entries in its row. -/
def IsDiagDominant (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i, ∑ j ∈ Finset.univ.erase i, |M i j| ≤ |M i i|

/-- Symmetric diagonally dominant matrix (SDD). -/
def IsSDD (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  M.IsSymm ∧ IsDiagDominant M

/-- Symmetric diagonally dominant M-matrix (SDDM): an SDD matrix with positive
diagonal and non-positive off-diagonal entries. -/
def IsSDDM (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsSDD M ∧ (∀ i, 0 < M i i) ∧ (∀ i j, i ≠ j → M i j ≤ 0)

theorem IsSDDM.isSDD {M : Matrix (Fin n) (Fin n) ℝ} (h : IsSDDM M) : IsSDD M :=
  h.1

end Matrix

end NystromSubmodularity
