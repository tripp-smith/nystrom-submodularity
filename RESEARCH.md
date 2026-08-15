# Remaining research threads

The original [SPEC.md](SPEC.md) and Colbrook Theorem 1 are complete. This
note is the specification for the seven leftovers recorded in
`FINDINGS.md`. Each thread has a Lean delivery, the same verification
cadence (`lake build`, no `sorry`, Lean-default axioms on public
theorems), and a documentation update.

Wikipedia supermodularity names are used throughout.

## Success criteria

| Thread | Delivery |
|--------|----------|
| 1 Other losses | Frobenius, operator-norm, and residual-quadratic (“prediction”) errors on \(M_0\); nuclear is not the only loss that fails |
| 2 Census | Finite certified counts: Colbrook-family rational grid; 64 integer strict-SDD triangles |
| 3 Singular \(\gamma=0\) | SDDM is PSD; unshifted path Laplacian is singular; Nyström error on proper complements is well-defined and the nonempty-base four-point stays nonnegative |
| 4 SVD / nuclear API | Hermitian nuclear norm \(\sum_i\|\lambda_i\|\) via mathlib eigenvalues; equals trace on PSD matrices |
| 5 Mathlib extraction | `MathlibReady.lean` + `MATHLIB.md` packaging the Stieltjes / four-point lemmas |
| 6 Neumann | Stieltjes splitting \(B=sI-M\ge 0\); length-1 modular and length-2 supermodular walk traces |
| 7 Perturbation | Explicit neighborhood of \(M_0\) keeps a negative defect; scale invariance already in the library |

Intentional after this note: a general approximate-submodularity *ratio*
for arbitrary perturbations; a full `LinearMap.singularValues` wrapper;
an infinite Neumann series equaling the inverse; opening an actual
mathlib PR on `leanprover-community/mathlib4`.

## Verification (every thread)

- `lake build` sorry-free
- `rg sorry --glob '*.lean'` empty
- `#print axioms` on structural theorems: `propext`, `Classical.choice`,
  `Quot.sound`. Cramer evaluations (Frobenius / prediction traces, the
  64-matrix census, path-Laplacian principals, ridge defects) use
  `native_decide`, as the existing \(n\le 5\) SDDM checks do.
- Independent rational check when a closed form is claimed
