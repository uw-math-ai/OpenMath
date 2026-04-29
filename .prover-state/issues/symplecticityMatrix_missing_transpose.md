# Issue: `symplecticityMatrix` is defined without a transpose, restricting algebraic stability to symmetric `A`

## Resolution (cycle 034) — RESOLVED

Solution 1 (the recommended fix) was applied:

* `OpenMath/Chapter3/Section370.lean:55–58` — the second `R.A` is now
  `R.A.transpose`, so `symplecticityMatrix R` unfolds entry-wise to the
  textbook form `m_{ij} = b_i a_{ij} + b_j a_{ji} − b_i b_j`.
* `OpenMath/Chapter3/Section370.lean:81` —
  `implicitMidpoint_isSymplectic` still goes through (the `s = 1` 1×1
  case is invariant under transpose); only `Matrix.transpose_apply` was
  added to the simp set for clarity.
* `OpenMath/Chapter3/Section357.lean` —
  `algebraicallyStable_imp_A_symm` was deleted (no longer provable, no
  longer needed), and the `hSym` hypothesis on
  `symplecticityMatrix_quadratic_form_eq` was dropped. The proof of
  the lemma now uses an `i ↔ j` index-swap argument that works for
  every `RKTableau`. The call site in
  `algebraicallyStable_isBNStable` was updated to pass one fewer
  argument.

After the fix, `IsAlgebraicallyStable` no longer silently entails
symmetric `A`, so the predicate covers all RK methods (including
explicit and Gauss–Legendre methods of order ≥ 4) as the textbook
intends. The cycle-033 `algebraicallyStable_isBNStable` proof was
preserved end-to-end with simpler intermediate lemmas; axioms are
unchanged at `[propext, Classical.choice, Quot.sound]`.

Predecessor commit: `903c17bb`. The cycle-034 fix commit follows.

## Blocker

The current definition (cycle 027, `OpenMath/Chapter3/Section370.lean:55–58`)

```lean
def symplecticityMatrix {s : ℕ} (R : RKTableau s) :
    Matrix (Fin s) (Fin s) ℝ :=
  Matrix.diagonal R.b * R.A + R.A * Matrix.diagonal R.b -
    Matrix.vecMulVec R.b R.b
```

unfolds entrywise to

`(symplecticityMatrix R) i j = R.b i * R.A i j + R.A i j * R.b j - R.b i * R.b j
                             = (R.b i + R.b j) * R.A i j - R.b i * R.b j`.

Butcher's textbook formula (Burrage–Butcher §357d, also called the
algebraic-stability matrix) is

`m_{ij} = b_i a_{ij} + b_j a_{ji} - b_i b_j`

which corresponds to `M = diag(b) A + Aᵀ diag(b) - bbᵀ` (note the
**transpose** on the second `A`). The Lean version is missing the
transpose.

## Why this matters

The textbook `m_{ij}` is automatically symmetric in `(i, j)`. The Lean
version is symmetric only when `A` is itself symmetric (`A i j = A j i`).
Since `Matrix.PosSemidef` requires `IsHermitian` (= symmetric over ℝ),
`(symplecticityMatrix R).PosSemidef` together with `b i > 0` forces
`A i j = A j i` for all `i, j`. This silently restricts
`IsAlgebraicallyStable R` to RK methods with **symmetric A** —
excluding for example all explicit RK methods (which have lower
triangular A) and most implicit RK methods of practical interest
(e.g., Gauss–Legendre methods of order ≥ 4 do not have symmetric A).

For the implicit midpoint method (`s = 1`) the difference is invisible
because the single entry `A 0 0` is trivially "symmetric", which is
why cycles 027 and 028 did not catch the bug.

## Context

Discovered in cycle 033 while proving `thm:357C`
(`algebraicallyStable_isBNStable`). The textbook proof uses the
symmetric form `b_i a_{ij} + b_j a_{ji} - b_i b_j`. With the Lean form,
the theorem still holds — but only because the PSD assumption silently
forces `A` symmetric, and under that hypothesis the two forms agree
when summed against the symmetric Gram matrix `⟨F_i, F_j⟩`.

This was worked around in cycle 033 by deriving `A i j = A j i` from
`IsAlgebraicallyStable M` (lemma `algebraicallyStable_imp_A_symm` in
`Section357.lean`) and using it as a hypothesis in
`symplecticityMatrix_quadratic_form_eq` (Lemma 1 of the §357C proof).

## What was tried

- The cycle 033 strategy claimed `symplecticityMatrix M i j` unfolds to
  `b_i a_{ij} + b_j a_{ji} - b_i b_j` (the textbook form). A direct
  `simp [symplecticityMatrix, Matrix.diagonal, Matrix.vecMulVec,
  Matrix.mul_apply]` test confirms it actually unfolds to
  `b_i a_{ij} + a_{ij} b_j - b_i b_j = (b_i + b_j) a_{ij} - b_i b_j`,
  contradicting the strategy and the textbook.
- A two-stage counterexample (`s = 2`, `b = (1, 2)`, `A = ((0,1),(0,0))`,
  `F = (e1, e1+e2)`) confirmed the two forms differ as quadratic forms
  on a symmetric Gram matrix when `A` is not symmetric.

## Possible solutions

1. **Fix the definition (preferred)**: replace
   `R.A * Matrix.diagonal R.b` with `R.A.transpose * Matrix.diagonal R.b`.
   This requires updating:
   - `OpenMath/Chapter3/Section370.lean` (`symplecticityMatrix` and
     `implicitMidpoint_isSymplectic` — for `s = 1` the proof only needs
     a one-line change).
   - The `Section370.lean` comment about the entry-wise form (already
     claims the textbook form, so the comment is correct after the fix).
   - `OpenMath/Chapter3/Section357.lean`
     `implicitMidpoint_isAlgebraicallyStable` — it relies on the cycle
     027 `implicitMidpoint_isSymplectic` fact that the symplecticity
     matrix vanishes; that still holds for `s = 1`.
   - Cycle 033's `algebraicallyStable_isBNStable` proof — `Lemma 1`
     would no longer need the `A` symmetric hypothesis; the statement
     would simplify to a direct unfolding identity, and the
     `algebraicallyStable_imp_A_symm` helper could be removed (or kept
     as a corollary for users who want to extract `A` symmetric).

2. **Add a corrected parallel definition**: introduce
   `symplecticityMatrixSym` (the textbook form) and a lemma
   `symplecticityMatrix_eq_symplecticityMatrixSym_of_symm` saying the
   two agree when `A` is symmetric. Less invasive but creates a
   long-term maintenance burden and a confusing two-name situation.

3. **Document the restriction** (status quo, what cycle 033 did): keep
   the buggy definition, document that algebraic stability silently
   imposes `A` symmetric, and rely on
   `algebraicallyStable_imp_A_symm` to bridge the gap. Functional but
   makes `IsAlgebraicallyStable` semantically stronger than the
   textbook (excludes most useful methods).

## Recommendation

Solution 1 in the next planner cycle. The fix is local
(one definition + one cycle-027 proof one-liner) and the existing
cycle-033 proof of `thm:357C` would simplify rather than break.
