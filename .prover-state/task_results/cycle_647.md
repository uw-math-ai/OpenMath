# Cycle 647 Results

## Worked on

§521 BDF PY-block characteristic polynomial in `OpenMath/LMMAsGLM.lean`.

## Approach

Ran the required companion-matrix audit before proving anything:

- `lean_leansearch "companion matrix characteristic polynomial"` returned only
  generic charpoly declarations such as `Matrix.charpoly.univ`,
  `Matrix.charpoly_fin_two`, `Matrix.charmatrix`, and Cayley-Hamilton/minpoly
  facts; no companion-matrix theorem.
- `lean_loogle "Matrix.companion"` returned no results.
- `lean_loogle "?M.charpoly = Polynomial.X ^ ?n - _"` returned unrelated
  facts, mainly `Matrix.charpoly_vecMulVec` and polynomial/minpoly examples.
- `lean_local_search "companion"` returned no local declarations.
- `lean_local_search "LinearRecurrence"` found only Mathlib's
  `LinearRecurrence` structure. Source inspection confirmed it has
  `LinearRecurrence.charPoly`, but no theorem identifying the charpoly of the
  `tupleSucc` companion matrix.
- Direct `rg` over Mathlib/OpenMath found no `Matrix.companion` or
  `charpoly_companion` theorem.

Because Step 1 had no usable companion-charpoly lemma, I used Step 2:
proved a private generic bottom-row companion charpoly theorem by induction on
the size. The proof expands `Matrix.charpoly` by `Matrix.det_succ_column_zero`;
the tail minor is the smaller companion charmatrix, and the final-row minor is
lower triangular with diagonal `-1`.

I also followed the Aristotle policy with one scratch scaffold submission:
project `cff5c78d-200f-4ed3-8a3f-a41e235f3fc8`. It was still `IN_PROGRESS`
at the single status check, so the landed proof is manual.

## Result

SUCCESS. Landed the headline theorem, sorry-free:

```lean
theorem toGLM_stabilityMatrixPY_charpoly_of_bdf
    (m : LMM s) (z : ℂ)
    (hbdf : ∀ l : Fin (s + 1), l ≠ Fin.last s → m.β l = 0)
    (hz : 1 - z * ((m.β (Fin.last s) : ℝ) : ℂ) ≠ 0) :
    (toGLM_stabilityMatrixPY m z).charpoly =
      (Polynomial.X : Polynomial ℂ) ^ s -
        ∑ l : Fin s,
          Polynomial.C
            (((-m.α (Fin.castSucc l) : ℝ) : ℂ) /
              (1 - z * ((m.β (Fin.last s) : ℝ) : ℂ))) *
            Polynomial.X ^ (l : ℕ)
```

Supporting private lemmas:

- `toGLM_stabilityMatrixPYCompanion`
- `toGLM_stabilityMatrixPYCompanion_charpoly`
- `toGLM_stabilityMatrixPY_eq_companion_of_bdf`

`lake env lean OpenMath/LMMAsGLM.lean` exits 0. `rg` finds no `sorry` or
`admit` in `OpenMath/LMMAsGLM.lean`. File length is 2648 lines, still below
the 2700 soft split threshold and the 3000 cycle cap.

## Dead ends

No Mathlib companion theorem was available. The nearest Mathlib object,
`LinearRecurrence.charPoly`, is only the polynomial definition and does not
come with a matrix charpoly theorem for `tupleSucc`.

## Discovery

The BDF PY block is exactly the bottom-row companion matrix after the
cycle-646 entry simp lemmas. The determinant induction that worked best is
column-0 expansion:

- removing row 0 / column 0 gives the companion charmatrix for the tail
  coefficients;
- removing the last row / column 0 gives a lower-triangular bidiagonal minor
  with determinant `(-1)^(s-1)`, producing the constant coefficient term.

## Suggested next approach

Define the polynomial-valued LMM stability polynomial for fixed `z` and prove
its evaluation agrees with the existing scalar `LMM.stabilityPoly`. Then use
`toGLM_stabilityMatrix_charpoly_of_bdf` together with
`toGLM_stabilityMatrixPY_charpoly_of_bdf` to bridge the BDF GLM root condition
back to the LMM stability polynomial.
