# Cycle 676 Results

## Worked on
§521 Step C.7 — General-RowF column closed forms in
`OpenMath/LMMAsGLM/StabilityCharpoly.lean`. Two new sorry-free
theorems landed, lifting cycle 674's PHF(0) charmatrix adjugate
last-column closed form into the two summands of
`toGLM_stabilityCharpolyRowF_eq_explicit`.

1. `toGLM_stabilityCharpolyRowF_β_summand_eq` — closed form of the
   β-summand:
   ```
   vecMul β (PY.charmatrix.det • PHF.charmatrix.adjugate) ⟨s-1⟩
     = PY.charpoly * ∑ k, β(k) * X^k
   ```
2. `toGLM_stabilityCharpolyRowF_α_summand_col_eq` — column ⟨s-1⟩
   closed form of the α-summand:
   ```
   vecMul (-α) (-PY.adj * (-PYHF.map C) * PHF.adj) ⟨s-1⟩
     = ∑ l, vecMul (-α) (-PY.adj * (-PYHF.map C)) l * X^l
   ```

## Approach

For the β-summand:
1. `Matrix.vecMul_smul` pulled the `PY.charmatrix.det` smul out of
   the matrix, turning `vecMul v (c • M) j` into `(c • vecMul v M) j`.
2. `Pi.smul_apply` + `smul_eq_mul` flattened the smul on the function
   to ordinary multiplication.
3. Identified `PY.charmatrix.det` with `PY.charpoly` (definitional).
4. `congr 1` reduced to the `vecMul` sum, which `show` exposed via
   the definitional unfolding of `Matrix.vecMul` to a `Finset.sum`.
5. `Finset.sum_congr rfl` + cycle 674's
   `toGLM_stabilityMatrixPHF_zero_charmatrix_adjugate_last_col`
   collapsed each entry to `X^k`.

For the α-summand:
1. `← Matrix.vecMul_vecMul` reassociated
   `v ᵥ* ((A * B) * C) = (v ᵥ* (A * B)) ᵥ* C`.
2. `show` exposed the resulting `vecMul ... ᵥ* PHF.adj ⟨s-1⟩` as a
   `Finset.sum` via `vecMul`/`dotProduct` definitional unfolding.
3. `Finset.sum_congr rfl` + cycle 674's adjugate column lemma closed
   each summand.

## Result
SUCCESS — both theorems landed sorry-free, file compiles cleanly via
`lake env lean OpenMath/LMMAsGLM/StabilityCharpoly.lean` (no errors,
no warnings).

## Dead ends
None this cycle — the strategy's recipe worked exactly as written.
The `Matrix.vecMul_smul` + `Pi.smul_apply` + `smul_eq_mul` path is
the clean way to extract a scalar `det` from a smul-matrix without
detouring through `dotProduct` rewrites.

## Discovery
- `Matrix.vecMul_smul (v : m → α) (b : R) (M : ...)` requires
  `[SMulCommClass R α α]`, which holds automatically for
  `R = α = Polynomial ℂ` (commutative ring acting on itself).
- `Matrix.vecMul v M j` is **definitionally** `∑ i, v i * M i j` via
  `vecMul = dotProduct ∘ transpose-column` and `dotProduct` unfolding.
  So `show ∑ k, ...` works without an explicit `rw [vecMul]` /
  `dotProduct` rewrite chain.
- `Matrix.vecMul_vecMul` is `v ᵥ* M ᵥ* N = v ᵥ* (M * N)`. Applying it
  with `← rw` reassociates a `v ᵥ* (M * N)` into the iterated form,
  exposing the column-projection seam needed for the cycle 674
  rewrite.

## Suggested next approach
Step 3 of the §521 program: combine the two new closed forms
through `toGLM_stabilityCharpolyRowF_eq_explicit` to land
```
toGLM_stabilityCharpolyRowF m
  = PY.charpoly * (∑ k, β(k) * X^k) + ∑ l, αRow(l) * X^l
```
where `αRow(l) := vecMul (-α) (-PY.adj * (-PYHF.map C)) l`. From
there, the next milestone is the X^s factorisation:
- `αRow(l)` is a polynomial in `X` of degree `≤ s - 1` (since
  `PY.adj` and `PYHF.map C` are size-`s` polynomial matrices),
- `∑ k, β(k) * X^k` is degree `≤ s - 1`,
so the *combined* sum is degree `≤ s - 1` plus `PY.charpoly` (which
is degree `s`). The `X^s` factor in
`rowFQuot_mul_X_pow_eq_RowF` only emerges after the constant-term
cancellation between the two summands, exactly as the strategy's
worked s=1 trapezoidal example shows.

A reasonable next-cycle deliverable: state and prove
```
toGLM_stabilityCharpolyRowF_split
    (m : LMM s) (hs : 0 < s) :
    toGLM_stabilityCharpolyRowF m
      = (∑ l : Fin s, αRow m l * X^l)
      + PY.charpoly * (∑ k : Fin s, βCoef m k * X^k)
```
as a one-liner combining cycle 676's two closed forms, then start
the constant-term analysis as a separate lemma in a future cycle.

A nice-to-have intermediate would be naming the scalar coefficients
`αRow m l := vecMul (-α) (-PY.adj * (-PYHF.map C)) l` and
`βCoef m k := Polynomial.C ((m.β (Fin.castSucc k) : ℝ) : ℂ)` to
shorten downstream statements.
