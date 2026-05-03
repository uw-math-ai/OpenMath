# Cycle 086 Results

## Worked on

- Opened §520 of Butcher Chapter 5: created
  `OpenMath/Chapter5/Section520.lean`.
- Formalized **`def:520A`** — the *stability matrix* `M(z)` of a
  general linear method, plus the supporting helper `complexify`
  (entrywise lift of a real matrix to ℂ).
- Wrote two non-vacuity witnesses:
  - `GeneralLinearMethod.stabilityMatrix_at_zero`: every GLM has
    `M(0) = V` (after entrywise complexification).
  - `explicitEulerGLM_stabilityMatrix`: for the canonical
    `(s, r) = (1, 1)` explicit-Euler GLM, `M(z) = !![1 + z]`.

## Approach

Followed the cycle-086 strategy verbatim:

1. Checked Mathlib for an existing `Matrix _ _ ℝ → Matrix _ _ ℂ`
   idiom. Found `RingHom.mapMatrix` (square matrices only — needs
   `Fintype m`, `DecidableEq m` and is `Matrix m m α`). Since
   GLM's `B : Matrix (Fin r) (Fin s) ℝ` and
   `U : Matrix (Fin s) (Fin r) ℝ` are non-square in general,
   `RingHom.mapMatrix` doesn't fit. Defined `complexify` directly
   as `A.map (Complex.ofReal ·)`.
2. Wrote the stability-matrix definition as
   ```
   complexify M.V +
     z • complexify M.B *
       (1 - z • complexify M.A)⁻¹ *
       complexify M.U
   ```
   marked `noncomputable` (because `Matrix.inv` is noncomputable).
3. Compiled, hit a namespace error: dot notation
   `M.stabilityMatrix` looks up
   `OpenMath.Chapter5.Section510.GeneralLinearMethod.stabilityMatrix`.
   Resolved by closing the `Section520` namespace after
   `complexify` and reopening `Section510` for the
   `stabilityMatrix` definition + theorems (with
   `open OpenMath.Chapter5.Section520 (complexify)` inside).
4. `stabilityMatrix_at_zero` closed by `unfold; simp` directly.
5. `explicitEulerGLM_stabilityMatrix` closed in three steps:
   (a) prove `(1 - z • complexify A) = 1` since `A = !![0]`
   (b) `rw [hA, inv_one]` to reduce the resolvent
   (c) entrywise `ext; fin_cases; simp [..., Matrix.mul_apply]`.

No Aristotle submission was needed: all three theorems closed on
the first manual attempt. (Strategy noted Aristotle was a fallback
"in case the matrix-inverse arithmetic is fiddly" — it wasn't.)

## Result

**SUCCESS.** All three new declarations compile cleanly with zero
warnings:

- `OpenMath.Chapter5.Section520.complexify` — definition (data).
- `OpenMath.Chapter5.Section510.GeneralLinearMethod.stabilityMatrix`
  — definition (per strategy convention, lives in `Section510`
  namespace so dot notation `M.stabilityMatrix z` works).
- `OpenMath.Chapter5.Section510.GeneralLinearMethod.stabilityMatrix_at_zero`
  — theorem.
- `OpenMath.Chapter5.Section510.explicitEulerGLM_stabilityMatrix`
  — theorem.

`lean_verify` on each of the three theorem-level declarations
returned axioms `[propext, Classical.choice, Quot.sound]` only. No
`sorryAx`, no new axioms.

`OpenMath/Chapter5.lean` updated to `import OpenMath.Chapter5.Section520`.

`extraction/formalization_data/lean_status.json`: `def:520A` marked
`formalized` with `lean_file = "OpenMath/Chapter5/Section520.lean"`
and `lean_symbol = "OpenMath.Chapter5.Section510.GeneralLinearMethod.stabilityMatrix"`.

`plan.md` Chapter 5 row updated; progress count `56 / 175 → 57 / 175`.

## Faithfulness check

### `Section520.complexify`
- *No textbook entity* — internal helper. Documented as such in its
  docstring. Type `Matrix m n ℝ → Matrix m n ℂ` exactly captures
  "lift the real GLM coefficient matrices to complex", which is the
  textbook's implicit operation when writing
  `(I − zA)⁻¹` with `z ∈ ℂ` and `A` a real matrix.

### `Section510.GeneralLinearMethod.stabilityMatrix`
- Entity ID `def:520A`, textbook statement (quoted from
  `entities/def_520A.json`):
  > "For a general linear method `(A, U, B, V)`, the 'stability
  > matrix' `M(z)` is defined by
  > `M(z) = V + zB(I − zA)⁻¹U`."
- Lean statement captures: **same content**, modulo Mathlib's
  junk-value convention for `Matrix.inv`.
  - Encoding: `complexify M.V + z • complexify M.B *
    (1 - z • complexify M.A)⁻¹ * complexify M.U`.
  - The `(I − z·A)⁻¹` factor uses Mathlib's `Matrix.inv`. On the
    invertible domain (the textbook's implicit domain of
    definition) this agrees with the genuine resolvent. Outside
    that domain Mathlib returns `0`. Documented in the docstring.
- Definition smuggling check: definition matches the textbook
  formula literally; not "the algebraic conditions characterizing
  the stability matrix". ✓
- Hypothesis strength check: hypothesis-free (it's a definition).
- Index-shape sanity (per Section510 conventions
  `A : s×s`, `U : s×r`, `B : r×s`, `V : r×r`):
  `(1 - z·A) : s×s`, resolvent `s×s`, `B · resolvent · U : r×r`,
  result `r×r`. ✓

### `Section510.GeneralLinearMethod.stabilityMatrix_at_zero`
- Tautology check: conclusion `M.stabilityMatrix 0 = complexify M.V`
  is not a hypothesis. ✓
- Identity check: proof is `unfold; simp`, doing real reduction
  work (kills the `0 • _` and `_ + 0` factors). ✓
- Hypothesis strength: hypothesis-free. ✓

### `Section510.explicitEulerGLM_stabilityMatrix`
- Tautology / identity / hypothesis-strength: clean (concrete
  computation on a fixed instance, hypothesis-free).
- This is the load-bearing non-vacuity witness — confirms the
  stability matrix is computable on a concrete GLM and gives the
  textbook-expected answer `M(z) = 1 + z` for explicit Euler
  (Butcher §520 example, p. 418 onwards). ✓

## Dead ends

- Initial namespace mistake: defining `GeneralLinearMethod.stabilityMatrix`
  inside `namespace OpenMath.Chapter5.Section520` produced
  `OpenMath.Chapter5.Section520.GeneralLinearMethod.stabilityMatrix`,
  which broke dot notation `M.stabilityMatrix` for values of type
  `Section510.GeneralLinearMethod`. Fixed by closing the `Section520`
  namespace after `complexify` and reopening `Section510` for the
  rest of the file. (Recorded for future cycles: when adding methods
  to a structure defined in another namespace, define them in the
  *structure's* namespace — the file's own namespace is a footgun.)

## Discovery

- `Matrix.inv` of `(1 : Matrix (Fin n) (Fin n) ℂ)` reduces via the
  generic ring `inv_one` lemma (works because `Matrix (Fin n) (Fin n) ℂ`
  is a non-commutative ring). No need for a matrix-specific
  `Matrix.inv_one` lemma. Saved the planner's fallback search.
- For the `1×1` resolvent reduction, the cleanest pattern is:
  1. Prove the algebraic equality `(1 - z • complexify A) = 1` by
     `ext; fin_cases; simp [explicitEulerGLM, complexify]`.
  2. Rewrite using that fact and `inv_one`.
  3. Finish entrywise with `Matrix.mul_apply` in the simp set.
  This decomposition was suggested by the strategy and worked
  first try. `Fin.sum_univ_succ` is *not* needed in the simp set
  (linter flagged it as unused) — `Matrix.mul_apply` plus the
  `Matrix.cons` simp lemmas handle the `Fin 1` sum directly.
- The `complexify_apply @[simp]` lemma helps `simp` unfold the
  entrywise lift without needing to mention `complexify` explicitly
  every time, but in practice we still added `complexify` to the
  simp set in the explicit-Euler proof to ensure the `!![0]` /
  `!![1]` constants reduce. Kept the `@[simp]` for downstream use.

## Suggested next approach

Per strategy: cycle 087's natural target is **`def:520C`**, the
stability function `Φ(w, z) = det(wI − M(z))`, plus the
*stability region* and *instability region* (Butcher §520).
`def:520C` depends on `def:520A` (just landed) and reuses the same
complex matrix machinery + `Matrix.det`. Estimated 1 cycle.

Bonus follow-up: with `stabilityMatrix` in hand, the long-deferred
`AN_stability_deferred.md` issue (a scalar specialization of the
same resolvent pattern) is now much closer. After `def:520C` lands,
returning to AN-stability is recommended.
