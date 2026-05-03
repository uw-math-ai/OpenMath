# Cycle 084 Results

## Worked on

- `def:510C` (stable GLM) — formalized as
  `OpenMath.Chapter5.Section510.GeneralLinearMethod.IsStable`.
- Non-vacuity witness `explicitEulerGLM_isStable` — `explicit Euler` GLM
  is stable with bound `C = 1`.

## Approach

Followed the cycle-084 strategy verbatim:

1. Added imports for `Mathlib.Analysis.Matrix.Normed` and
   `OpenMath.Chapter1.Section142` to `OpenMath/Chapter5/Section510.lean`.
2. Defined `IsStable` as the GLM instance of the existing
   `PowerBounded` predicate from `def:142A`:
   `∃ C : ℝ, PowerBounded C M.V`. Reusing the cross-chapter
   power-boundedness predicate avoids a parallel matrix-norm
   definition and keeps the GLM stability concept literally the
   matrix-stability concept restricted to `V`.
3. Activated the linfty operator-norm `SeminormedRing` instance via
   `open scoped Matrix.Norms.Operator` (matches the convention used in
   `Section142.lean`).
4. Proved `explicitEulerGLM_isStable` by witnessing `C = 1`. Since
   `explicitEulerGLM.V = (1 : Matrix (Fin 1) (Fin 1) ℝ)` (one-cell
   identity), `V^n = 1` for every `n`, and `‖1‖ = 1` closes the bound.
5. Used `lean_multi_attempt` to verify five candidate closers for the
   final `‖1‖ ≤ 1` step; chose `exact le_of_eq norm_one` per the
   strategy.
6. Updated `lean_status.json` (`def:510C` → formalized) and `plan.md`
   (row marked `[x]`, progress counter `54 → 55`).

## Result

SUCCESS.

- `lake env lean OpenMath/Chapter5/Section510.lean` — clean (no errors,
  no warnings).
- `lake build OpenMath.Chapter5.Section510` — clean (2771/2771 jobs, .olean cache refreshed).
- `#print axioms` for both new declarations — baseline only:
  `[propext, Classical.choice, Quot.sound]`. No new axioms introduced.

## Faithfulness check

### `def:510C` → `OpenMath.Chapter5.Section510.GeneralLinearMethod.IsStable`

- Entity ID and textbook statement (quoted from
  `extraction/formalization_data/entities/def_510C.json`):
  > A general linear method `(A, U, B, V)` is `stable' if there exists
  > a constant `C` such that, for all `n = 1, 2, ..., \|V^n\| \leq C`.
- Lean statement: `∃ C : ℝ, PowerBounded C M.V`, where
  `PowerBounded C V := ∀ k : ℕ, ‖V^k‖ ≤ C`.
- Captures: same content (modulo a `n = 0` extension of the
  quantifier; `‖V^0‖ = ‖1‖` is constant, so any bound for `n ≥ 1`
  trivially extends, and the full-`ℕ` quantifier is necessary for
  direct reuse of the `def:142A` predicate). Documented in the
  docstring.
- No definition smuggling: `IsStable` is the literal
  power-boundedness condition. We do **not** define stability via
  spectral radius `< 1`, eigenvalue conditions on the closed unit
  disc, minimal-polynomial roots, or any other characterization.
  Those characterizations remain genuine theorems.
- Tautology check: not applicable (definition).

### `theorem explicitEulerGLM_isStable`

- Tautology check: conclusion `explicitEulerGLM.IsStable` is not a
  hypothesis (the theorem is hypothesis-free).
- Identity check: proof constructs the witness `C = 1` and discharges
  a real norm bound — not `exact h` or `:= id`.
- Hypothesis strength check: no hypotheses, so vacuously satisfied.

## Dead ends

None — the strategy executed without dead ends.

## Discovery

- `open scoped Matrix.Norms.Operator` is the necessary scoped open in
  any file that wants the linfty `SeminormedRing` instance on
  `Matrix (Fin r) (Fin r) ℝ`. The explicit `import
  Mathlib.Analysis.Matrix.Normed` alone is not enough — without the
  scoped open, type-class synthesis for `SeminormedRing (Matrix _ _ ℝ)`
  fails when reusing `PowerBounded`. (This was already used in
  `Section142.lean`; reproduced here for cross-chapter consistency.)
- The 1×1 identity matrix has `‖1‖ = 1` directly via `norm_one`; no
  unfolding of `Matrix.linftyOpNorm_def` was needed. `simp`,
  `norm_num`, and `exact norm_one.le` would all also have closed it
  per the `lean_multi_attempt` probe.
- The simp linter flagged `Matrix.one_apply` as an unused argument in
  the `explicitEulerGLM.V = 1` proof — `!![1] = 1` is closed by `simp`
  using only `explicitEulerGLM`'s definition, with no need for
  `Matrix.one_apply`. Cleaned up.

## Suggested next approach

Per the cycle-084 strategy's roadmap section, the natural cycle 085
target is **`def:510B` (consistent GLM)**. It depends on `def:510A`
(now formalized) and `def:510C` (this cycle), and the textbook
statement is:

> A general linear method `(A, U, B, V)` with preconsistency vector
> `u` is `consistent' if there exists a vector `v` such that
> `B 𝟙 + V v = u + v`.

Suggested Lean encoding:

```lean
def GeneralLinearMethod.IsConsistent {s r : ℕ}
    (M : GeneralLinearMethod s r) (u : Fin r → ℝ)
    (hu : M.V *ᵥ u = u ∧ M.U *ᵥ u = (fun _ => 1)) : Prop :=
  ∃ v : Fin r → ℝ,
    M.B *ᵥ (fun _ => 1) + M.V *ᵥ v = u + v
```

(The exact handling of "with preconsistency vector `u`" — whether `u`
is a parameter, an existence on `IsPreconsistent`, or a packaged
sigma — is a design choice for the planner. The textbook treats `u`
as fixed once the method is preconsistent, which suggests packaging
preconsistency + consistency together rather than making `u` a free
parameter.)

The 1×1 explicitEuler witness extends naturally with `v = 0`:
`B 𝟙 + V·0 = !![1]·1 + 0 = 1 = u + 0`.

Subsequent cycles (086+) should pick up `def:512A` (convergent GLM)
and the §520 cluster as planned.
