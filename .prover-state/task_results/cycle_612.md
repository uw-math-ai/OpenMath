# Cycle 612 Results

## Worked on

Butcher §510 — partial opening. Added preconsistency and stability
predicates to `OpenMath/GeneralLinearMethod.lean`, with RK-embedding
sanity checks in `OpenMath/RKAsGLM.lean`. Updated `plan.md` to reflect
the partial close.

## Approach

Followed the strategy spec verbatim:

1. Added `IsPreconsistent` to `GeneralLinearMethod.lean`:
   ```
   ∃ q, (∀ k, ∑ l, V k l * q l = q k) ∧ (∀ i, ∑ k, U i k * q k = 1)
   ```
   Plain `∑ … = …` form (not `Matrix.mulVec`) to keep the unfolding
   light, matching the existing `step` / `stageMap` convention.

2. Added `IsStable` using the iterate-`Function.iterate` form:
   ```
   ∃ M, 0 ≤ M ∧ ∀ n q, (∀ k, |q k| ≤ 1) →
     ∀ k, |((fun v k' => ∑ l, V k' l * v l)^[n] q) k| ≤ M
   ```
   Iterating an explicit lambda in `Fin r → ℝ` keeps everything in the
   elementary explicit-sum world.

3. RK sanity checks in `RKAsGLM.lean`:
   - `toGLM_isPreconsistent`: witness `q := fun _ => 1`, both sides
     close under `simp [toGLM_V]` / `simp [toGLM_U]` (the `Fin 1` sum
     collapses to one term, `1 * 1 = 1`).
   - `toGLM_isStable`: bound `M := 1`. Induction on `n`. Base case
     `Function.iterate_zero` returns `q`, hypothesis `|q k| ≤ 1` closes
     it. Successor: `Function.iterate_succ_apply'` rewrites
     `f^[n+1] q` to `f (f^[n] q)`, then
     `simp only [toGLM_V, one_mul, Fin.sum_univ_one] at ih ⊢` collapses
     the `Fin 1` sum to `(f^[n] q) 0`, and `ih 0` closes.

4. Updated `plan.md`:
   - Marked §510 as `[~]` with the predicates and RK sanity checks
     listed.
   - Added a cycle 612 frontier note alongside the 609 / 610 / 611
     notes in "Active Frontier".
   - Annotated backlog item #1 as "partial — full consistency +
     convergence chain still pending".

## Result

SUCCESS — all four deliverables landed sorry-free.

- `lake env lean OpenMath/GeneralLinearMethod.lean` — clean.
- `lake env lean OpenMath/RKAsGLM.lean` — clean.
- `lake build OpenMath.RKAsGLM` — clean.
- No new sorrys anywhere.

## Dead ends

The first attempt at `toGLM_isStable` used
`simp only [toGLM_V, one_mul, Fin.sum_univ_one]` only on the goal,
not on `ih`. After `Function.iterate_succ_apply'`, simp normalised
the inner `(fun v k' => ∑ l, t.toGLM.V k' l * v l)` to `(fun v k' => v 0)`
on **both** sides of the iterate, leaving `ih` in the un-normalised
form. Adding `at ih ⊢` to the `simp only` line fixed the mismatch.

Otherwise no real dead ends — the deliverables were small and the
strategy spec correctly predicted that `simp` + `induction` would
close everything.

## Discovery

`Function.iterate_succ_apply'` (with the prime — outer-application
form `f (f^[n] x)`) plays well with `simp` collapsing a constant-1
matrix on `Fin 1`, since the simplified outer lambda still composes
with the simplified inner iterate. When using this pattern, remember
to `simp` `at ih ⊢` together so the iterate-of-lambda matches on
both sides.

## Suggested next approach

Per the strategy, with §510 partially open the natural next step is
**backlog item #2 — Butcher §515 (GLM Dahlquist equivalence)**:
`stability + consistency ⟹ convergence` for GLMs. The companion-matrix
spectral bound used in `OpenMath/SpectralBound.lean` for the LMM case
will need re-derivation for general `V`, but the structural template
from `OpenMath/DahlquistEquivalence.lean` should carry over directly
once we pin down what "GLM consistency" means past preconsistency.

A reasonable intermediate is to add a `IsConsistent` predicate that
strengthens `IsPreconsistent` with the `B q + V q = q + 𝟙` (or the
appropriate stage-evaluation analogue) condition. Currently
`IsConsistent` is still the placeholder `True`; tightening it is a
prerequisite for any honest §515 statement.
