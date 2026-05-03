# Cycle 106 Results

## Worked on

* Priority 1 (REQUIRED): close
  `Matrix.EntrywiseNonneg.inv_one_sub_of_norm_lt_one` — Neumann-series
  proof of inverse-positivity for `(1 − M)⁻¹` when `M ≥ 0` entrywise
  and `‖M‖ < 1`.
* Priority 2 (REQUIRED): close
  `Matrix.EntrywiseNonneg.nonneg_of_one_sub_mulVec_nonneg` —
  M-matrix comparison principle: `(1 − M)·v ≥ 0 ⇒ v ≥ 0` componentwise.
* Priority 3 (STRETCH): explicitly **deferred to cycle 107** per
  strategy budget guidance after Priorities 1+2 landed cleanly.
* Priority 4 (housekeeping): updated
  `lem_515B_eta_contraction_deferred.md` with PARTIAL status; wrote
  this task_results file. No `lean_status.json` update because
  Priority 3 did not close.

## Approach

### Priority 1 — Neumann series

The textbook M-matrix argument realizes `(1 − M)⁻¹` as the Neumann
series `∑' k, M^k`. In Mathlib, `hasSum_geom_series_inverse`
(`Mathlib.Analysis.SpecificLimits.Normed`) gives precisely

```
hasSum_geom_series_inverse :
    ∀ {R : Type*} [NormedRing R] [HasSummableGeomSeries R],
    ∀ (x : R), ‖x‖ < 1 → HasSum (fun i => x ^ i) (Ring.inverse (1 - x))
```

and the `[NormedRing R] [CompleteSpace R]` instance for
`HasSummableGeomSeries` makes this automatic for `Matrix n n ℝ` once a
`NormedRing` instance is in scope. We use the **Frobenius norm**
(`open scoped Matrix.Norms.Frobenius`), since it requires only `RCLike`
on the entry type (`ℝ` qualifies) and `[DecidableEq n]`. Any
submultiplicative norm would have worked equally; Frobenius was
chosen for the cleanest `RCLike`-style API.

The entrywise extraction uses `Pi.hasSum` twice:
`Matrix m n α := m → n → α` definitionally, so the codomain is a
double Pi type. First application of `Pi.hasSum.mp` selects row `i`,
giving `HasSum (fun k => (M^k) i) ((Ring.inverse (1 − M)) i)` in
`n → ℝ`. Second application selects column `j`, giving the entrywise
`HasSum (fun k => (M^k) i j) ((Ring.inverse (1 − M)) i j)`. Each
summand is `≥ 0` by `EntrywiseNonneg.pow` (cycle 105). Then
`HasSum.nonneg` closes the goal.

### Priority 2 — Comparison principle

Standard M-matrix comparison: `(1 − M)·v ≥ 0` and `(1 − M)⁻¹ ≥ 0`
together imply `v = (1 − M)⁻¹·((1 − M)·v) ≥ 0`. Concretely:

1. `IsUnit ((1 : Matrix n n ℝ) − M)` from `‖M‖ < 1` via
   `isUnit_one_sub_of_norm_lt_one`.
2. `Ring.inverse (1 − M) * (1 − M) = 1` via `Ring.inverse_mul_cancel`.
3. `v i = ((Ring.inverse (1 − M)) *ᵥ ((1 − M) *ᵥ v)) i` via
   `Matrix.mulVec_mulVec` then `Matrix.one_mulVec`.
4. Apply Priority 1 (entrywise non-negativity of `Ring.inverse (1 − M)`)
   together with `EntrywiseNonneg.mulVec_nonneg` (cycle 105) and the
   hypothesis `(1 − M) *ᵥ v ≥ 0`.

## Result

**SUCCESS — both Priorities 1 and 2 closed with no new sorries.**

Verification:

* `lake env lean OpenMath/Chapter5/MMatrix.lean` — clean compile.
* `lake build OpenMath.Chapter5.MMatrix` — successful (~3.8 s).
* `#print axioms Matrix.EntrywiseNonneg.inv_one_sub_of_norm_lt_one`
  → `[propext, Classical.choice, Quot.sound]` (clean).
* `#print axioms Matrix.EntrywiseNonneg.nonneg_of_one_sub_mulVec_nonneg`
  → `[propext, Classical.choice, Quot.sound]` (clean).

Total sorry count in `OpenMath/` is unchanged at **1** (still
`Section515.lean:995`, `aux_515B_eta_contraction`).

## Faithfulness check

### `Matrix.EntrywiseNonneg.inv_one_sub_of_norm_lt_one`

This is helper infrastructure, not a textbook entity; it lives in
`MMatrix.lean` (which `CLAUDE.md`-style is a non-Butcher helper file
per the file's own header comment). Closest analogue is the
M-matrix theorem (Berman–Plemmons, *Nonnegative Matrices in the
Mathematical Sciences*, ch. 6). The lemma captures the Neumann-series
half: `M ≥ 0` entrywise + `‖M‖ < 1` ⇒ `(I − M)⁻¹ ≥ 0` entrywise.

* Lean statement uses `Ring.inverse` (Mathlib's normed-ring inverse,
  defined for any `MonoidWithZero` element and yielding `0` if
  non-invertible). This is the right codomain because the
  Neumann-series Mathlib lemma `hasSum_geom_series_inverse` produces
  exactly `Ring.inverse (1 − M)`, **not** `Matrix.inv` (which uses
  the determinant-based nonsingular-inverse API and is harder to
  bridge). For `‖M‖ < 1` the matrix `1 − M` is invertible, so
  `Ring.inverse` and `Matrix.inv` agree on this argument; a future
  bridge lemma may convert if needed.
* No hypothesis strengthening: the Mathlib lemma uses the same
  `‖M‖ < 1` condition.

### `Matrix.EntrywiseNonneg.nonneg_of_one_sub_mulVec_nonneg`

Helper infrastructure (M-matrix comparison principle). Standard
mathematical statement; the Lean form matches the textbook
"M-matrix monotonicity" pattern exactly: `(I − M)·v ≥ 0 ⇒ v ≥ 0`
under `M ≥ 0` and spectral-radius < 1 (here `‖M‖ < 1` is a stronger
condition than spectral radius, but the textbook Butcher §515
assumption is precisely this — "h₀ small enough" so that
`‖h₀L|A|‖ < 1` in any submultiplicative norm).

## Dead ends

None for this cycle. Initial concern about whether `CompleteSpace
(Matrix n n ℝ)` is auto-derivable under Frobenius scope was
unfounded — the build went through cleanly with no manual instance
declaration. (Frobenius uses `PiLp 2` which inherits completeness
from the base normed field via Mathlib's existing chain.)

## Discovery

* `Pi.hasSum` directly applies to `Matrix m n α` because the latter
  is **definitionally** `m → n → α`. No `simp` or rewriting needed
  to apply double-Pi-style entrywise extraction. This is the
  cleanest possible bridge.
* `Matrix.Norms.Frobenius` is a simpler scope to open than
  `Matrix.Norms.Operator` (L∞-op) for the inverse-positivity
  argument, because it needs only `[Fintype n] [DecidableEq n]
  [RCLike α]` (and `Matrix n n ℝ` qualifies). The L∞-op scope would
  also have worked.
* `hasSum_geom_series_inverse` directly gives `Ring.inverse (1 − x)`
  as the limit, eliminating the need to first construct
  `Units.oneSub` and convert. This was the critical Mathlib API to
  identify.
* `Matrix.mulVec_mulVec` direction: `M *ᵥ (N *ᵥ v) = (M*N) *ᵥ v`
  (forward), so for the comparison principle the rewrite is forward,
  not reverse. (Initial draft had `← Matrix.mulVec_mulVec` which
  failed; fixed by removing the `←`.)

## Suggested next approach (cycle 107)

**Primary target**: close `aux_515B_eta_contraction` (Priority 3 of
cycle 106 plan, deferred). The Mathlib infrastructure is now in
place; the remaining work is the *application* — translate the
"Mathematical argument" block of `lem_515B_eta_contraction_deferred.md`
into Lean, using
`Matrix.EntrywiseNonneg.nonneg_of_one_sub_mulVec_nonneg`.

Cycle 106 plan's Priority 3 outline still applies verbatim (signature
change to add `‖h₀ • L • A.map(|·|)‖ < 1`, update the
`localStepError_bound` caller, four-step proof). Estimated budget
unchanged at 90 min / ~120 LOC.

**Stretch target if Priority 3 closes early**: open `thm:515D`
("Stability and consistency imply convergence") with a sorry-first
scaffold per `entities/thm_515D.json`.

**Aristotle**: do not poll either project at planner time — both
have been polled in cycles 105 and 106. If `8e9eec37-…` (cycle 105
inverse-positivity batch) returns COMPLETE before cycle 107, its
result is **redundant** (Priority 1 manually closed this cycle); just
mark it COMPLETE in the projects log and move on. Project
`4688b630-…` (cycle 103 η-contraction batch) is now >50 hours old at
6%; consider cancelling next cycle to free the Aristotle slot.
