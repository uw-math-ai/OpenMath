# Cycle 131 Results

## Worked on
`def:551A` *Inherent Runge–Kutta stability* — primary deliverable per the
cycle 131 strategy. New predicate
`OpenMath.Chapter5.Section510.GeneralLinearMethod.IsIRKStable` plus
non-vacuity witness `explicitEulerGLM_isIRKStable`, both placed in
`OpenMath/Chapter5/Section520.lean` directly after the cycle-130
`explicitEulerGLM_isRKStable` block.

## Approach
Followed the strategy almost verbatim:

1. Encoded only the two textbook-stated conditions:
   - (551a): `V`'s first column is `e₀` — i.e. `V[0][0] = 1` and
     `V[i][0] = 0` for `i ≠ 0`.
   - `∃ X : Matrix (Fin r) (Fin r) ℝ` such that `B·A − X·B` and
     `B·U − X·V + V·X` are zero outside row 0.
2. Picked `X := 0` for the explicit-Euler witness (s = r = 1 makes
   the row-0 clauses vacuously hold for any `X`).
3. Closed the V-form clause with `fin_cases i; simp [explicitEulerGLM]`
   and the row-0 clauses with `Subsingleton.elim i 0` rerouting the
   nonzero hypothesis into a contradiction.

The single deviation from the strategy text was adding `[NeZero r]` to
the predicate signature: without it Lean cannot synthesize
`OfNat (Fin r) 0` so the literal `0` index doesn't elaborate. The
`[NeZero r]` constraint captures the textbook's implicit `r = p + 1 ≥ 1`
context-block assumption, which is faithful: the equation (551a) block
form `V = [[1, v]; [0, V̇]]` requires `r ≥ 1` to even make sense. Trade
removes the strategy's "r = 0 → vacuously true" edge case but does not
weaken the predicate on any non-degenerate GLM.

## Result
SUCCESS. New code:

* `GeneralLinearMethod.IsIRKStable` predicate (axiom-clean: `[propext,
  Classical.choice, Quot.sound]`).
* `explicitEulerGLM_isIRKStable` witness theorem (axiom-clean).

Verified via `lake build OpenMath.Chapter5.Section520` (3.9s, 2772/2772
cached) and `lean_verify` on both names.

`plan.md` and `extraction/formalization_data/lean_status.json` updated;
progress is now 68 / 175.

## Faithfulness check

### `def:551A` — `GeneralLinearMethod.IsIRKStable`

Entity ID and textbook statement (quoted from
`extraction/formalization_data/entities/def_551A.json`):

> A general linear method (A, U, B, V) is 'inherently Runge–Kutta
> stable' if V is of the form (551a) and the two matrices
>
>     BA − XB         and         BU − XV + VX
>
> are zero except for their first rows, where X is some matrix.

Equation (551a): `V = [[1, v], [0, V̇]]`.

Lean statement captures: **same content** — modulo the `[NeZero r]`
class argument. The encoding maps:

* "V is of the form (551a)" → first-column-is-`e₀` form
  `(∀ i, V i 0 = if i = 0 then 1 else 0)`. The `v` row-vector and the
  `V̇` block remain unconstrained, exactly as the textbook intends.
* "BA − XB and BU − XV + VX are zero except for their first rows" →
  `∃ X, (∀ i ≠ 0, ∀ j, (B*A − X*B) i j = 0) ∧
        (∀ i ≠ 0, ∀ j, (B*U − X*V + V*X) i j = 0)`.

Method-class side-conditions from the textbook `Context` block —
`p = q`, `s = r = p + 1`, `A` diagonally implicit, `λ ≥ 0` on the
`A`-diagonal, `ρ(V̇) = 0` — are deliberately NOT smuggled into the
predicate. They describe which methods the textbook studies under the
IRK-stability heading, not which methods qualify as IRK-stable.
Compare cycle 130's `def:542A` analogous treatment.

**Definition smuggling check**: predicate is non-trivial on `r ≥ 2`
GLMs — the row-0 clauses are not vacuous when there exist `i ≠ 0` in
`Fin r`. The `r = 1` case is intentionally vacuous on the row-0
clauses (only `i = 0` exists), which is the standard 1×1 trivial-RK
limit and matches the textbook's expectation that 1-stage RK methods
are trivially IRK-stable.

### `explicitEulerGLM_isIRKStable`

Theorem statement: `explicitEulerGLM.IsIRKStable`. No hypotheses.

* **Tautology check**: the conclusion `explicitEulerGLM.IsIRKStable`
  is not a hypothesis — there are no hypotheses. ✓
* **Identity check**: proof is not `exact h` / `:= h_*` / `:= id`. The
  proof actively constructs `X = 0` and discharges the V-form clause
  via `fin_cases i; simp`. ✓
* **Hypothesis strength check**: no hypotheses to strengthen. ✓
* **Absent theorem check**: no `sorry`-promised content. ✓

## Dead ends
None this cycle — landing went per the strategy's first path. One
small mid-course correction: the strategy's predicate signature
omitted `[NeZero r]`, which produced an `OfNat (Fin r) 0` synthesis
failure. Adding `[NeZero r]` resolved it without affecting the
non-vacuity witness (`r = 1`, so `NeZero 1` is automatic).

## Discovery
* `[NeZero r]` is the right typeclass to require when a predicate
  needs to literally write `0 : Fin r` (rather than e.g.
  `Fin.mk 0 _` with a manual proof). Lean's `OfNat (Fin r) 0`
  instance is gated on `[NeZero r]`. This will recur for any future
  §55 / §551 infrastructure that distinguishes "row 0" from other
  rows.
* `Subsingleton.elim i 0 : i = 0` does typecheck on `Fin 1` and is a
  clean closer for "vacuously true on `Fin 1`" goals — preferable to
  `fin_cases i; exact absurd rfl hi` because it avoids the case
  split.

## Suggested next approach
Per the strategy's "Suggested next approach" section, candidates
ranked by directness:

1. **Substantive `implicitMidpointGLM_isIRKStable`** strengthening
   (parallel to cycle 130's substantive RK-stability witness).
   Requires actually computing `B·A − X·B` and `B·U − X·V + V·X` for
   the 1×1 implicit-midpoint tableau (`A = !![1/2]`, `U = B = V = !![1]`).
   With `X := 0`, `B·A = !![1/2]` (s = 1, so the row-0 clause is
   non-vacuous: we'd need `(B·A − 0) 0 j = 0` which fails). Need a
   non-trivial `X` — `X := !![1/2]` makes `B·A − X·B = !![1/2 − 1/2] =
   !![0]` ✓; then `B·U − X·V + V·X = !![1] − !![1/2] + !![1/2] = !![1]`
   which is *not* zero (and only has row 0, so the constraint is
   vacuous on `i ≠ 0`). So `implicitMidpointGLM_isIRKStable` actually
   holds with `X := 1/2`. ~25 LOC; a clean follow-up if the planner
   wants to strengthen the witness without bumping entity count.

2. **`def:530A` non-degenerate** — §53 leaf, definition-shape work
   in the same vein as this cycle.

3. **`thm:535A` underlying one-step method (GLM)** — theorem-level
   work in §535, dependencies all formalized.

4. **`thm:541A` DIMSIM types** — classification theorem; may need
   a lookup of the §541 DIMSIM definitions to verify dependencies.

The substantive `implicitMidpointGLM_isIRKStable` path looks cheapest
and most informative for `def:551A`'s downstream use; `def:530A` is
a clean parallel definition cycle.
