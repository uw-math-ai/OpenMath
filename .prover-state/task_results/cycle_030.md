# Cycle 030 Results

## Worked on

`def:381A` — *equivalent* Runge–Kutta methods, Butcher §380.

Three new declarations in `OpenMath/Chapter3/Section381.lean`:

* `RKTableau.IsRKOneStep M f y₀ h y₁` — predicate-form one-step output
  relation (handles implicit methods correctly: zero/one/many stage
  solutions all admissible).
* `RKTableau.Equivalent M M'` — Butcher def:381A, semantic same-output
  equivalence on Lipschitz autonomous problems for sufficiently small
  step.
* `equivalent_explicitEuler_self` — non-vacuity witness on explicit
  Euler.

## Approach

1. Read `extraction/formalization_data/entities/def_381A.json` to lock
   the textbook statement: "for any initial value problem defined by
   an autonomous function `f` satisfying a Lipschitz condition, and
   an initial value `y₀`, there exists `h₀ > 0` such that the result
   computed by the first method is identical with the result computed
   by the second method, if `h ≤ h₀`."

2. Translated this into a *predicate* encoding of the one-step
   relation (`IsRKOneStep`) rather than a function `oneStep : ... → N`,
   because implicit methods may admit multiple stage solutions and a
   function-style encoding would silently drop the ambiguity.

3. Defined `Equivalent M M'` quantifying over all Lipschitz `f`, all
   initial values `y₀`, and over *every pair* of method outputs at the
   given step.

4. For the witness, exploited that explicit Euler's stage system
   collapses to `Y 0 = y₀` (since `A = 0`), so any two stage tuples
   immediately agree and `y₁ = y₀ + h • f y₀` is the unique output.

5. Added `import Mathlib.Topology.MetricSpace.Lipschitz` and
   `open scoped NNReal` to the file for `LipschitzWith` and `ℝ≥0`.

6. Verified `lake env lean OpenMath/Chapter3/Section381.lean` clean,
   `lake build` clean, axioms = `[propext, Classical.choice, Quot.sound]`
   for all three new declarations.

7. Wrote `.prover-state/issues/equivalent_self_general_deferred.md`
   explaining why `equivalent_self M` for arbitrary `M` is deferred.

## Result

SUCCESS — all three declarations compile, full `lake build` is clean,
no sorries, no axioms beyond the standard trio. `def:381A` flipped to
`formalized` in `lean_status.json`; `plan.md` updated (30 → 31).

## Faithfulness check

### `RKTableau.IsRKOneStep`

- Entity ID: helper for `def:381A` (no separate JSON; Butcher's
  one-step formulae are §312/§313 background and the stage system
  `Yᵢ = y₀ + h Σⱼ aᵢⱼ f(Yⱼ)`, `y₁ = y₀ + h Σᵢ bᵢ f(Yᵢ)` is
  standard).
- Lean statement captures: same content (literal transcription of the
  autonomous one-step Runge–Kutta stage system into Lean syntax).
- Encoded as `Prop`, not function — honest about implicit-method
  multi-solution case.

### `RKTableau.Equivalent`

- Entity ID `def:381A` — textbook statement (quoted from
  `extraction/formalization_data/entities/def_381A.json`):

  > Two Runge–Kutta methods are 'equivalent' if, for any initial value
  > problem defined by an autonomous function `f` satisfying a
  > Lipschitz condition, and an initial value `y₀`, there exists
  > `h₀ > 0` such that the result computed by the first method is
  > identical with the result computed by the second method, if
  > `h ≤ h₀`.

- Lean statement captures: same content.
  - "autonomous `f`" → `f : N → N` (independent of time).
  - "satisfying a Lipschitz condition" → `LipschitzWith L f` for
    some `L : ℝ≥0` (Mathlib's standard global-Lipschitz predicate).
  - "initial value `y₀`" → `(y₀ : N)`.
  - "there exists `h₀ > 0` such that … if `h ≤ h₀`" →
    `∃ h₀ > 0, ∀ h, 0 < h → h ≤ h₀ → …`.
  - "the result … is identical with the result …" →
    `∀ y₁ y₁', M.IsRKOneStep f y₀ h y₁ → M'.IsRKOneStep f y₀ h y₁' → y₁ = y₁'`.
- The `∀ y₁ y₁'` quantifier handles the implicit-method case where the
  stage equations admit multiple solutions; we require *every* output
  pair to agree.
- Definition smuggling check passed: NOT defined as `PhiEquivalent`.
  These are two distinct definitions; `thm:381H` later establishes the
  equivalence (modulo the reduced method).
- Hypothesis strength check passed: did NOT strengthen "Lipschitz" to
  `Continuous` or `ContDiff`.

### `equivalent_explicitEuler_self`

- Tautology check passed: conclusion (`y₁ = y₁'`) does not appear as
  a hypothesis. Real work is done — the proof unfolds `IsRKOneStep`,
  uses the `A = 0` collapse to derive `Y 0 = y₀ = Y' 0`, then uses
  `simp [explicitEuler]` to close `y₀ + h • (1 • f y₀) = y₀ + h • (1 • f y₀)`.
- Identity check passed: proof is not `exact h` or a one-liner.
- Hypothesis strength check passed: no hypotheses besides the
  `Equivalent` quantifier list.

## Dead ends

None. The plan from the strategy worked first time. The witness proof
matched the strategy's pseudocode almost verbatim.

## Discovery

* Adding `open scoped NNReal` once at the namespace level (rather than
  per-declaration `open scoped NNReal in`) is enough — `ℝ≥0` notation
  becomes available throughout the namespace.
* The strategy's choice of putting `IsRKOneStep`/`Equivalent` in the
  `RKTableau` namespace (so `M.Equivalent M'` works via dot notation)
  is convenient; the witness proof reads naturally.
* Mathlib's `LipschitzWith` over an arbitrary `NormedAddCommGroup` /
  `NormedSpace ℝ N` works without typeclass-resolution hiccups when
  `N` is left implicit and brought in by Lean from `f : N → N`.

## Suggested next approach

Continue the §381 cluster:

1. **`def:381F` — P-equivalent Runge–Kutta methods** (next §381 leaf).
   Statement: two methods are P-equivalent if their P-reduced methods
   are Φ-equivalent. The reducibility infrastructure (`pReduced`,
   `IsPReducible`, `PhiEquivalent`) is already in place — this should
   be a clean ~one-cycle definition + a witness.

2. After §381 leaves are clear, the §381 cluster's *theorems*:
   `thm:381G` (irreducible methods distinguish stages) and
   `thm:381H` (equivalence-conditions theorem). `thm:381H` is the
   capstone tying `Equivalent`, `PhiEquivalent`, and `PEquivalent`
   together; it almost certainly needs the implicit-stage uniqueness
   infrastructure flagged in
   `equivalent_self_general_deferred.md`. Plan a dedicated
   contraction-infrastructure cycle when `thm:381H` is queued.

3. AN-stability for `def:356A` and the §382–§388 Runge–Kutta-group
   cluster remain as later targets.
