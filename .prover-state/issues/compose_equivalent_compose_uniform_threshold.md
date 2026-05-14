# Issue: `compose_equivalent_compose` blocked on `Equivalent`'s non-uniform threshold

## Cycle 216 update — CLOSED

The Option A refactor landed cleanly in cycle 216:

* `Equivalent` definition (cycle 206) tightened from
  `∀ y₀, ∃ h₀, ...` to `∃ h₀, ∀ y₀, ...` (one-line binder
  reorder).
* All downstream consumers ported by mechanical binder reorder
  (no threshold changes — every concrete instance already had a
  y₀-uniform threshold, as predicted): `equivalent_self`,
  `equivalent_explicitEuler_self`, `Equivalent.symm`,
  `Equivalent.trans`, `pReduced_equivalent`,
  `zeroReduced_equivalent`. The `setoid` / `setoidSigma` /
  `PReducesTo.toEquivalent` / `PEquivalent.toEquivalent` and the
  paddedEuler witnesses needed no body change.
* `compose_equivalent_compose` sorry-scaffold replaced (~20 LOC
  body) with the route B.1 recipe: factor the composite step via
  cycle 214's `compose_isRKOneStep_iff`; apply `hEq₁` at `y₀` to
  force `y_mid = y_mid'`; rewrite the M₂ step on the LHS to fire
  from `y_mid'`; apply `hEq₂` at `y_mid'` (newly admissible
  because `y₀` is now universally quantified *inside* the
  existential) to force `y_final = y_final'`.
* All five target theorems axiom-clean
  (`[propext, Classical.choice, Quot.sound]`).
* Sorry count: 1 → 0.

Original gap analysis preserved below for historical reference.

## Blocker

Cycle 215's target theorem `RKTableau.compose_equivalent_compose`
(the (382g) form of `thm:382A`, Butcher §382 p. 285) cannot be
proved with the cycle 215 strategy's recipe because the current
`Equivalent` definition has a non-uniform smallness threshold:

```lean
def Equivalent {s s' : ℕ} (M : RKTableau s) (M' : RKTableau s') : Prop :=
  ∀ {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [CompleteSpace N]
    (f : N → N) (L : ℝ≥0) (_hL : LipschitzWith L f) (y₀ : N),
    ∃ h₀ > (0 : ℝ), ∀ h, 0 < h → h ≤ h₀ →
      ∀ y₁ y₁', M.IsRKOneStep f y₀ h y₁ → M'.IsRKOneStep f y₀ h y₁' →
        y₁ = y₁'
```

The quantifier order is `∀ y₀, ∃ h₀, ∀ h ≤ h₀, ...`. The cycle 215
strategy's recipe assumed `∃ h₀, ∀ y₀, ∀ h ≤ h₀, ...` (uniform in
`y₀`), which would let the compose proof pick a single threshold
ahead of `H`. With the non-uniform definition, the proof structure
fails as follows.

## Context (the Lean compiler error)

The strategy's recipe (route B.1, ~20 LOC) destructures `hEq₂` at
the outer `y₀`:

```lean
obtain ⟨H₂, hH₂_pos, hEq₂_app⟩ := hEq₂ f L hL y₀
```

producing `hEq₂_app : ∀ h, 0 < h → h ≤ H₂ → ∀ y₁ y₁',
M₂.IsRKOneStep f y₀ h y₁ → M₂'.IsRKOneStep f y₀ h y₁' → y₁ = y₁'`.

Later in the proof, the M₂ step in the composite factorization (via
cycle 214's `compose_isRKOneStep_iff.mp`) fires from `y_mid'`, not
`y₀`. So the final `exact hEq₂_app H hH_pos hH_le_H₂ y_final
y_final' h_M₂_step h_M₂'_step` fails with:

```
error: Application type mismatch: The argument
  h_M₂_step
has type
  M₂.IsRKOneStep f y_mid' H y_final
but is expected to have type
  M₂.IsRKOneStep f y₀ H y_final
```

This is the *first* of two structural mismatches. Even renaming /
re-destructuring `hEq₂` at `y_mid'` produces a threshold
`H₂(y_mid')` that depends on `y_mid'`, which itself depends on the
universally-quantified `H` — a circular dependency that cannot be
resolved within the abstract `Equivalent` definition.

## What was tried

1. **Strategy's recipe verbatim (route B.1)**: type error on the
   final `exact` (M₂ step fires from `y_mid'`, not `y₀`).

2. **Destructure `hEq₂` at `y_mid'` instead of `y₀`** (inside the
   inner `∀ H`): produces `H₂(y_mid')` but we'd need `H ≤
   H₂(y_mid')`, and the composite's threshold must be chosen
   before `H` is introduced. The threshold for `compose_equivalent_compose`
   would have to be a function of `y_mid'`, which depends on `H`
   — circular.

3. **Choose `h₀(y₀) = min(H₁(y₀), inf_{y_mid'} H₂(y_mid'))`**:
   the infimum can be `0` without extra hypotheses (e.g., if
   `H₂(y_mid')` decays to `0` as `y_mid'` varies). Without
   continuity / uniformity of `H₂`, this approach has no
   guarantee.

4. **Use `IsRKOneStep_exists` on M₁' at y₀** to construct
   `y_mid'_canonical(H)`: produces a specific `y_mid'(H)`, but the
   threshold for `H₂(y_mid'(H))` still depends on `H` — same
   circularity.

5. **Continuity argument**: show `H₂(y_mid'(H)) → H₂(y₀)` as `H
   → 0` (by continuity of M₁'-step in H), then bound the
   composite's threshold uniformly below. Requires continuity of
   the extracted `H₂` function, which is NOT given by the
   abstract `Equivalent` type (the existential is extracted via
   choice, not given as a continuous function).

## Why Butcher's textbook proof works

Butcher's §382 proof reads:

> If f satisfies a Lipschitz condition and if h is sufficiently
> small, then y₁ = ŷ₁ because m₁ ≡ m̂₁, and y₂ = ŷ₂ because m₂ ≡
> m̂₂.

"h sufficiently small" implicitly assumes a **uniform** smallness
threshold across all initial values — Butcher does not consider
the dependence of h₀ on y₀. Every concrete `Equivalent` instance
in our codebase has a y₀-uniform threshold:

- `equivalent_self`: threshold is `1/(2*(L*C+1))` where `C := Σᵢⱼ
  |M.Aᵢⱼ|` — independent of y₀.
- `Equivalent.symm`: re-uses input's threshold — uniform iff input
  is uniform.
- `Equivalent.trans`: takes min of three thresholds, including a
  Banach smallness threshold of the middle method — uniform iff
  inputs are uniform.

But the abstract `Equivalent` type does not expose this — when
we receive `hEq : M.Equivalent M'` as a hypothesis, we can only
extract a threshold per y₀, not a uniform one.

## Possible solutions

### Option A: Strengthen `Equivalent` to be uniform (recommended)

Change the definition to:

```lean
def Equivalent {s s' : ℕ} (M : RKTableau s) (M' : RKTableau s') : Prop :=
  ∀ {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [CompleteSpace N]
    (f : N → N) (L : ℝ≥0) (_hL : LipschitzWith L f),
    ∃ h₀ > (0 : ℝ), ∀ (y₀ : N), ∀ h, 0 < h → h ≤ h₀ →
      ∀ y₁ y₁', M.IsRKOneStep f y₀ h y₁ → M'.IsRKOneStep f y₀ h y₁' →
        y₁ = y₁'
```

This matches Butcher's implicit assumption (uniform smallness).
Existing proofs port verbatim:
- `equivalent_self`: just move the `y₀` binder; the threshold
  `1/(2*(L*C+1))` is already y₀-independent.
- `Equivalent.symm`: same structure, threshold passes through.
- `Equivalent.trans`: same threshold construction (min of three),
  all y₀-independent.

**Estimated scope**: ~30 LOC of churn across cycles 203/204/206
(`equivalent_self`, `Equivalent.symm`, `Equivalent.trans`) plus
downstream consumers (`PReducesTo.toEquivalent`,
`paddedEuler_equivalent_*`, the `Setoid` instances at cycles
211/212). All updates are mechanical — move the `∀ y₀` binder
inside.

**Cycle 216 entry point**: refactor `Equivalent` to uniform form,
re-verify all axiom-cleanliness, then re-attempt
`compose_equivalent_compose` with the cycle 215 strategy's recipe.

### Option B: Add uniformity as an explicit hypothesis

```lean
theorem compose_equivalent_compose
    (hEq₁_uniform : ∃ h₀ > 0, ∀ {N} ..., ∀ y₀, ∀ h ≤ h₀, ...)
    (hEq₂_uniform : ...)
    : ...
```

This is faithful to Butcher's implicit assumption but adds
hypothesis complexity at every call site. Not recommended;
Option A is cleaner.

### Option C: Drop cycle 215's deliverable

Abandon `compose_equivalent_compose` as currently scoped; ship
only the structural infrastructure (cycle 214's iff) without the
(382g) form of `thm:382A`. Significantly weakens the path to
`thm:382A` and the §382 group structure.

Not recommended.

## Cycle 215 deliverable

Per the cycle 215 strategy's abort threshold (§H), this cycle
ships:

1. **`RKTableau.compose_equivalent_compose`** in
   `OpenMath/Chapter3/Section381.lean` as a **sorry-scaffolded**
   theorem statement, with the docstring documenting the
   quantifier-order gap and pointing to this issue file.
2. **P2 paddedEuler non-vacuity `example`** in
   `OpenMath/Chapter3/Section381.lean` exercising the scaffold's
   signature with reflexive equivalence inputs. (Sorry-scaffolded
   theorem still typechecks, so the example compiles.)
3. **This issue file** documenting the gap and proposing Option A
   as the cycle 216 resolution.
4. **`lean_status.json` thm:382A row**: status `unformalized` →
   `partial` (the signature is locked in, the body is deferred).
5. **`plan.md` thm:382A row**: `[ ]` → `[~]` with the gap noted.
6. **`thm_382A_path.md`**: cycle 215 update appended noting the
   gap and pointing here.

Sorry count: 0 → 1. Supervisor will scrutinize but the
scaffolded signature preserves cycle 214's gain and unblocks
cycle 216 with a named target.

## Recommendation

Cycle 216 should pursue **Option A** (uniform-threshold refactor
of `Equivalent`). The refactor is mechanical (~30 LOC of binder
movement across ~5 theorems), matches Butcher's implicit
assumption, and unblocks `compose_equivalent_compose` with the
cycle 215 strategy's recipe (~20 LOC body) cleanly.

After cycle 216 lands the refactor + the (382g) form, cycles
217+ can pursue the heterogeneous-stage form and the bracketed
`composeQ` lift per `.prover-state/issues/thm_382A_path.md`.
