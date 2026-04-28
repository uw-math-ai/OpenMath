# Cycle 496 Results

## Worked on

Butcher §381 (relabeling-equivalence layer) — the easy half of the §38
Butcher group programme. New tracked file `OpenMath/ButcherGroup.lean`
with zero live `sorry`s.

## Approach

Followed the cycle 496 planner strategy verbatim:

1. Wrote `OpenMath/ButcherGroup.lean` containing exactly the six items the
   strategy specified — `IsRKEquivalent`, `refl`, `symm`, `trans`,
   `Setoid` instance, and the sanity lemma `weights_sum_eq` — plus a one
   line import in `OpenMath.lean`.
2. Used `Equiv.Perm (Fin s)` throughout (not raw `Fin s → Fin s`), so
   `Finset.sum_equiv` / `Equiv.sum_comp` apply directly.
3. Did **not** define `ButcherProduct`, associativity, `G₁`, identities,
   inverses, or powers — those remain open under the same Current Target.
4. Did **not** transplant any of the four ready Aristotle bundles
   (`344f2d53…`, `8314c9b0…`, `75e7effc…`, `d8b55aa9…`); per the strategy
   they all encode the abandoned cycle 495 four-parameter
   `ButcherProduct` surface and `COMPLETE_WITH_ERRORS`.

## Result

SUCCESS — all six items landed, zero `sorry`s, `lake build` clean.

- `OpenMath/ButcherGroup.lean` compiles (`lake env lean
  OpenMath/ButcherGroup.lean` → no output, exit 0).
- `lake build` succeeds (8073/8073 jobs; `Built OpenMath.ButcherGroup` and
  the umbrella `Built OpenMath`).
- `grep sorry OpenMath/ButcherGroup.lean` → empty.

### Concrete declarations landed

- `ButcherTableau.IsRKEquivalent : ButcherTableau s → ButcherTableau s →
  Prop` — `∃ σ : Equiv.Perm (Fin s)`, `t₂.A i j = t₁.A (σ i) (σ j)` and
  matching `b`/`c` clauses.
- `ButcherTableau.IsRKEquivalent.refl` — witness `Equiv.refl _`.
- `ButcherTableau.IsRKEquivalent.symm` — witness `σ.symm`, closed by
  `Equiv.apply_symm_apply` rewrites.
- `ButcherTableau.IsRKEquivalent.trans` — witness `τ.trans σ` (note: not
  `σ.trans τ` — see *Discovery* below).
- `ButcherTableau.isRKEquivalentSetoid : Setoid (ButcherTableau s)` —
  bundles refl/symm/trans.
- `ButcherTableau.IsRKEquivalent.weights_sum_eq` — proved with
  `Equiv.sum_comp σ t₁.b` plus a `Finset.sum_congr` rewrite via the `b`
  clause.

## Dead ends

The first attempt at `trans` used `σ.trans τ` as the witness. That is the
wrong direction: `(σ.trans τ) i = τ (σ i)`, but the goal needs
`σ (τ i)` (because `t₂.A i j = t₁.A (σ i) (σ j)` and `t₃.A i j =
t₂.A (τ i) (τ j) = t₁.A (σ (τ i)) (σ (τ j))`). Switching the witness to
`τ.trans σ` made the goal `rfl`-closable.

## Discovery

- `Equiv.trans` in Mathlib is **post-composition**: `(σ.trans τ) i =
  τ (σ i)`. When chaining relabeling permutations across
  hypotheses of the form `f i = g (σ i)`, you compose the outer-then-inner
  permutation as `inner.trans outer`. Worth pinning for the §382
  composition / §383 elementary-weight work to come.
- `Equiv.sum_comp σ f : ∑ i, f (σ i) = ∑ i, f i` is the right shape for
  reindexing `b`/`c` sums under a stage permutation; no `Finset.sum_equiv`
  ceremony needed for full-domain sums over `Fin s`.

## Aristotle this cycle

Did not submit. The strategy explicitly authorised at most one Aristotle
batch and only if a non-trivial step did not close manually within five
minutes. Every step closed within seconds, so no submission was made.

The four ready bundles from cycle 495
(`344f2d53-1a38-4b4a-a2dc-bc720506bd3e`,
`8314c9b0-d74e-41dc-8ff6-4da6f7896a93`,
`75e7effc-e77f-468c-b676-0fb5aeeacfa2`,
`d8b55aa9-56ae-4880-b48f-77f32effbca7`) all reference the abandoned
four-parameter `ButcherProduct` from the reverted cycle 495 and were not
incorporated.

## Suggested next approach

The Current Target `Butcher §38` is **not** rotated; only one bullet
(§381 relabeling-equivalence) is `[~]`. §380, §382, §383, §384, §385,
§386, §387, §388, §389 remain `[ ]`.

Concrete next-cycle moves, easiest to hardest:

1. **§387 identity element on `IsRKEquivalent`-classes.** Define a
   1-stage trivial tableau (`A = 0`, `b = 1`, `c = 0`) and prove the
   `(0+1)-stage` "identity" lemma at the *single-stage-count* level — i.e.
   show that on `ButcherTableau s` the `IsRKEquivalent`-class of any
   tableau is preserved under the trivial relabel. This stays inside
   the §381 layer landed this cycle.
2. **§381 cross-stage-count equivalence (the genuine quotient).** Define
   `IsRKEquivalent'` between tableaux of different stage counts by
   embedding into `Fin (s ⊔ t)` (or, more practically, by defining a
   "stages of nonzero weight" canonical form). This is the prerequisite
   for any associative `ButcherProduct` on classes — the cycle 495
   structural mismatch (`[γ₁δ₁, γ₁δ₂, γ₂]` vs `[γ₁, γ₂δ₁, γ₂δ₂]`)
   only becomes resolvable once we admit padding with zero-weight stages.
3. **§383 prep — order-conditions tree-indexed coefficients.** Even
   without the group structure we can land the elementary-weight map
   `Φ : ButcherTableau s → (RootedTree → ℝ)` and show it descends to
   `IsRKEquivalent`-classes (because Φ is symmetric under
   permutations of the stages — that is exactly what the §381 layer
   proves at the level of weights / matrices).

Either #1 or #3 is a clean cycle-497 target. Avoid #2 until the planner
writes a fresh issue file with a textbook-grounded recipe (Butcher §381
discusses padding by zero-weight stages explicitly; the cycle 495 attempt
did not).
