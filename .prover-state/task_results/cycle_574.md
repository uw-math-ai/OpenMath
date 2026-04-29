# Cycle 574 Results

## Worked on

§387 power-bridge layer for `G1 p`. Lifted the existing
`QuotEquiv.npow` machinery (cycles 505–513) to the `Monoid.npow` `^`
notation now provided by cycle 573's `instMonoid (G1 p)`. All edits
landed in `OpenMath/ButcherGroup.lean` (no new tracked module).

## Approach

Five-deliverable strategy from `.prover-state/strategy.md`:

1. `ButcherTableau.G1.mk_pow` — induction on `n`.
   - `n = 0`: both sides reduce to `G1.mk (Quotient.mk _ trivialTableau)`
     so closed by `rfl` after a `show` rewriting `(1 : G1 p)` as
     `mk (q.npow 0)`.
   - `n = k + 1`: used `pow_succ'` (i.e. `g ^ (k+1) = g * g^k`) to
     match `QuotEquiv.npow_succ q n = q.product (q.npow n)` directly.
     The inductive hypothesis plus `mul_mk` and `QuotEquiv.npow_succ`
     close the goal in three rewrites.
2. `ButcherTableau.G1.bSeriesHomAt_pow` — `rw [mk_pow]; rfl`. The
   second `rfl` exploits `bSeriesHomAt p τ hτ (mk q') = q'.bSeriesHom τ`
   (definitional through `Quotient.lift`), and `bSeriesHom q' τ` is in
   turn `bSeries q' τ` by definition.
3. `ButcherTableau.G1.bSeriesHomAt_pow_zero` — `rw [pow_zero]` then
   `bSeriesHomAt_one`. Tagged `@[simp]`.
4. `ButcherTableau.G1.bSeriesHomAt_pow_one` — `rw [pow_one]`.
   Tagged `@[simp]`.
5. `ButcherTableau.G1.one_pow_eq` — `show ((1 : G1 p)) ^ n = (1 : G1 p);
   exact one_pow n`. Tagged `@[simp]`.

## Result

SUCCESS. All five lemmas land, `lake env lean OpenMath/ButcherGroup.lean`
exits 0, and `lake build OpenMath.ButcherGroup` rebuilds end-to-end in
~9s. `lean_verify` on `G1.mk_pow` and `G1.bSeriesHomAt_pow` reports
axioms `{propext, Classical.choice, Quot.sound}` — no new axioms beyond
the ambient quotient surface. Sorry count across `OpenMath/` remains 0.
File size grew from 2841 → 2895 lines, well under the 3000-line cap.

## Dead ends

- First attempt used `pow_succ` (i.e. `a^(k+1) = a^k * a`), which left
  the goal as `(q.npow k).product q ≈ q.product (q.npow k)` — a
  product-commutativity statement that does *not* hold at the raw
  tableau level (different stage permutations for the right-block).
  Switching to `pow_succ'` (i.e. `a * a^k`) aligned the multiplication
  order with `QuotEquiv.npow_succ` and removed the need for any
  product-commutativity lemma.
- An unused `ButcherProduct.bSeries_comm` reference from the first draft
  was removed; that lemma does not exist in the codebase and does not
  need to exist.

## Discovery

- The bridge between `Monoid.npow` and a hand-rolled `npow` reduces to a
  single recurrence-orientation choice: pick `pow_succ'` (left-mult)
  whenever your hand-rolled recursion is `a.product (a.npow n)`, or
  `pow_succ` (right-mult) for the reverse. No commutativity needed
  either way.
- The strategy's optional bonus `pow_eq_one_zero` was reframed as
  `one_pow_eq` (powers of the identity), which actually states the
  intended invariance (`one ^ n = one`); the name in the strategy was a
  typo. Implementation falls out of `Monoid.one_pow` immediately.

## Suggested next approach

The §388 inverse construction on the unit-stage subgroup of `G1 p` is
the next planned §38 layer. Recursion on tree order is the only known
route. A natural decomposition:

1. Define the unit-stage predicate
   `IsUnit g := bSeriesHomAt p BTree.leaf … g = 1` (the augmentation
   condition in Connes-Kreimer language).
2. Define `inverseCoeff p g : BTree → ℝ` recursively via
   `inverseCoeff τ = -(g.bSeries τ + Σ_{cuts} g.bSeries(trunk) *
   inverseCoeff(forest))` (Möbius inversion on the rooted-tree poset).
3. Build a representative `QuotEquiv` whose `bSeries` matches
   `inverseCoeff` on every tree of order ≤ p (this is where the §384
   convolution closure plus `bSeriesHomAt_pow` already give us the
   needed shadow lemma).
4. Define `G1.inv g := mk (...)` and prove `g * g.inv = one` and
   `g.inv * g = one` for `g` unit-stage.
5. Install `Group` instance on the subgroup.

This is a multi-cycle target. A reasonable cycle 575 deliverable is
just steps 1 and 2, plus the recursion termination and the first
sanity lemma `bSeriesHomAt_inv_leaf`. The cycle 574 strategy
explicitly defers Aristotle for trivial bridges and keeps it for the
inverse seam — saving the budget pays off for step 3, where the
`(trunk, cuts)` recursion has multiple non-trivial sub-lemmas.

## Aristotle

Skipped per strategy: the five bridge lemmas were one-line / short
induction proofs and would not have benefited from a 30-minute
submission cycle. No optional inverse-scaffold sketch was attempted
this cycle; the deliverables landed cleanly and the inverse layer is
better staged from a planner's seat than from a single Aristotle
batch.
