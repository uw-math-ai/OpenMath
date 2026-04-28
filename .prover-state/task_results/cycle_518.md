# Cycle 518 Results

## Worked on
§384 convolution prep in `OpenMath/ButcherGroup.lean`:
- Item (1): `foldr_mul_add_eq_powerset_sum` — list combinator that
  expands a `foldr`-style product of binomial sums as a
  `Finset.powerset`-indexed sum over which factor is taken from each
  list position. (Private helper, ℝ-valued.)
- Item (2):
  `ButcherProduct.elementaryWeight_natAdd_node_eq_powerset_sum` —
  the first node-level consumer at a `Fin.natAdd s i` row of
  `ButcherProduct t₁ t₂`, expressing the elementary weight of
  `node children` as a Finset.powerset-indexed sum over which
  children are "cut" (via the lower-left `t₁.b j₁` block) versus
  "kept" (via the lower-right `t₂.A i j₂` block).

## Approach
1. Reduced the `foldr` form to a `Finset.prod` over `Fin children.length`
   by induction with `Fin.prod_univ_succ`, then applied Mathlib's
   `Finset.prod_add` to reach the powerset form. This avoids having
   to reason about `List.sublists` / `List.diff` (which would have
   required `[BEq α]`).
2. For the consumer, split the inner sum
   `∑ k : Fin (s+t), (ButcherProduct t₁ t₂).A (natAdd s i) k * Φ k`
   into the two `Fin s` / `Fin t` blocks via `Fin.sum_univ_add`,
   reducing each block via `simp [ButcherProduct]`, then rewrote the
   `foldr` body using a `funext` and applied the combinator.

## Result
SUCCESS — both deliverables compile. `lake env lean
OpenMath/ButcherGroup.lean` and `lake build` both succeed
(`✔ Built OpenMath.ButcherGroup`, build completed 8073 jobs).

Tracked code remains sorry-free.

## Aristotle batch
Submitted three jobs in a single batch at the start of the cycle
(scaffolds in `.prover-state/aristotle_scaffolds/cycle_518/`):
- `foldr_mul_add_combinator.lean`
- `elementaryWeight_castAdd_block.lean` (the next-layer reduction)
- `elementaryWeight_natAdd_leaf.lean` (sanity base case)

All three returned **HTTP 429** ("too many requests in progress")
immediately, matching the strategy's prediction (cycles
503/504/509/511/512/513/515/516/517 history). Per the strategy, no
retries were attempted. Manual closure carried the cycle.

## Dead ends
- The strategy's signature for item (2) used `t₁.bSeries c` directly,
  which would require the upper-left elementary-weight block lemma
  `(ButcherProduct t₁ t₂).elementaryWeight τ (Fin.castAdd t i)
   = t₁.elementaryWeight τ i`. That lemma is not yet in the file
  (and doing the structural induction now would have crowded the
  cycle). Fell back to the explicitly-authorized variation: leave
  the cut-side factor as the raw inner sum
  `∑ j₁, t₁.b j₁ * (ButcherProduct t₁ t₂).elementaryWeight c (Fin.castAdd t j₁)`
  (equivalent to `t₁.bSeries c` once the upper-left block reduction
  is proved).

## Discovery
- Mathlib's `Finset.prod_add` is the right hammer for the binomial
  expansion at the list level once the foldr is converted to a
  Finset.prod over `Fin n`. The conversion goes through a clean
  induction with `Fin.prod_univ_succ` and the rfl-level identities
  `(c :: cs)[(0 : Fin (cs.length+1))] = c` and
  `(c :: cs)[(k.succ : Fin (cs.length+1))] = cs[k]`.
- `simp [elementaryWeight]` is the right unfold lemma at a node;
  raw `show ... from rfl` does **not** work because the
  `noncomputable def` carries a `termination_by` and the equation
  must be invoked through its auto-generated equation lemma.

## Suggested next approach
Cycle 519 should land the upper-left block reduction
`butcherProduct_elementaryWeight_castAdd : 
  (ButcherProduct t₁ t₂).elementaryWeight τ (Fin.castAdd t i)
  = t₁.elementaryWeight τ i`
by structural induction on `τ` (leaf is trivial; node splits
`∑ k : Fin (s+t)` into the s-block, which gives `t₁.A i j₁` paired
with the IH on each child, and the t-block, which is identically
zero because the upper-right `A` block is zero). Once that lands,
the cut factor in cycle 518's powerset identity rewrites to
`t₁.bSeries c` (via `Equiv.sum_comp` / `Finset.sum_congr`), bringing
us one layer closer to the closed-form `(trunk, cuts)` decomposition
needed for `IsG1Equiv.product_congr` and `G1.mul`.
