# Cycle 524 Results

## Worked on

Butcher §384 right-block structural equivalence in
`OpenMath/ButcherGroup.lean`, immediately after the cycle 523
closed-form auxiliary scaffolding.

Added:
- `ButcherProduct.rightAuxAt_eq_rightAuxAtCoef_bSeries` (headline)
- `ButcherProduct.elementaryWeight_natAdd_eq_rightAuxAtCoef` (S1)
- `ButcherProduct.bSeries_natAdd_eq_rightAuxAtCoef` (S2)

## Approach

1. Wrote the headline theorem with `BTree.rec` (no list-helper
   factor-out needed) carrying two motives:
   - `motive_1 : BTree → Prop` — pointwise equality at each `Fin t`
     stage index.
   - `motive_2 : List BTree → Prop` — `∀ c ∈ children, ∀ j, …`,
     propagating the IH per-child.
2. Closed the leaf case via the existing
   `ButcherProduct.rightAuxAt_leaf_eq_coef`.
3. Closed the node case by rewriting the LHS with
   `rightAuxAt_node_eq_coef_one_level` and the RHS with
   `rightAuxAtCoef_node`, both into the same powerset-sum shape, then
   peeling `Finset.sum_congr → Finset.prod_congr → Finset.sum_congr`
   down to the per-child equality, supplied by `motive_2` via
   `List.get_mem children p`.
4. The `nil` motive_2 case is vacuous (`simp at hc`); the `cons` case
   destructs membership with `List.mem_cons.mp`, dispatching to the
   head IH or the tail IH.
5. S1 (`elementaryWeight_natAdd_eq_rightAuxAtCoef`) is one rewrite
   composing `elementaryWeight_natAdd` with the headline equality.
6. S2 (`bSeries_natAdd_eq_rightAuxAtCoef`) is `Finset.sum_congr rfl`
   composed with S1.

## Result

SUCCESS — headline theorem and both stretch goals S1 and S2 landed
with no remaining `sorry`s in `OpenMath/ButcherGroup.lean`.

Verification:
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ButcherGroup.lean`
  succeeded.
- `grep -c sorry OpenMath/ButcherGroup.lean` returned `0`.
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build OpenMath.ButcherGroup`
  succeeded with only pre-existing `OpenMath.OrderConditions` info
  output.

`plan.md` records the new declarations under §384 in the chapter ledger
and in the `## Current Target` body. §38 remains active.

## Aristotle status

Did not submit this cycle. The headline proof was direct enough to
close manually in one pass without sorry-first iteration: the
`BTree.rec` structure plus three `Finset.{sum,prod}_congr` peels lined
up cleanly with the existing one-level node lemma. Aristotle has been
returning HTTP 429 on every recent submission (cycles 504, 509, 511,
512, 513, 515, 516, 517, 519, 521, 522, 523), and the strategy
explicitly capped this cycle at one batch with no retry on 429, so
queueing a job for an already-closed result would have been pure
overhead.

## Dead ends

Initial sketch used `List.not_mem_nil c` and `rcases hc with rfl | hc`,
but `List.not_mem_nil` now expects an `_ ∈ []` proof rather than the
list element, and the bare `rcases` cannot destructure
`c ∈ head :: tail` directly. Switched to `simp at hc` for the nil case
and `List.mem_cons.mp hc` for the cons case. No proof-search dead ends
on the headline equality itself.

## Discovery

For per-child IH propagation through `BTree.rec`, the
`motive_2 := fun children => ∀ c ∈ children, ∀ j, …` shape is cleaner
than the `motive_2 := fun children => ∀ i, foldr ... = foldr ...`
shape used in cycles 519 / 520. The latter was needed because those
proofs threaded the inductive hypothesis through a live `foldr`
recursion in the goal; here, both sides have already been rewritten
into a `Finset` sum/prod by the one-level lemmas, so the IH only
needs to fire pointwise per child, and the membership-quantified motive
makes the cons step a simple `rcases List.mem_cons.mp`.

The list-helper alternative the strategy described (cycle 521 idiom)
was unnecessary because the powerset-sum shape collapses the foldr
already.

## Suggested next approach

The next §384 seam — flagged by the strategy as the major gap after
the headline — is the closed `(trunk, cuts)` identification of

```
∑ i : Fin t, t₂.b i * rightAuxAtCoef t₂ coef τ i
```

as a sum of `(trunk, cuts)` contributions over the rooted-subtree
splits of `τ`. Concretely, this means proving by `BTree`-induction (or
`BTree.rec` with a list motive) that the closed-form auxiliary
satisfies a Butcher-style convolution: the trunk of `τ` is mapped by
`t₂.bSeries`, and each cut subtree contributes a `coef` factor. With
that lemma in hand, `coef := t₁.bSeries` will turn
`bSeries_natAdd_eq_rightAuxAtCoef` into the closed form
`(t₁.product t₂).bSeries τ - t₁.bSeries τ` requires.

Once the closed `(trunk, cuts)` form lands, the next seam after that
is `IsG1Equiv.product_congr`, then `G1.mul`, `G1.mul_mk`, and
`G1.bSeriesHomAt_mul`, all currently blocked on the §384 convolution
gap.
