# Cycle 581 Results

## Worked on

§386 augmented b-series convolution in
`OpenMath/ButcherGroup/Section386Conv.lean`, targeting the cycle-580
associativity counterexample at `BTree.node [BTree.leaf]`.

## Approach

Followed the sorry-first workflow:

1. Added `bSeriesConvAug β₀ α β τ = bSeriesConv α β τ + α τ * β₀`.
2. Staged the three unfolding lemmas, the singleton-leaf associativity
   sanity check, and the planned full `bSeriesConvAug_assoc` proof surface
   with `sorry`.
3. Verified the sorry-first file with
   `lake env lean OpenMath/ButcherGroup/Section386Conv.lean`.
4. Submitted Aristotle against the staged file for
   `bSeriesConvAug_assoc_singleton_leaf`, but the service returned HTTP 429
   (`too many requests in progress`), so I used the strategy's manual
   fallback.
5. Closed the unfoldings by `simp` and closed the singleton-leaf check by
   direct expansion using `bSeriesConv_node_singleton_leaf`,
   `bSeriesConv_leaf`, `bSeriesConv_node_nil`, and `ring`.

## Result

SUCCESS.

Landed:

* `bSeriesConvAug`
* `bSeriesConvAug_leaf`
* `bSeriesConvAug_node_nil`
* `bSeriesConvAug_node_singleton_leaf`
* `bSeriesConvAug_assoc_singleton_leaf` in the raw unit-empty form:

      bSeriesConvAug 1 (fun τ => bSeriesConvAug 1 α β τ) γ
          (BTree.node [BTree.leaf])
        =
      bSeriesConvAug 1 α (fun τ => bSeriesConvAug 1 β γ τ)
          (BTree.node [BTree.leaf])

The concrete cycle-580 coefficients `α ≡ 1`, `β ≡ 0`, `γ ≡ 1`, with
unit empty values, now evaluate to `3` on both sides at
`BTree.node [BTree.leaf]`. This replaces the old unaugmented `1 ≠ 2`
counterexample at the same tree.

The full unit-empty associativity theorem is left as the planned
`bSeriesConvAug_assoc` stub, as directed by the cycle strategy.

## Dead ends

The fully scalar-parametric formula from the planner is too strong for the
narrow one-sided augmentation as landed: `bSeriesConvAug` records the right
empty-forest scalar `β₀`, but does not carry an independent left empty-forest
scalar through nested convolutions. I therefore landed the accepted raw
unit-empty singleton form instead of sorry-shifting through a false general
statement.

Aristotle did not create a project ID because the submission hit HTTP 429.

## Discovery

The missing full-cut term is exactly enough to repair the smallest
non-trivial associativity check under the standard unit-empty convention.
At `node [leaf]`, direct expansion gives the same polynomial on both sides;
for the cycle-580 constants the common value is `3`.

## Suggested next approach

Prove the deferred `bSeriesConvAug_assoc` theorem for the unit-empty
augmented convolution by building the two-cut/coassociativity bridge. If
future work needs non-unit empty values, introduce a genuinely two-sided
augmented coefficient structure carrying both left and right empty scalars
instead of overloading this one-sided helper.
