# Issue: `bSeriesConv` is not associative as currently defined

## Blocker

The cycle 580 strategy named convolution associativity for
`bSeriesConv`,

    bSeriesConv (bSeriesConv α β) γ τ
      = bSeriesConv α (bSeriesConv β γ) τ,

as a "real theorem (the formal-power-series ring on rooted trees is
associative)" and the structural law that would unblock a tableau-level
antipode for the §38 Butcher group.  This identity is **false** for
`bSeriesConv` as defined in
`OpenMath/ButcherGroup/Section386Conv.lean`.

## Counterexample

Take `α ≡ 1`, `β ≡ 0`, `γ ≡ 1` and `τ = BTree.node [BTree.leaf]`.

Using the existing unfolding lemma
`bSeriesConv_node_singleton_leaf`:

    bSeriesConv α β (node [leaf]) = β (node [leaf]) + α(leaf) · β(node []),

we evaluate both sides.

* LHS  `bSeriesConv (bSeriesConv α β) γ (node [leaf])`
       = `γ (node [leaf]) + (bSeriesConv α β)(leaf) · γ (node [])`
       = `γ (node [leaf]) + β(leaf) · γ (node [])`
       = `1 + 0 · 1 = 1`.
* RHS  `bSeriesConv α (bSeriesConv β γ) (node [leaf])`
       = `(bSeriesConv β γ)(node [leaf]) + α(leaf) · (bSeriesConv β γ)(node [])`
       = `(γ(node [leaf]) + β(leaf) γ(node [])) + α(leaf) γ(node [])`
       = `1 + 0 + 1 = 2`.

Discrepancy: `1 ≠ 2`.

This counterexample is landed in Lean as

    ButcherTableau.bSeriesConv_assoc_singleton_leaf_counterexample

in `OpenMath/ButcherGroup/Section386Conv.lean`.

## Why it fails — structural reason

The `bSeriesConv` definition treats the empty pruned forest
**asymmetrically**:

* The trivial cut `(some τ, 1)` in `BTree.innerCut` contributes
  `1 · β(τ) = β(τ)` — i.e., the convolution at the trivial cut sees
  *no* `α`-prefactor.
* The "everything pruned" cut `(none, α(τ))` is filtered out by
  `c.1.map`, contributing nothing — i.e., the convolution at the
  full cut sees *no* `γ`-correction.

In Hopf-algebra language this is the convention `α(empty) = 1`,
`β(empty) = 0` (or symmetrically: γ-side empty value `0`).  The
standard Connes–Kreimer convolution requires *both* sides to have
the same empty-value convention (typically `1`), corresponding to
the full coproduct

    Δ τ = τ ⊗ 1 + 1 ⊗ τ + ∑ proper cuts P ⊗ R.

Because `bSeriesConv` drops the `τ ⊗ 1` term, the RHS picks up
a `β`-correction at the full trunk that the LHS cannot match: the
outer `bSeriesConv α β` on the LHS only ever sees *proper* pruned
subtrees, never `τ` itself.

The general algebraic shape of the discrepancy is

    bSeriesConv α (bSeriesConv β γ) τ  −  bSeriesConv (bSeriesConv α β) γ τ
      =  ∑ over admissible cuts (P, R) of τ with R ⊊ τ
              (∏_{p ∈ P} α(p)) · (∑ over proper cuts (P', R') of R, β(P') γ(R'))
        − ∑ over admissible cuts (P, R) of τ with R ⊊ τ
              (∏_{p ∈ P} (β-shifted α at p)) · γ(R),

which collapses to the missing `α(P) β(R) γ(empty)`-type terms in the
asymmetric convention.

## Salvageable content

The two degenerate base cases at trees with no proper admissible cut
*are* true and have been landed as standalone lemmas:

* `bSeriesConv_assoc_leaf`
* `bSeriesConv_assoc_node_nil`

Both reduce to `bSeriesConv_leaf` / `bSeriesConv_node_nil`: at `leaf`
or `node []` there is only the trivial admissible cut, so both sides
collapse to `γ τ`.  These lemmas are honest but degenerate; they do
not extend to a general associativity statement.

## What was tried

* Stated `bSeriesConv_assoc` as a sorry-first headline and noticed
  immediately that the singleton-leaf sanity check failed: under
  `bSeriesConv_node_singleton_leaf` the two sides disagree by an
  `α(leaf) · γ(node [])` term.
* Verified the discrepancy directly with `lean_run_code` using the
  constants `α ≡ 1`, `β ≡ 0`, `γ ≡ 1`.
* Replaced the false sorry with the counterexample theorem above.

This mirrors cycle 578's discovery that the §388 left-cancellation
identity is also false under the current `inverseCoeff` recursion.

## Possible solutions

1. **Redefine `bSeriesConv` symmetrically.** Replace the current
   `((τ.innerCut α).filterMap fun c => c.1.map …).sum` with a sum
   that includes the "everything pruned" branch, picking up an
   `α(τ)`-prefactor and a designated empty-trunk value of `β`.
   Concretely, distinguish `BTree → ℝ` (no empty value) from
   `Option BTree → ℝ` (with the "empty forest" represented as
   `none`) and demand both `α none = 1` and `β none = 1`.

2. **Restrict to "augmented" coefficient maps.** Define a pair
   `(α₀, α : BTree → ℝ)` where `α₀` is the empty-forest value (a real
   scalar), and make `bSeriesConv` use `α₀` when the pruned forest is
   empty.  Associativity then holds when `α₀ = β₀ = γ₀ = 1`.

3. **Project to the `bSeries`-only image.** Many of the §38 identities
   we actually want only need the special case where `α = t.bSeries`
   for some tableau `t`.  In that case `t.bSeries(empty) := 1` is the
   natural unitality convention and the standard associativity holds
   when paired with a similarly-augmented `bSeriesConv`.

4. **Rewrite §388 antipode work to use a different convolution.**  The
   tableau-level antipode goal in §388 needs an associative
   convolution; option (1) or (2) is the cleanest path.

(1) is the most invasive but mathematically correct option.  (2) is
the cheapest source-of-truth pivot.

## Implications for the §38 plan

* The cycle 578 issue file
  `butcher_section388_left_cancellation.md` — the false
  left-cancellation identity — is now recognised as a downstream
  manifestation of the same asymmetric-convolution defect.  Both
  failures share the same root cause: the trivial cut contributes
  `β(τ)` with no `α`-prefactor while the full cut is filtered out.
* The tableau-level antipode in §388 cannot be built on the current
  `bSeriesConv`.  Cycles 575–579 inverse-coefficient infrastructure
  remains technically correct but no longer admits the planned clean
  algebraic justification through associativity.
* Any future cycle aiming at §388 must first pick option (1)–(4)
  above and execute it, before retrying associativity or the
  antipode.

## Suggested next-cycle approach

* Pick option (2) (augmented coefficients) as the smallest pivot and
  define `bSeriesConvAug (α₀ β₀ : ℝ) (α β : BTree → ℝ) τ` summing the
  full inner-cut list (including `(none, α(τ))` weighted by `β₀`).
* Re-state and re-prove convolution associativity for this augmented
  variant; the strategy 580 step plan (two-cut combinator → mutual
  `BTree.rec`) applies cleanly there.
* Map the existing `bSeriesConv` into the augmented form via
  `bSeriesConv α β τ = bSeriesConvAug 1 0 α β τ` (or whatever the
  correct boundary values turn out to be) so that prior work is
  reused, not invalidated.

## Cycle 581 status update

Cycle 581 landed the narrow one-sided augmented variant in
`OpenMath/ButcherGroup/Section386Conv.lean`:

    noncomputable def bSeriesConvAug
        (β₀ : ℝ) (α β : BTree → ℝ) (τ : BTree) : ℝ :=
      bSeriesConv α β τ + α τ * β₀

The exact proved unfoldings are `bSeriesConvAug_leaf`,
`bSeriesConvAug_node_nil`, and `bSeriesConvAug_node_singleton_leaf`.
The singleton-leaf associativity sanity check is landed in the raw
unit-empty form

    theorem bSeriesConvAug_assoc_singleton_leaf
        (α β γ : BTree → ℝ) :
        bSeriesConvAug 1 (fun τ => bSeriesConvAug 1 α β τ) γ
            (BTree.node [BTree.leaf])
          = bSeriesConvAug 1 α (fun τ => bSeriesConvAug 1 β γ τ)
            (BTree.node [BTree.leaf])

and closes by direct expansion plus `ring`.  For the cycle-580
counterexample coefficients `α ≡ 1`, `β ≡ 0`, `γ ≡ 1`, both sides now
evaluate to `3` at `BTree.node [BTree.leaf]`.

The more heavily scalar-parametric formula from the cycle prompt was
not landed: with only the right empty-forest scalar represented in
`bSeriesConvAug`, arbitrary non-unit intermediate empty values are not
tracked symmetrically.  The full unit-empty associativity theorem is
left as the planned proof surface `bSeriesConvAug_assoc`.
