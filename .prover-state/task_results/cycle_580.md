# Cycle 580 Results

## Worked on

§386 convolution associativity for `bSeriesConv` in
`OpenMath/ButcherGroup/Section386Conv.lean`, per the cycle 580 strategy
("Connes–Kreimer convolution associativity") that named

    bSeriesConv (bSeriesConv α β) γ τ = bSeriesConv α (bSeriesConv β γ) τ

as the structural law unblocking a tableau-level antipode for the
Butcher group in §388.

## Approach

Followed the strategy's required sorry-first / Aristotle-first /
verify-compile workflow:

1. Staged the headline statement `bSeriesConv_assoc` as a sorry-first
   theorem alongside three companions:
   * `bSeriesConv_assoc_leaf` — leaf base case.
   * `bSeriesConv_assoc_node_nil` — empty-children-node base case.
   * `bSeriesConv_assoc_singleton_leaf` — sanity check at
     `node [leaf]` (strategy step 5).

2. Started with the singleton-leaf sanity check, expanding both sides
   via the existing `bSeriesConv_node_singleton_leaf` /
   `bSeriesConv_leaf` / `bSeriesConv_node_nil` unfolding lemmas.
   The `rw … ring` proof failed with a residual
   `α(leaf) · bSeriesConv β γ (node [])` term that could not be
   absorbed into the LHS.

3. Verified the discrepancy directly with `lean_run_code`, instantiating
   `α ≡ 1`, `β ≡ 0`, `γ ≡ 1`. The two sides evaluated to `1` and `2`
   respectively, confirming the headline identity is **false** for
   `bSeriesConv` as currently defined.

## Result

SUCCESS (revised target).

The cycle-580 headline target is **false**. The deliverables landed are:

* `bSeriesConv_assoc_leaf` and `bSeriesConv_assoc_node_nil` —
  honest but degenerate base cases at trees with no proper admissible
  cut (no sorry, no Aristotle dependency).
* `bSeriesConv_assoc_singleton_leaf_counterexample` — Lean-checked
  existential counterexample at `τ = node [leaf]`, ruling out a
  literal Connes–Kreimer associativity for the present `bSeriesConv`.
* `.prover-state/issues/butcher_section386_associativity_false.md` —
  detailed structural diagnosis: the asymmetric treatment of the
  empty pruned forest (the trivial cut `(some τ, 1)` contributes
  `β(τ)` without an `α`-prefactor while the "everything pruned" cut
  `(none, α(τ))` is filtered out) breaks associativity at every tree
  with a non-trivial admissible cut.
* `.prover-state/issues/butcher_section388_left_cancellation.md` —
  cycle 580 status update tying the false §388 left-cancellation
  (cycle 578) and the false §386 associativity to the same root
  cause.
* `plan.md` — §38 narrative updated.

## Aristotle batch

No Aristotle jobs were submitted this cycle. After the
`lean_run_code` counterexample showed the headline is mathematically
false, the strategy's sorry-first/Aristotle-first workflow no longer
applied: there is nothing to ask Aristotle to prove. Submitting jobs
would have generated stalled or HTTP-429 traffic and consumed budget
without forward progress. The four false-headline-driven Aristotle
jobs scheduled by the strategy (headline, leaf, `node []`, two-cut
combinator) are documented as moot in the issue file above.

## Dead ends

* Attempted `rw … ring` for the singleton-leaf sanity check —
  failed with the leftover `α(leaf) · bSeriesConv β γ (node [])`
  term that has no counterpart on the LHS.
* Considered formulating the strategy's "two-cut combinator" as the
  acceptable cycle minimum.  Without an associativity theorem for it
  to power, the combinator has no consumer; the relevant
  combinatorial bridge — admissible cuts of `τ` versus pairs of cuts
  on a `bSeriesConv` argument — only matches under the symmetric
  augmented variant of `bSeriesConv` proposed in the issue file.
* Considered pivoting to the §372 Symplectic order-conditions backup
  target. That requires a separate `HasSymplecticOrder` predicate
  whose textbook definition the current cycle has not validated; the
  "trivial" follow-up framing in the strategy hides a definitional
  judgment that should be a planner decision, not a worker pivot.

## Discovery

* The same asymmetric-empty-pruned-forest defect that cycle 578
  identified as the obstruction to §388 left-cancellation also
  obstructs §386 associativity. These are not two independent
  problems; both are downstream of the shape of the
  `(some τ, 1)` / `(none, α(τ))` split in `BTree.innerCut`.
* The smallest counterexample to associativity is `node [leaf]`
  with constant coefficients, so any future §388/§386 work that
  uses associativity *must* either redefine `bSeriesConv` or
  restrict to trees with no proper admissible cut (only `leaf` and
  `node []`).
* The cycle 575–579 inverse-coefficient infrastructure remains
  technically valid but no longer admits the planned algebraic
  justification. The clean path forward is the augmented-coefficient
  pivot recorded in the new issue file.

## Suggested next approach

Per the new issue file, the cleanest pivot is to define an
**augmented convolution** `bSeriesConvAug (α₀ β₀ : ℝ) (α β : BTree → ℝ)`
that sums the *full* `BTree.innerCut` list (including the
`(none, α(τ))` branch) using a designated empty-forest scalar pair.
Concretely:

* `bSeriesConvAug α₀ β₀ α β τ` includes the term `α(τ) · β₀` for the
  "everything pruned" branch and `α₀ · β(τ)` for the "everything
  kept" branch, plus the existing proper inner-cut sum.
* With `α₀ = β₀ = γ₀ = 1` (Hopf-algebra unitality), associativity
  `bSeriesConvAug · · (bSeriesConvAug · · α β) γ
     = bSeriesConvAug · · α (bSeriesConvAug · · β γ)` becomes the
  honest Connes–Kreimer associativity and the cycle 580 strategy's
  step plan (two-cut combinator → mutual `BTree.rec`) applies cleanly.
* Map the existing `bSeriesConv` to the augmented form via
  `bSeriesConv α β τ = bSeriesConvAug 1 0 α β τ` (or the matching
  asymmetric pair) so cycles 542–579 remain reusable.

Once associativity for the augmented variant is in hand, retry the
§388 antipode / two-sided inverse construction directly, no longer
stuck on the asymmetric defect.
