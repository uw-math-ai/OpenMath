# Cycle 586 Results

## Worked on
Target 1 (PRIMARY): `mul_assoc_at_node_replicate_leaf` — depth-2 unital
associativity of `bSeriesConvAug` at every `BTree.node (List.replicate n BTree.leaf)`,
parametric in `n`. Plus the supporting closed form and a binomial-identity
helper. Target 3 (`mul_assoc_at_node_two_leaves`) was also locked in early
as a safety net.

## Approach
1. Submitted 5 Aristotle jobs at the start of the cycle (HTTP 429 — queue
   already saturated). Proceeded with manual closure per the strategy
   fallback.
2. Promoted three private helpers in `Section386Conv.lean` to the public
   namespace (`cutSum_filterMap_eq_map`, `innerCutForest_replicate_leaf_sum`,
   `sum_finset_fin_succ_card_eq`) so `Section386Aug.lean` can reuse them.
3. Added the closed form
   `bSeriesConvAug_node_replicate_leaf α β n` by chaining
   `bSeriesConvAug_node` (cycle 585) with `innerCutForest_replicate_leaf_sum`
   via the `cutSum_filterMap_eq_map β.toFun` bridge.
4. Built the binomial helper
   `replicate_leaf_assoc_aux a b n h : ∑ S, (b+a)^|S| h(n-|S|) = ∑ S, a^|S| ∑ T, b^|T| h(n-|S|-|T|)`
   by induction on `n`. Each `succ` step splits both outer sums via
   `sum_finset_fin_succ_card_eq`, applies IH to `h` and to the shifted
   `h' = h(·+1)`, and closes with `ring`. The RHS inner-sum split (the
   `succ`-card subgoal) was the trickiest mechanism — `simp only [Finset.mul_sum]`
   plus `pow_succ` plus `omega` for `Nat.sub` rewrites.
5. Wrote the headline `mul_assoc_at_node_replicate_leaf` proof:
   - `rw` the closed form on both sides;
   - `dsimp only` to reduce the `⟨1, …⟩.toFun` / `⟨1, …⟩.emptyVal`
     constructor projections;
   - `simp only [bSeriesConvAug_leaf, bSeriesConvAug_node_replicate_leaf,
     hβ', hγ', mul_one, mul_add, Finset.sum_add_distrib]` to fully expand;
   - `linear_combination` against `replicate_leaf_assoc_aux` to discharge.
   The decisive trick was `linear_combination` rather than alternating
   `congr 1` (which got tripped up by left/right associativity asymmetry
   produced by the `simp only` round).
6. Also added `bSeriesConvAug_node_two_leaves` (closed form) and
   `mul_assoc_at_node_two_leaves` (Target 3) as the n=2 instance / safety
   net.

## Result
SUCCESS. `OpenMath/ButcherGroup/Section386Aug.lean` and
`OpenMath/ButcherGroup.lean` both compile cleanly with no `sorry`. Targets 1
and 3 of the cycle 586 strategy are closed; the headline parametric
`mul_assoc_at_node_replicate_leaf` covers all `BTree.node (List.replicate n BTree.leaf)`
shapes uniformly.

## Dead ends
- `congr 2` after the `simp only` expansion split `(A + B) + C = A + (B + D)`
  into mismatched halves (left/right associativity differed). Switching to
  `linear_combination` finished cleanly without restructuring.
- An `bSeriesConvAug_eq_bSeriesConv_add` bridge approach was considered but
  abandoned: `bSeriesConv` is linear in its second argument only, so the
  symmetry needed for assoc doesn't transfer.
- Aristotle batch submission failed with HTTP 429 (queue full from prior
  cycles' 10+ in-flight jobs), so all closures were manual.

## Discovery
- `linear_combination` plus a reference equality is a much cleaner way to
  finish complex algebraic-rearrangement subgoals than alternating
  `add_assoc`/`congr 1` calls. Worth keeping in mind for future
  bSeriesConvAug parametric proofs.
- The base case of `replicate_leaf_assoc_aux` requires explicitly noting
  that `Finset (Fin 0)` is the singleton `{∅}`; plain `simp` reduced to
  `(b+a)^|default|` and stalled. The fix:
  `simp [show ∀ s : Finset (Fin 0), s = ∅ from fun s => by ext x; exact x.elim0]`.
- `Nat.sub` reasoning inside binomial identities is robustly handled by
  `omega` once the relevant `T.card ≤ n - S.card` hypothesis is in scope.

## Suggested next approach
- Lift to general `BTree` shape: replace `List.replicate n BTree.leaf` with
  `List.replicate n τ` for a fixed subtree `τ`, then with arbitrary
  `children : List BTree`. Both should follow the same playbook
  (`bSeriesConvAug_node` + a generalized binomial-style identity over
  the subset structure), though the "branch out admissible cuts" identity
  becomes more elaborate.
- Try the §388 antipode work next — the fully parametric replicate-leaf
  associativity is the depth-2 evidence base needed for that.
- If Aristotle becomes responsive, batch-submit the `List.replicate n τ`
  generalization.
