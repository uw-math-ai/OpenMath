# Issue: parametric strong induction for `forestSum_assoc`

## Blocker

Generalising cycle 598/599 to a single
`forestSum_assoc_children_order_le p` strong induction stalls in the
head case at any depth `p+1` because the LHS `forestSum (αβ) γ (c :: cs)`
must be expanded via the cons recurrence at the **product** coefficient
function `(αβ).toFun`, while the inductive hypothesis and the
`shift_agg` machinery only naturally expose the **α** cuts of `c`.

## Context

The cycle 598/599 head-case scheme has the following shape (working
inside `Section386Aug.lean`):

1. `forestSum_cons_<shape> α β c cs` expands `forestSum α β (c :: cs)`
   into the prune-root term `α(c) * forestSum α β cs` plus a sum over
   keep-root cuts of `c` (each indexed by a trunk `t` and a weight `w`
   coming from `c.innerCut α.toFun`).
2. `keyPt c xs` expresses `bSeriesConvAug β γ (BTree.node (c :: xs))` in
   terms of `bSeriesConvAug β γ (BTree.node xs)` and
   `bSeriesConvAug β (γ.shiftBy t) (BTree.node xs)` for each trunk `t`
   from `c.innerCut β.toFun`.
3. `aux` lifts that pointwise expansion to the L-aggregation that
   appears inside `forestSum α (Aug(βγ).shiftBy c) cs`.
4. `shift_<shape>_agg` combines `keyPt`, `aux`, and the IH instantiated
   at `γ` and at each `γ.shiftBy s` for `s ∈ c.innerCut β.toFun` to
   express `forestSum α (Aug(βγ).shiftBy c) cs` as a polynomial in
   `forestSum (αβ) γ cs` and `forestSum (αβ) (γ.shiftBy s) cs`.
5. The head case for shape `c` then uses `forestSum_cons_<shape>` on
   each of the three forest sums and closes by `linear_combination`.

Generalising to arbitrary `c` of order `≤ p+1` requires:

- `forestSum_cons_general` for arbitrary `c`: feasible from
  `bSeriesConvAug_innerForest_cons` (line 908) plus a list rewrite.
- `keyPt` for arbitrary `c`: feasible from
  `forestSum_cons_general` plus `bSeriesConvAug_node` twice.
- `shift_agg` for arbitrary `c`: feasible from `keyPt`, `aux`, and the
  IH (universal in `γ`).
- The head-case dispatch: this is where the wall lives.

## What was tried

Symbolic walk of the head case for an arbitrary head `c`:

* LHS expands as
  ```
  forestSum (αβ) γ (c :: cs) + forestSum α β (c :: cs) * γ.emptyVal
    = (αβ)(c) * forestSum (αβ) γ cs
      + Σ_{(some t, w) ∈ c.innerCut (αβ)} w * forestSum (αβ) (γ.shiftBy t) cs
      + α(c) * forestSum α β cs * γ.emptyVal
      + Σ_{(some t, w) ∈ c.innerCut α} w * forestSum α (β.shiftBy t) cs * γ.emptyVal
  ```
* RHS expands as
  ```
  forestSum α (Aug(βγ)) (c :: cs)
    = α(c) * forestSum α (Aug(βγ)) cs
      + Σ_{(some t, w_e) ∈ c.innerCut α} w_e * forestSum α (Aug(βγ).shiftBy t) cs
  ```
* Apply IH at `γ` to the first RHS term and `shift_agg` to each summand
  of the second:
  ```
  RHS = α(c) * (forestSum (αβ) γ cs + forestSum α β cs * γ.emptyVal)
        + Σ_{(some t, w_e) ∈ c.innerCut α} w_e * forestSum α (β.shiftBy t) cs * γ.emptyVal
        + (Σ_{(some t, w_e) ∈ c.innerCut α} w_e * β(t)) * forestSum (αβ) γ cs
        + Σ_{(some t, w_e) ∈ c.innerCut α} Σ_{(some s, w_f) ∈ t.innerCut β}
              w_e * w_f * forestSum (αβ) (γ.shiftBy s) cs
  ```
* The two non-trivial obligations to close `LHS = RHS` are:
  1. **Coefficient of `forestSum (αβ) γ cs`:**
     `(αβ)(c) = α(c) + Σ_{(some t, w) ∈ c.innerCut α} w * β(t)`.
     This holds by `bSeriesConvAug_node` plus unital `β`. (Provable.)
  2. **Coefficient of `forestSum (αβ) (γ.shiftBy s) cs`** for each
     trunk `s`:
     ```
     Σ_{(some s, w) ∈ c.innerCut (αβ)} w * F(s)
       = Σ_{(some t, w_e) ∈ c.innerCut α}
           Σ_{(some s, w_f) ∈ t.innerCut β}
              w_e * w_f * F(s)
     ```
     for any `F : BTree → ℝ`. This is a structural "cut associativity"
     identity at the level of `BTree.innerCut`.

The cut-associativity identity is the wall. For unital `β` it does
hold (verified by hand for `c = leaf`, `c = node []`, `c = node [d]`
with `d.order ≤ 1`, and `c = node [leaf, leaf]`), but the proof
mirrors the bSeries Hopf-algebra coproduct compatibility and is not a
single `simp`/`linear_combination` line.

A clean Lean proof would proceed by induction on `c`, propagating the
identity through `BTree.innerCutForest`. Each step of the induction
needs to expand `(αβ)(d)` for a child `d` of `c` and re-distribute via
`d.innerCut β` — i.e. the inductive step itself uses the identity at a
strict subtree.  Two interlocking inductions (on `c` and on the
forest structure) make this a non-trivial deliverable on its own.

## Possible solutions

1. **Bottom-up expansion:** Prove
   `cut_assoc : ∀ c, (innerCut-aggregate-(αβ) c F) = (double-aggregate-α-then-β c F)`
   by mutual induction on `c` and `BTree.innerCutForest`. Then the
   parametric `forestSum_assoc_children_order_le` is a one-shot
   application.  Estimated cost: a fresh ~300-line module of bSeries
   coproduct lemmas, plus the easy parametric headline (~80 lines).

2. **Defer parametric form, ladder by depth:** Land
   `mul_assoc_at_node_depth_three_children` this cycle (cycle 600
   fallback authorised by the strategy), then push to depth-4 etc. as
   needed. Each new depth adds ~1 head-shape per new child shape. This
   is what cycle 600 actually does.

3. **Switch to BTree-size strong induction:** Instead of bounding
   children-order, induct on `(node children).size` and use the IH
   for both the cs tail AND for the trunks. This route needs the
   universal-in-γ shape but avoids the parametric children bound; the
   `shift_agg` lemmas then close because trunks have strictly smaller
   size. Worth scoping in a future cycle.

## Pointers

* `OpenMath/ButcherGroup/Section386Aug.lean:908`
  `bSeriesConvAug_innerForest_cons` — generic cons recurrence at the
  forest level; the entry point for `forestSum_cons_general`.
* `OpenMath/ButcherGroup/Section386Aug.lean:1057`
  `forestSum_assoc_depth_one` — cycle 598 head-case template.
* `OpenMath/ButcherGroup/Section386Aug.lean:1408`
  `forestSum_assoc_depth_two` — cycle 599 head-case template.
* `OpenMath/ButcherGroup/Section386Conv.lean:43` `BTree.innerCut` —
  underlying recursive cut enumeration.
