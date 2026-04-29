# Cycle 572 Results

## Worked on
- Step 1: `bSeriesConv_congr_of_le` locality lemma in
  `OpenMath/ButcherGroup/Section386Conv.lean`
- Step 2: unrestricted `IsG1Equiv.product_congr` in
  `OpenMath/ButcherGroup.lean`
- Step 3: `G1.mul`, `G1.mul_mk`, `G1.bSeriesHomAt_mul_mk`
- Step 4 (bonus): `G1.one_mul`, `G1.mul_one`

## Approach

### Step 1 — `bSeriesConv_congr_of_le`
Direct mutual induction on `BTree` via `BTree.rec` with `motive_2`:
- `innerCut_eq_of_agree` — α-locality of the inner-cut list.
- `innerCutForest` agreement on subtrees of order ≤ p.
- `innerCut_trunk_order_le α τ c hc t ht` — every trunk
  appearing in `innerCut τ` has order ≤ τ.order. This is
  the structural fact that forces β-locality to suffice.
- `sum_filterMap_β_eq_of_agree` — given α-agreement-shaped lists
  and β agreement on the trunks, the `filterMap` β-weighted sum
  is invariant.
- Headline: combine the three.

`α` is treated as a fixed *outer parameter* in the recursion
to dodge Lean's auto-introduction of motive_2 hypotheses as
anonymous binders. Used `rename_i` for the cons case as a
fallback.

### Step 2 — `IsG1Equiv.product_congr`
With the locality lemma available, the proof is now a clean
4-fold `Quotient.inductionOn` (q, q', r, r' all reduced to
representatives), then:
1. `show (ButcherProduct t₁ t₂).bSeries τ = ...`
2. `rw [ButcherProduct.bSeriesConv_consistency, ...]`
3. `rw [hα τ hτ, ButcherTableau.bSeriesConv_congr_of_le hα hβ hτ]`

`hα`/`hβ` are derived from `hq`/`hr` via the
`bSeriesHom = bSeries` definitional reduction on
`QuotEquiv.mk`-class representatives.

Note: had to use the fully qualified
`ButcherTableau.bSeriesConv_congr_of_le` because
the unqualified name didn't resolve from inside
`ButcherTableau.IsG1Equiv` (Lean caching artefact —
worked after `lake build OpenMath.ButcherGroup.Section386Conv`).

### Step 3 — `G1.mul` + sugar
- `G1.mul := Quotient.lift₂ (mk ∘ product) (by exact IsG1Equiv.product_congr)`
- `G1.mul_mk` is `rfl`.
- `G1.bSeriesHomAt_mul_mk` (representative-level): closes via
  one application of `ButcherProduct.bSeriesConv_consistency`
  after `Quotient.inductionOn` at the inner stage representatives.

### Step 4 — identity laws
- `one_mul` and `mul_one` follow from
  `QuotEquiv.product_bSeries_one_left` /
  `QuotEquiv.product_bSeries_one_right` already on file.
  The proof: `Quotient.inductionOn`, unfold `one`, `mul_mk`,
  `Quotient.sound`, then the existing one-side product lemma.

## Result

**SUCCESS for all four steps.**

- `lake env lean OpenMath/ButcherGroup/Section386Conv.lean` — clean.
- `lake env lean OpenMath/ButcherGroup.lean` — clean.
- `lake build` — full build succeeds (only pre-existing lints elsewhere).

New declarations landed:
- `ButcherTableau.bSeriesConv_congr_of_le`
- `ButcherTableau.IsG1Equiv.product_congr`
- `ButcherTableau.G1.mul`
- `ButcherTableau.G1.mul_mk`
- `ButcherTableau.G1.bSeriesHomAt_mul_mk`
- `ButcherTableau.G1.one_mul`
- `ButcherTableau.G1.mul_one`

## Dead ends

- Tried `refine Quotient.inductionOn ...` for `product_congr`
  in early drafts — fails because the hypothesis `hq` is not
  generalized along with the goal, so the resulting hypothesis
  type after substitution doesn't match. Switched to
  `induction q using Quotient.inductionOn with | _ t₁ =>` form,
  which generalizes/specializes hypotheses cleanly.
- Initial draft of `bSeriesHomAt_mul` had `if-then-else` dressing
  for the lifted convolution coefficients. Replaced with the
  cleaner `bSeriesHomAt_mul_mk` representative-level form, which
  is what downstream G1 group-axiom lemmas will actually use.
- `(Quotient.mk _ trivialTableau).product q` doesn't elaborate
  with dot notation because Lean can't infer the QuotEquiv stage
  from the bare `Quot.mk`. Wrote `QuotEquiv.product (Quotient.mk _ trivialTableau) q`
  in the `show` clause.

## Discovery

- The locality lemma is *the* structural ingredient: with it,
  the §387 group multiplication descends to `G1 p` with no
  shape restriction on `τ`, and any future `mul_assoc` /
  `mul_inv` proof goes through the same locality channel.
- The motive_2 quirk in `BTree.rec` (auto-introducing list
  hypotheses as anonymous binders) is best handled by lifting
  list-independent parameters out of the motive, OR using
  `rename_i` once `intro` runs out of binders.
- `lake env lean <file>` does not refresh the `.olean` cache;
  if a downstream file complains about an "Unknown constant"
  in an upstream file you just edited, run
  `lake build <upstream-module>` to actually persist the .olean.

## Suggested next approach

`G1` is now a monoid up to `mul_assoc` and possibly inverses.
Natural cycle 573 targets:

1. **`G1.mul_assoc`**: lift `QuotEquiv.product_bSeries_assoc`
   through the `G1` quotient. Should be straightforward — three
   `Quotient.inductionOn`s plus the existing associativity.

2. **`G1.bSeriesHomAt` is multiplicative** in the sense that
   it sends `mul` to the admissible-cut convolution operation
   on `BTree → ℝ`. Promote `bSeriesHomAt_mul_mk` to a
   quotient-level statement (without `mk`) — useful for
   downstream §387 group-theoretic statements.

3. **Inverses on `G1(p)`**: the textbook §387 inverse exists
   only on the subgroup of "RK-like" elements with `weightsSum = 1`
   (i.e., `bSeriesHom BTree.leaf = 1`). Probably needs a separate
   subtype or a partial inverse construction.

4. **Group instance**: with `mul_assoc`, `one_mul`, `mul_one` in
   place, install `Monoid (G1 p)` and confirm the group axiom for
   the unit-stage subset. This is the §387 finale.
