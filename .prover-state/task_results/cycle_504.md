# Cycle 504 Results

## Worked on

Butcher §386 list-split infrastructure for the §384 quotient-facing
convolution product (the recursive Butcher product on tree-indexed
coefficients), plus the placeholder symbol `QuotEquiv.bSeriesConv` that
the cycle-505+ body will fill in. All work in
`OpenMath/ButcherGroup.lean`.

## Approach

Followed the strategy: install the prerequisite list-split lemmas
sorry-free, add the second-block node-case unfolding for
`ButcherProduct.elementaryWeight`, and only leave the headline `bSeriesConv`
definition body as `sorry` (the active target's allowed tracked sorry).

Mathlib search showed `Fin.prod_univ_fun_getElem`
(`∏ i : Fin l.length, f l[i.1] = (l.map f).prod`) and `Finset.prod_add`
(`∏ i ∈ s, (f i + g i) = ∑ t ∈ s.powerset, (∏ i ∈ t, f i) * (∏ i ∈ s \ t, g i)`).
Composing those two lets the list-fold `xs.foldr (· * (x · + y ·)) 1`
land directly as a sum-over-subsets of `Fin xs.length`-positions.

For the second-block node-case unfolding of
`(ButcherProduct t₁ t₂).elementaryWeight (.node τs) (Fin.natAdd s i)`,
the inner sum splits via `Fin.sum_univ_add` into a first-block sum
(weight `t₁.b k₁`) plus a second-block sum (weight `t₂.A i k₂`); two new
simp lemmas (`butcherProduct_A_natAdd_castAdd` /
`butcherProduct_A_natAdd_natAdd`) collapse the addCases A-blocks, then
`List.foldr` induction propagates the per-child sum through the children
list.

## Result

SUCCESS. Landed sorry-free declarations:

- `ButcherGroup.foldr_mul_add_eq_prod`
- `ButcherGroup.foldr_mul_add_eq_sum_powerset`
- `ButcherGroup.prod_add_finset_indexed`
- `butcherProduct_A_natAdd_castAdd`
- `butcherProduct_A_natAdd_natAdd`
- `ButcherProduct.innerSum_natAdd_split`
- `ButcherProduct.elementaryWeight_node_natAdd`

Plus the single tracked `sorry`:

- `QuotEquiv.bSeriesConv` (placeholder body, intentional, allowed by the
  active-target rule).

Verification:

- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/ButcherGroup.lean`
  succeeds with the single expected `declaration uses 'sorry'` warning.
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build` succeeds.
- `rg -n "sorry|admit" OpenMath/ButcherGroup.lean` returns one match
  (line 986, the `bSeriesConv` placeholder).

Updated `plan.md` (§386 status, Current Target follow-up note),
`.prover-state/issues/butcher_section384_convolution.md` (recorded the
landed list-split infrastructure and updated possible-solutions section
2 to `DONE — cycle 504`).

## Aristotle results used

None this cycle. Each of the strategy's listed Aristotle targets
(`foldr_mul_add_eq_sum_sublists`, the Finset-powerset variant, the
node-case unfolding, the bridge factor lemma) closed cleanly via
manual proofs once the right Mathlib lemmas were located. No new
Aristotle scaffolds were submitted — the only sorry remaining is the
intentional `bSeriesConv` placeholder, whose body is explicitly deferred
to cycle 505+ per strategy.

## Mathlib lemmas reused

For cycle 505 to find quickly:

- `Fin.prod_univ_fun_getElem` — `∏ i : Fin l.length, f l[i.1] = (l.map f).prod`.
  In `Mathlib.Algebra.BigOperators.Fin`.
- `Finset.prod_add` — `∏ i ∈ s, (f i + g i) = ∑ t ∈ s.powerset, (∏ i ∈ t, f i) * (∏ i ∈ s \ t, g i)`.
- `Fin.sum_univ_add` — splits a sum over `Fin (m + n)` into a sum over
  `Fin m` (via `Fin.castAdd n`) plus a sum over `Fin n` (via `Fin.natAdd m`).

## Dead ends

- `change` and `show` failed to unfold
  `(ButcherProduct t₁ t₂).elementaryWeight (.node τs) (Fin.natAdd s i)`
  to its `List.foldr` form by definition (well-founded recursion blocks
  defeq). Worked around by an explicit `rw [show … from by simp [ButcherTableau.elementaryWeight]]`.
- `List.foldr_congr` does not exist in this Mathlib snapshot. Replaced
  with explicit `List.recOn`-style induction on the children list,
  applying `ButcherProduct.innerSum_natAdd_split` per cons cell.
- `rfl` on the foldr unfolding fails because `elementaryWeight` is
  defined with `termination_by` and is not reducible.

## Discovery

The §386 node-case unfolding statement is *exactly* the
`x child + y child` shape that `foldr_mul_add_eq_sum_powerset` consumes,
with `x child = ∑ k₁ : Fin s, t₁.b k₁ *
(ButcherProduct t₁ t₂).elementaryWeight child (Fin.castAdd t k₁)` and
`y child = ∑ k₂ : Fin t, t₂.A i k₂ *
(ButcherProduct t₁ t₂).elementaryWeight child (Fin.natAdd s k₂)`. So the
recursive product body for `bSeriesConv` at a `node τs` is essentially
mechanical once the two per-child contributions are named.

The first-block stage (`Fin.castAdd t i₁`) is symmetric: the lower-right
block of `(ButcherProduct t₁ t₂).A` at a first-block row is `0`, so the
inner sum collapses to the first-block-only term. A matching
`elementaryWeight_node_castAdd` lemma is the analogous one-line cycle-505+
helper.

## Suggested next approach (cycle 505)

1. Add `butcherProduct_A_castAdd_castAdd = t₁.A i j` and the zero
   simp lemma `butcherProduct_A_castAdd_natAdd = 0` to mirror the
   second-block unfolding.
2. Add `ButcherProduct.elementaryWeight_node_castAdd` (first-block stage):
   `(ButcherProduct t₁ t₂).elementaryWeight (.node τs) (Fin.castAdd t i)
       = τs.foldr (fun child acc => acc *
           ∑ k : Fin s, t₁.A i k *
             (ButcherProduct t₁ t₂).elementaryWeight child (Fin.castAdd t k)) 1`.
3. Define `QuotEquiv.bSeriesConv` recursively: at `leaf`, return a closed
   form; at `node τs`, use
   `ButcherGroup.foldr_mul_add_eq_sum_powerset` with `x` and `y` set
   to the two per-child contributions of `t₂`. Two style choices:
   either fold over `BTree.rec` on a `noncomputable def` lifted from the
   raw representative, or define directly on `BTree` and prove well-typed
   on `QuotEquiv` via lift.
4. Then prove `QuotEquiv.bSeriesHom_product`:
   `bSeriesHom (product q₁ q₂) τ = bSeriesConv q₁.bSeriesHom q₂.bSeriesHom τ`.
   The proof should use `Quotient.inductionOn₂`, then split the outer
   `b`-weighted sum over `Fin (s + t)` via `Fin.sum_univ_add`. The
   first-block half collapses by the cycle-503 identity prep lemmas; the
   second-block half uses the node-case unfolding from cycle 504 plus
   the `bSeriesConv` recursion.
