# Cycle 268 Results

## Worked on

§310/§311 Phase E.1 — order-4 partial-sum bridge for the
exact-solution B-series.

**Five new public theorems** shipped axiom-clean
(`[propext, Classical.choice, Quot.sound]`):

P1. `OpenMath.Chapter3.Section310.RootedTree.bseriesExactTerm_bushy_scalar`
    (Section301)
P2. `OpenMath.Chapter3.Section310.RootedTree.bseriesExactTerm_mkVertexCherry_scalar`
    (Section301)
P3. `OpenMath.Chapter3.Section310.RootedTree.bseriesExactTerm_mkBroom₃_scalar`
    (Section301)
P4. `OpenMath.Chapter3.Section310.RootedTree.bseriesExactTerm_mkMkCherry_scalar`
    (Section301)
P5. `OpenMath.Chapter3.Section311.lem_311A_order_four_partialSum`
    (Section311)
P6. Non-vacuity witness `example` on `f := 0, yex := const y₀`
    (Section311)

Plus one new `def` alias `bushy : RootedTree := mk [vertex, vertex,
vertex]` at `Section310.lean` (sister to existing `vertex`, `cherry`,
`broom₃`).

## Approach

Followed the cycle 268 strategy verbatim: each per-tree scalar
closed form follows the cycle 267 recipe

> `unfold bseriesExactTerm + tree-alias` →
> `rfl`-reduce `(order, σ, γ)` from definitional reductions →
> `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` at depth `n` →
> `Fin.prod_univ_n` (`one`, `two`, or `three`) →
> `iteratedDeriv_succ` × (n−1) followed by `iteratedDeriv_one` →
> `smul_eq_mul` + `push_cast` + `ring`.

P1 (bushy) uses the cycle 267 discovery
`iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod` at depth 3 with
`Fin.prod_univ_three`; the inner `elementaryDiff f y₀ vertex = f y₀`
is established by `iteratedFDeriv_zero_apply`.

P2 (mk [vertex, cherry]) is a depth-2 outer `iteratedFDeriv` with
an inline `hED_cherry` block computing the inner `cherry` summand
via `iteratedFDeriv_one_apply` + `fderiv_eq_smul_deriv` (cycle 266
recipe).

P3 (mk [broom₃]) is a depth-1 outer of a depth-2 inner; the inner
`elementaryDiff f y₀ broom₃ = f''·f²` is computed inline via a
self-contained replay of the cycle-267 `bseriesExactTerm_broom₃_scalar`
derivation at the `elementaryDiff` level. **σ(mk [broom₃]) = 2 by
the σ-recursion `σ(mk [t]) = 1!·σ(t)^1 = σ(t)` with σ(broom₃) = 2**
— this gives the coefficient `1/(σ·γ) = 1/(2·12) = 1/24`, not
`1/12`, matching cycle 258's order-4 closed form.

P4 (mk [mk [cherry]]) is a depth-1 outer of a depth-1 inner; the
intermediate `elementaryDiff f y₀ (mk [cherry]) = (f')²·f` follows
the cycle 267 `bseriesExactTerm_mkCherry_scalar` derivation at
the `elementaryDiff` level.

P5 (`lem_311A_order_four_partialSum`) follows cycle 267's
`lem_311A_order_three_partialSum` pattern, extended to 8 trees: 7
non-membership lemmas for the iterated `Finset.insert` chain
(each one a `simp [vertex, cherry, broom₃, bushy]` on
`RootedTree.mk.injEq`), then a `hcongr` block unfolding the
partial sum to the closed-form polynomial of cycle 258's
`lem_311A_order_four` via seven `bseriesExactPartialSum_insert`
applications + one `_singleton` + the eight per-tree closed forms
(four from cycles 266–267, four from P1–P4) + `smul_eq_mul` +
`ring`. Finally `hbase.congr'` against cycle 258's order-4 base.

P6 specialises `lem_311A_order_four_partialSum` to the trivial
ODE `f ≡ 0, yex ≡ y₀`; the entire B-series collapses to `y₀`,
giving a trivially-zero residual.

## Result

**SUCCESS** — all six deliverables shipped axiom-clean. Sorry
count remains 0 across both modified files. `lake build
OpenMath.Chapter3` completes without errors or warnings on the
new symbols.

Axiom check via `#print axioms`:
```
'…bseriesExactTerm_bushy_scalar'             : [propext, Classical.choice, Quot.sound]
'…bseriesExactTerm_mkVertexCherry_scalar'    : [propext, Classical.choice, Quot.sound]
'…bseriesExactTerm_mkBroom₃_scalar'          : [propext, Classical.choice, Quot.sound]
'…bseriesExactTerm_mkMkCherry_scalar'        : [propext, Classical.choice, Quot.sound]
'…lem_311A_order_four_partialSum'            : [propext, Classical.choice, Quot.sound]
```

LOC delta (close to estimate):
* `Section310.lean` +5 LOC (bushy alias + example)
* `Section301.lean` 1080 → 1280 LOC (+200, four per-tree closed forms)
* `Section311.lean` 1611 → 1898 LOC (+287, P5 partial-sum bridge +
  P6 non-vacuity example)

Total ~492 LOC delta, slightly above the §I budget of 315 LOC due
to the verbose `OpenMath.Chapter3.Section310.RootedTree.<symbol>`
qualifications used in `Section311.lean` (Section311 cannot `open`
that namespace because of cycle-307 GLM symbol shadowing risk; the
strategy file's LOC estimate is for non-qualified naming).

## Faithfulness check

### P1 `bseriesExactTerm_bushy_scalar`

**Anchor entity**: `def:312A` (derivative weights / `Φ(t)` for
exact solution; in this project, parameterised via `def:310A`
`elementary differential` + the `1/(σ·γ)` prefactor of Butcher
§312 used in the exact-solution B-series).

**Textbook statement (extraction/formalization_data/entities/def_312A.json
`statement_latex`, abbreviated)**:

> Then the elementary weights $\Phi(t)$ … are defined by …
> $(\Phi_i D)([t_1 t_2 \cdots t_k]) = \prod_{j=1}^k \Phi_i(t_j)$ …
> $\Phi(t) = \sum_{i=1}^s b_i (\Phi_i D)(t).$

For the exact-solution form (§312, distinct from the RK-method
elementary weights), the per-tree term is `(h^r / (σ·γ)) · F(t)(y₀)`.
At `t = bushy = mk [vertex, vertex, vertex]`: `r = 4`, `σ = 6`,
`γ = 4` (all `rfl`-witnessed via existing examples at lines 373–377
of `Section301.lean`). Elementary differential is the 3rd-order
multilinear derivative `f^{(3)}(y₀)(f(y₀), f(y₀), f(y₀))`, which on
the scalar real line is `f'''(y₀)·f(y₀)³`. Coefficient
`h^4 / (σ·γ) = h^4 / 24`.

**Lean statement captures**: same content (scalar specialisation
of `def:312A` / `def:310A` evaluated at `bushy`).

### P2 `bseriesExactTerm_mkVertexCherry_scalar`

Same anchor (`def:312A` / `def:310A`). At `t = mk [vertex, cherry]`:
`r = 4`, `σ = 1`, `γ = 8` (witnessed at lines 349–353 of
`Section301.lean`). Elementary differential expands as
`f''(y₀)(f(y₀), f'(y₀)·f(y₀))` = `f''(y₀) · f'(y₀) · f(y₀)²` on
scalars. Coefficient `h^4 / 8`.

**Lean statement captures**: same content.

### P3 `bseriesExactTerm_mkBroom₃_scalar`

Same anchor. At `t = mk [broom₃]`: `r = 4`, **σ = 2**, `γ = 12`
(witnessed at lines 386–390 of `Section301.lean`).
**Faithfulness alert resolved**: σ(mk [broom₃]) = 2 by the
σ-recursion `σ(mk [t]) = 1!·σ(t)^1 = σ(t)` and σ(broom₃) = 2
(from cycle 017's σ-table on order-3 trees and `mk.injEq`
verification). Coefficient `h^4 / (2·12) = h^4 / 24`.

Elementary differential expands to `f'(y₀) · f''(y₀) · f(y₀)²` on
scalars (one outer first-derivative `f'` applied to the inner
`f''·f²` from `broom₃`).

**Lean statement captures**: same content.

### P4 `bseriesExactTerm_mkMkCherry_scalar`

Same anchor. At `t = mk [mk [cherry]]`: `r = 4`, `σ = 1`, `γ = 24`
(witnessed at lines 398–402 of `Section301.lean`). Elementary
differential expands to `(f'(y₀))³ · f(y₀)` on scalars (chain of
three first-derivatives). Coefficient `h^4 / 24`.

**Lean statement captures**: same content.

### P5 `lem_311A_order_four_partialSum`

**Anchor entity**: `lem:311A` (extraction/formalization_data/entities/lem_311A.json).

**Textbook statement (`statement_latex`)**:

> Let $S = S_0 \cup \{s\}$ … Let $t \in T_{S_0}^*$. Then
> $\frac{d}{dx} F(|t|)(y(x))$ is the sum of $F(|u|)(y(x))$ over all
> $u \in T_S^*$ such that the subtree formed by removing $s$ from
> the set of vertices is $t$.

This is the **textbook recursive structure** lemma (combinatorial
labelling over `T_S^*`); the full lemma requires `def:300C`
(labelled-tree quotient infrastructure, currently absent — see
`.prover-state/issues/lem_310B_plan.md` Phase A.2) and is multi-cycle
scope.

The cycle-268 lemma `lem_311A_order_four_partialSum` is **the
order-4 partial-sum specialisation** of `lem:311A`'s downstream
consumer, the Taylor-truncated exact-solution B-series. It bridges
cycle 258's `lem_311A_order_four` (closed-form polynomial form) and
the `bseriesExactPartialSum f y₀ h S` aggregate form for `S =
{vertex, cherry, broom₃, mk [cherry], bushy, mk [vertex, cherry],
mk [broom₃], mk [mk [cherry]]}` (all 8 trees of order ≤ 4).

**Lean statement captures**: weaker (order-4 specialisation of one
downstream form, not the full textbook combinatorial statement),
explicitly documented as "partial" in `lean_status.json`. Cycle 268
extends the cycle 267 order-3 partial-sum bridge by one more order;
the underlying recursive lemma is still future scope.

**Hypothesis strength**: matches cycle 258's `lem_311A_order_four`
verbatim (`ContDiff ℝ 3 f`, `yex x₀ = y₀`, `ContDiff ℝ 5 yex`,
`∀ x, HasDerivAt yex (f (yex x)) x`). No extra hypotheses
introduced this cycle.

**Tautology / identity / absent-theorem check**: P5 is a multi-step
`hcongr` + `IsBigO.congr'` proof against cycle 258's base, with
no `exact h`/`:= h` shortcuts; conclusion does not appear as a
hypothesis. P1–P4 are all multi-step `unfold + rw + ring`
derivations. All theorems perform substantive content (translating
between two B-series representations), not vacuous re-exports.

**Definition smuggling check**: All four `bseriesExactTerm_*_scalar`
closed forms unfold to concrete polynomial expressions in
`deriv^k f y₀` and `f y₀`; no definitional unfolding smuggled into
the statement. P5's RHS uses the well-defined `bseriesExactPartialSum`
def (cycle 266); no smuggling.

### Bookkeeping faithfulness

* `lean_status.json` `lem:311A` row updated: status `partial`,
  cycle 268, `lean_symbol` set to `lem_311A_order_four_partialSum`.
  Status remains `partial` (not `formalized`) because the full
  textbook `lem:311A` requires `def:300C` (still missing).
* `lean_status.json` `lem:310B` row unchanged: still `unformalized`
  — cycle 268 is one stepping stone in the multi-phase
  `lem_310B_plan.md` (Phase E.1, now closed up to order 4 in
  the scalar setting).

## Dead ends

None this cycle. The strategy's risk register (R1–R6) flagged six
potential issues; the actual issues encountered were:

* **Spurious `simp` warnings** on `h_mkvc_notin` and `h_mkb_notin`
  about unused `bushy` simp argument. Trivial fix — those two
  non-membership facts don't involve `bushy` on either side
  (the LHS is `mk [vertex, cherry]` or `mk [broom₃]`, neither
  needs `bushy` unfolded). Dropped from those simp calls.
* **Olean staleness propagation**: after adding `bushy` to
  `Section310.lean`, `lake env lean Section301.lean` initially
  failed with "Local variable `bushy` has no definition" because
  the `.olean` for Section310 was stale. Resolved by running
  `lake build OpenMath.Chapter3.Section310` (and later `…Section301`)
  to rebuild the cached oleans. **Lesson for future cycles**:
  when adding a symbol to a downstream-imported file (Section310),
  `lake build` that file before `lake env lean` of consumers.

## Discovery

* **`Fin.prod_univ_three`** is the natural sibling of `Fin.prod_univ_two`
  / `Fin.prod_univ_one` for the depth-3 case (bushy, P1). Lives in
  `Mathlib.Algebra.BigOperators.Fin`. The `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod`
  recipe scales mechanically to any depth via `Fin.prod_univ_n`
  + `iteratedDeriv_succ` chain.
* **σ-recursion at one-child trees**: for `t' = mk [t]` (one child),
  the σ-recursion gives `σ(mk [t]) = ∏ᵢ mᵢ! · σ(tᵢ)^{mᵢ}` = `1!·σ(t)^1
  = σ(t)`. This matters for P3 (`σ(mk [broom₃]) = σ(broom₃) = 2`,
  not 1) and is the only non-trivial σ value among the four new
  order-4 trees. The strategy's §B and §E both flagged this
  explicitly; verified independently by reading
  `Section301.lean:386–390`.
* **Iterated-`Finset.insert` non-membership pattern at scale**:
  for 8 trees and 7 non-membership lemmas, the `simp [vertex,
  cherry, broom₃, bushy]` approach with the auto-generated
  `RootedTree.mk.injEq` discharges each one in ≤ 5 LOC. Total
  non-membership scaffolding is ~75 LOC for the 7 facts. No fallback
  to per-pair `≠` lemmas needed (R3 in the risk register did not
  fire).
* **Recipe template for higher orders**: the cycle 267/268 work
  establishes a clean recipe for `bseriesExactTerm_<tree>_scalar`
  closed forms at all orders. For order N: depth-d outer
  `iteratedFDeriv ℝ d` + d inner closed forms (recursively
  expanded) + `Fin.prod_univ_d` + (d−1)-fold `iteratedDeriv_succ`.
  Cycle 269+ can apply this to the 9 trees of order 5 (or
  `lem_311A_order_five` directly).

## Suggested next approach

Per cycle 267's task-results and the cycle 268 strategy §J, the
natural cycle 269 candidates in priority order:

1. **Order-5 partial-sum bridge** using cycle 259's
   `lem_311A_order_five`. LOW risk, mechanical port of cycle 268
   at one more degree. 9 new order-5 trees: `mk [v,v,v,v]`,
   `mk [v,v,cherry]`, `mk [cherry,cherry]`, `mk [v,broom₃]`,
   `mk [v,mk [cherry]]`, `mk [broom₃,v]` (= same as `mk [v,broom₃]`
   by `List.cons` order convention — careful), `mk [mk [v,v]]` (=
   `mk [broom₃]`? no, that's order 4 — `mk [bushy]`), `mk [mk [cherry]
   plus a leaf]`, … need to enumerate 9 carefully via the Cayley
   recursion. Estimate ~400 LOC (8 new per-tree closed forms +
   one new partial-sum bridge with 13 trees total). The
   `lem_311A_order_five` closed-form coefficients `(1, 7, 4, 11, 1)`
   are already verified at HEAD.

2. **Polymorphic-`E` lift of cycle 266's `bseriesExactTerm_cherry_scalar`**
   (Phase D.1 / E.2 continuation). MEDIUM-HIGH risk per cycle 267
   task results due to the
   `ContinuousMultilinearMap.uncurry`/`.curry` plumbing for
   `iteratedFDeriv ℝ n f` viewed as an N-multilinear map. Worth
   only if the scalar order-≤4 partial-sum bridge work has
   compounded enough infrastructure to make the lift mechanical.

3. **Pivot to `lem:342A` (Legendre orthogonality on `[0,1]`)** —
   single-cycle independent target per `lem_310B_plan.md` §8.2.
   Detaches from the §310/§311 Phase E.* ladder and exercises a
   different chunk of `Mathlib.Analysis.SpecialFunctions.OrthogonalPolynomials`.

Recommend Option 1 (order-5 partial-sum bridge) for cycle 269.
The mechanical recipe is now well-established, and pushing to
order 5 means Phase E.1 is closed at the same order as
`lem_311A_order_five` itself — a clean stopping point that
matches the deliberate order-5 cutoff in `lem_311A_order_*` per
cycle 259's task results. Beyond order 5, the substantive §311
content needs the labelled-tree quotient `def:300C` (Phase A.2
of `lem_310B_plan.md`), so Option 1 is the highest-momentum
single-cycle deliverable.
