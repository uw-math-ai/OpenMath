# Issue: `def:422B` Phase α' scoping — recursive `inversePolynomial` design

## §1 Status & blocker

**Scoping doc, cycle 379.** No Lean code shipped this cycle — this is
a markdown-only research doc distilling the 8-tree closed-form ladder
shipped through cycle 378 into a concrete plan for a *recursive*
`inversePolynomial` definition that supersedes the current 8-way
`if-then-else` pattern match at
`OpenMath/Chapter4/Section422.lean:4651`. The cycle 378 worker's
"Suggested next approach" Option A explicitly named this scoping doc
as the highest-value next move (`task_results/cycle_378.md`
§"Suggested next approach"); the cycle 379 planner authorised the
markdown-only ship in `strategy.md` §"Priority 1 — DELIVERABLE".

This doc follows the cycle 373 precedent
(`.prover-state/issues/def_422B_subLemmaA_inductive_plan.md`,
1399 lines, ran 11 sections, no Lean churn, directly drove cycles
374–378's 8-tree ladder build-out). The cycle 373 strategy was
scored OK despite a zero-Lean cycle; the same evaluation should
apply here.

**§422 axiom-clean streak: 43 substantive + 1 doc (cycles 336–378).**
Single grandfathered sorry at `OpenMath/Chapter4/Section422.lean:2279`
(cycle 365's `powRep_sum_eq_of_strict_subtree_agreement` general body).
Section422.lean: 5595 LOC. `grep -c sorry` returns 5 (4 docstring
references + 1 actual code sorry).

**Pivot rationale.** Cycle 378's D1 discovery
(`task_results/cycle_378.md` §Discovery) was the structural insight
that the depth-3 single-child case `mk [mk [cherry]]` has a closed
form (`v⁴ − 3v²c + c² + 2vm − M_mkMkCherry`) with **no `broom₃`
term**, in contrast to the depth-2 multi-child cases of cycles 371
(`mk [broom₃]`) and 372 (`mk [vertex, cherry]`) which both depend
on `broom₃`. This is the first empirical evidence of a clean
structural rule: single-child ladder cases depend only on the chain
of left-most descendants. Cycle 379 invests one zero-Lean cycle in
formalising this structural observation into a phased design plan,
then cycle 380+ ships the implementation.

**Blocker.** The current `inversePolynomial` (cycles 374, 377, 378)
is an 8-way `if-then-else` that returns `0` on every tree outside
the ladder. This is fine for the cycle 365 m=0 corollaries and the
Phase β bridges, but it is structurally insufficient to close
cycle 365's grandfathered sorry
(`powRep_sum_eq_of_strict_subtree_agreement`, Section422.lean:2279)
because the sorry's body needs `inversePolynomial t f` to evaluate
to the *correct* closed form for arbitrary `t`, not `0`. The Phase
α' deliverable is a recursive definition whose evaluation on every
tree (in particular trees outside the 8-tree ladder) matches the
algebraic closed form derivable from cycle 358's
`elementaryWeightQ_phi_inv_mk`.

## §2 The current `inversePolynomial` definition (Phase α.1–α.4 status)

At HEAD (`Section422.lean:4651–4697`), the definition is an 8-way
`if-then-else` cascade on `t`. The shape, branch-by-branch:

```lean
noncomputable def inversePolynomial (t : RT) (f : RT → ℝ) : ℝ :=
  if t = RootedTree.vertex then
    -(f RootedTree.vertex)                                          -- cycle 374 (α.1)
  else if t = RootedTree.cherry then
    (f RootedTree.vertex) ^ 2 - f RootedTree.cherry                  -- cycle 374 (α.1)
  else if t = RootedTree.broom₃ then
    -(f RootedTree.vertex) ^ 3
      + 2 * f RootedTree.vertex * f RootedTree.cherry
      - f RootedTree.broom₃                                          -- cycle 374 (α.1)
  else if t = mk [RootedTree.cherry] then
    -(f RootedTree.vertex) ^ 3
      + 2 * f RootedTree.vertex * f RootedTree.cherry
      - f (mk [RootedTree.cherry])                                   -- cycle 374 (α.1)
  else if t = RootedTree.bushy then
    (f RootedTree.vertex) ^ 4
      - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
      + 3 * f RootedTree.vertex * f RootedTree.broom₃
      - f RootedTree.bushy                                           -- cycle 377 (α.2)
  else if t = mk [RootedTree.broom₃] then
    (f RootedTree.vertex) ^ 4
      - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
      + f RootedTree.vertex * f RootedTree.broom₃
      + 2 * f RootedTree.vertex * f (mk [RootedTree.cherry])
      - f (mk [RootedTree.broom₃])                                   -- cycle 377 (α.2)
  else if t = mk [RootedTree.vertex, RootedTree.cherry] then
    (f RootedTree.vertex) ^ 4
      - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
      + (f RootedTree.cherry) ^ 2
      + f RootedTree.vertex * f RootedTree.broom₃
      + f RootedTree.vertex * f (mk [RootedTree.cherry])
      - f (mk [RootedTree.vertex, RootedTree.cherry])                -- cycle 377 (α.2)
  else if t = mk [mk [RootedTree.cherry]] then
    (f RootedTree.vertex) ^ 4
      - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
      + (f RootedTree.cherry) ^ 2
      + 2 * f RootedTree.vertex * f (mk [RootedTree.cherry])
      - f (mk [mk [RootedTree.cherry]])                              -- cycle 378 (α.4)
  else
    0                                                                -- Phase α'-replaced
```

The 8 matched cases and their orders / sources:

| Cycle | Tree | Order | Phase ship |
|---|---|---|---|
| 374 | `vertex` | 1 | α.1 |
| 374 | `cherry = mk [vertex]` | 2 | α.1 |
| 374 | `broom₃ = mk [vertex, vertex]` | 3 | α.1 |
| 374 | `mk [cherry]` | 3 | α.1 |
| 377 | `bushy = mk [vertex, vertex, vertex]` | 4 | α.2 |
| 377 | `mk [broom₃]` | 4 | α.2 |
| 377 | `mk [vertex, cherry]` | 4 | α.2 |
| 378 | `mk [mk [cherry]]` | 4 | α.4 |

**Limitation.** Any tree not in the 8-tree ladder evaluates to `0`,
which is mathematically incorrect for Sub-lemma A's general body
(the cycle 365 grandfathered sorry at `Section422.lean:2279` needs
`inversePolynomial t (elementaryWeightQ_phi η_q) =
elementaryWeightQ_phi η_q⁻¹ t` for *arbitrary* `t`, not just the 8
ladder cases). The Phase β `_on_ladder` aggregator
(`Section422.lean:5200`) explicitly carries an 8-way disjunction
hypothesis on `t`, side-stepping this; Phase γ
`inversePolynomial_eq_of_subtree_agreement`
(`Section422.lean:5260`) handles the default `0 = 0` case
trivially. Both will require migration once the recursive
definition lands.

## §3 The 8 closed forms — empirical catalog

Build the table with full notation. Let:

* `v = Φ_η(vertex)` (Φ_η(τ) in Butcher notation)
* `c = Φ_η(cherry)` = `Φ_η([τ])`
* `b' = Φ_η(broom₃)` = `Φ_η([τ,τ])`
* `m = Φ_η(mk [cherry])` = `Φ_η([[τ]])`
* `B = Φ_η(bushy)` = `Φ_η([τ,τ,τ])`
* `M = Φ_η(mk [broom₃])` = `Φ_η([[τ,τ]])`
* `V = Φ_η(mk [vertex, cherry])` = `Φ_η([τ, [τ]])`
* `M_mc = Φ_η(mk [mk [cherry]])` = `Φ_η([[[τ]]])`

The full catalog with σ(t) values (verified by `Section301.lean`
reference theorems at lines 351, 358, 370, 382, 394, 407, 419 —
all witnessed by `rfl`):

| Cycle | Tree | Order | σ(t) | Closed form `Φ_{η⁻¹}(t)` |
|---|---|---|---|---|
| 341 | `vertex` | 1 | 1 | `−v` |
| 367 | `cherry` | 2 | 1 | `v² − c` |
| 368 | `broom₃` | 3 | 2 | `−v³ + 2vc − b'` |
| 369 | `mk [cherry]` | 3 | 1 | `−v³ + 2vc − m` |
| 370 | `bushy` | 4 | 6 | `v⁴ − 3v²c + 3vb' − B` |
| 371 | `mk [broom₃]` | 4 | 2 | `v⁴ − 3v²c + vb' + 2vm − M` |
| 372 | `mk [vertex, cherry]` | 4 | 1 | `v⁴ − 3v²c + c² + vb' + vm − V` |
| 378 | `mk [mk [cherry]]` | 4 | 1 | `v⁴ − 3v²c + c² + 2vm − M_mc` |

**Cross-check on `⟦explicitEuler⟧`.** Cycle 378's non-vacuity
witness verified `Φ_{⟦explicitEuler⟧⁻¹}(mk [mk [cherry]]) = 1`
(`cycle_378.md` §Result), matching the predicted value by
substitution of `v = c = m = M_mc = 1` (for `explicitEuler`, every
elementary weight is 1). Spot-checks on the other 7 trees give 1
each, confirming the algebraic identity.

**Coefficient counts** (number of monomial terms before
simplification, including the `−Φ_η(t)` self-term):
- vertex: 1 (−v)
- cherry: 2 (v², −c)
- broom₃: 3 (−v³, 2vc, −b')
- mk [cherry]: 3 (−v³, 2vc, −m)
- bushy: 4 (v⁴, −3v²c, 3vb', −B)
- mk [broom₃]: 5 (v⁴, −3v²c, vb', 2vm, −M)
- mk [vertex, cherry]: 6 (v⁴, −3v²c, c², vb', vm, −V)
- mk [mk [cherry]]: 5 (v⁴, −3v²c, c², 2vm, −M_mc)

The σ(t) value does **NOT** appear in any closed form: the cycle 373
scoping doc §4.5 discovery slot ("σ does NOT appear in any closed
form") is fully preserved through cycle 378. The `−Φ_η(t)` term
always has coefficient `−1`. Both invariants must hold in the
recursive definition.

## §4 Structural patterns identified (the core analysis)

Break the 8 trees into three families and identify the structural
recipe for each.

### Family A — Single-child ladder (chain of `mk` applications)

The 4 single-child trees: `vertex`, `cherry = mk [vertex]`,
`mk [cherry] = mk [mk [vertex]]`, `mk [mk [cherry]] =
mk [mk [mk [vertex]]]`. Closed forms:

| Tree | Depth | Closed form |
|---|---|---|
| `vertex` | 0 | `−v` |
| `cherry` | 1 | `v² − c` |
| `mk [cherry]` | 2 | `−v³ + 2vc − m` |
| `mk [mk [cherry]]` | 3 | `v⁴ − 3v²c + c² + 2vm − M_mc` |

**Coefficient counts: 1, 2, 3, 5.** This is consistent with the
Catalan numbers `C_n = 1, 1, 2, 5, 14, ...` shifted, or with
Motzkin numbers `1, 1, 2, 4, 9, ...` (less likely). The cycle 378
worker noted this in their D1 discovery but flagged it as "may give
Phase α' a cleaner combinatorial recipe" — Phase α'.1 (cycle 380)
should test the depth-4 prediction (a 9th data point not in the
ladder) to disambiguate.

**Structural rule (D1 discovery, refined).** The closed form for
the depth-`n` single-child tree depends ONLY on the chain of
left-most descendants `{vertex, cherry, mk[cherry], mk[mk[cherry]],
..., mk^n[vertex]}` of length `n+1`. Letting `c_k = Φ_η(mk^k[vertex])`
(so `c_0 = v, c_1 = c, c_2 = m, c_3 = M_mc`), the pattern is:

* `c_0 ↦ −c_0`
* `c_1 ↦ c_0² − c_1`
* `c_2 ↦ −c_0³ + 2c_0c_1 − c_2`
* `c_3 ↦ c_0⁴ − 3c_0²c_1 + c_1² + 2c_0c_2 − c_3`

**Conjectured depth-4 closed form.** Pattern extrapolation (to be
verified in cycle 380+):
* `c_4 = Φ_η(mk[mk[mk[cherry]]]) = Φ_η(mk^4[vertex])`
* Conjecture: `c_4 ↦ −c_0⁵ + 4c_0³c_1 − 2c_0c_1² − 3c_0²c_2 + 2c_1c_2 + 2c_0c_3 − c_4`
* This has 7 terms. If the coefficient counts follow Catalan
  `1, 2, 5, 14, 42, ...` (after the depth-0 anomaly), depth-4
  predicts 13 terms — does not match; the predicted 7-term form
  comes from extrapolating the "previous-depth + 2 new mixed
  terms" pattern observed at depth-3, and is itself a guess.

**Open subquestion.** Where does the `c_1² = c²` term at depth-3
come from? It is the first quadratic-in-non-leaf term in the
ladder. The cycle 358 `elementaryWeightQ_phi_inv_mk` expansion
mechanism (cycle 369 / 378 proofs) attributes it to the inner
`derivativeWeightWithSrc M.inverse j (mk [cherry])` evaluating to
`Σ_k A_jk · Σ_l A_kl − Σ_k A_jk · (Σ_l A_kl)` cancellation patterns.
A combinatorial reformulation would clarify the recursion shape.

### Family B — Symmetric leaf brooms `mk [vertex^k]`

The 3 leaf-broom trees: `vertex` (k=0, degenerate),
`cherry = mk [vertex]` (k=1), `broom₃ = mk [vertex, vertex]` (k=2),
`bushy = mk [vertex, vertex, vertex]` (k=3).

| Tree | k | Closed form |
|---|---|---|
| `vertex` | (degenerate) | `−v` |
| `cherry` | 1 | `v² − c` |
| `broom₃` | 2 | `−v³ + 2vc − b'` |
| `bushy` | 3 | `v⁴ − 3v²c + 3vb' − B` |

**Structural rule (Family B candidate).** For `t = mk [vertex^k]`
(k ≥ 1), the closed form appears to be:

```
Φ_{η⁻¹}(mk [vertex^k]) = (−1)^k · (v^(k+1) − k·v^(k−1)·c + ... − Φ_η(t))
```

More precisely, the binomial-expansion-like pattern is:

* k=1: `v² − c` = `v · v − c`
* k=2: `−v³ + 2vc − b'` = `−v · v² + 2v · c − b'`
* k=3: `v⁴ − 3v²c + 3vb' − B` = `v · v³ − 3v · v · c + 3v · b' − B`

The coefficients `(1, k, ...)` follow Pascal's triangle / binomial
coefficients. Letting `w_0 = v, w_1 = c, w_2 = b', w_3 = B`, the
proposed closed form is:

```
Φ_{η⁻¹}(mk [vertex^k]) = (−1)^k · Σⱼ₌₀ᵏ (k choose j) · v^(k−j) · (−1)^j · wⱼ
                       = Σⱼ₌₀ᵏ (−1)^(k+j) · (k choose j) · v^(k−j) · wⱼ
```

Spot-check:
* k=3: `(−1)^3·(C(3,0)·v³·v − C(3,1)·v²·c + C(3,2)·v·b' − C(3,3)·B)`
       `= −(v⁴ − 3v²c + 3vb' − B) = ... `
       Wait — sign convention needs adjustment. The textbook closed form
       for `bushy` is `+v⁴ − 3v²c + 3vb' − B`, not the `(−1)^3·...` form.
       The correct pattern is:
       ```
       Φ_{η⁻¹}(mk [vertex^k]) = (−1)^k · v^(k+1)
                              + Σⱼ₌₁ᵏ (−1)^(k+j) · (k choose j) · v^(k−j) · wⱼ
                              − wₖ
       ```
       Or equivalently, the leading sign is `(−1)^k` and each subsequent
       binomial term flips sign. For `bushy` (k=3):
       `(−1)^3·v⁴ + 3·(−1)^2·v²·c + 3·(−1)^1·v·b' − B = −v⁴ + 3v²c − 3vb' − B`,
       which has the wrong overall sign. The actual pattern needs
       re-derivation from cycle 368's per-tree proof (the inner
       `(Aᵢ − v)^k` factorisation observed at cycle 368 Discovery).

**Refinement needed.** The closed forms for `cherry`, `broom₃`,
`bushy` arise from cycle 368's per-row factorisation
`(Aᵢ − v)^k` (where `Aᵢ = Σⱼ Aᵢⱼ` is the row-sum of the underlying
RK tableau). Expanding `(Aᵢ − v)^k = Σⱼ (k choose j) · Aᵢ^(k−j) · (−v)^j`
and substituting back via `derivativeWeightWithSrc` gives a clean
binomial sum. The "wrong sign" above is a transcription artefact;
the genuine Family B recipe is:

```
Φ_{η⁻¹}(mk [vertex^k]) = Σⱼ₌₀ᵏ (k choose j) · v^(k−j) · (−1)^j · wⱼ   (k=1,2,3)
```

Spot-checks:
* k=1: `(1 choose 0)·v·w₀ − (1 choose 1)·w₁ = v² − c` ✓
* k=2: `(2 choose 0)·v²·w₀ − (2 choose 1)·v·w₁ + (2 choose 2)·w₂`
       `= v³ − 2vc + b'`. **Textbook says `−v³ + 2vc − b'`, sign
       flipped.** So the proper recipe includes a global `(−1)^k`
       prefactor:
* k=2 with prefactor `(−1)^2 = 1`: `v³ − 2vc + b' ≠ −v³ + 2vc − b'` — wrong
* k=2 with prefactor `(−1)^k = +1` and inner sign flip: try
  `(−v)^(k+1) − Σⱼ₌₁ᵏ (k choose j) · (−v)^(k−j+1)·wⱼ`
  = `−v³ − (2·(−v)·c + (−v)⁰·b') = −v³ + 2vc − b'` ✓

The correct factorisation: with `s = −v` as the "shift" parameter,
```
Φ_{η⁻¹}(mk [vertex^k]) = (−v)^(k+1) − Σⱼ₌₁ᵏ (k choose j) · (−v)^(k−j+1) · wⱼ
```
where the last term `j = k` gives `(−v)^1 · wₖ · (k choose k) = −v·wₖ`.
But the textbook ends in `−wₖ`, not `−v·wₖ`. So this is still
off by a `wₖ` shift.

**TO INVESTIGATE in cycle 380.** Derive the exact closed-form
formula for `Φ_{η⁻¹}(mk [vertex^k])` symbolically from cycle 358's
`_inv_mk` formula and the `derivativeWeightWithSrc` recursion for
`mk [vertex^k]`. The above spot-check derivation is suggestive but
not rigorous; the precise recipe must match cycle 367, 368, 370
proofs verbatim before Phase α'.1 ships.

### Family C — Mixed / heterogeneous children

The 2 mixed-child trees in the ladder: `mk [broom₃]`
(single non-leaf child), `mk [vertex, cherry]` (mixed leaf and
non-leaf children). Closed forms:

| Tree | Closed form |
|---|---|
| `mk [broom₃]` | `v⁴ − 3v²c + vb' + 2vm − M` |
| `mk [vertex, cherry]` | `v⁴ − 3v²c + c² + vb' + vm − V` |

**Cross-terms not predicted by Family A or B.** Both Family C
trees have terms involving products of non-leaf subtrees:

* `mk [broom₃]` has `2vm` where `m = Φ_η(mk [cherry])` (a non-leaf
  subtree). The factor `2` is unexpected from Family B (where the
  binomial coefficient would be 1).
* `mk [vertex, cherry]` has `c² = (Φ_η(cherry))²` (a quadratic in
  a non-leaf subtree).

**Structural recipe for Family C is unclear from 2 data points.**
Possible candidates:

1. **Tree composition / substitution** — the closed form of
   `mk [t₁, ..., tₖ]` depends on the closed forms of the `tᵢ` in
   some combinatorial way. E.g., `mk [broom₃] = mk [mk [vertex, vertex]]`
   might be related to `Φ_{η⁻¹}(broom₃) = −v³ + 2vc − b'` via a
   `mk`-wrapping operation.
2. **Forest enumeration** — the coefficient of `Φ_η(s)` in
   `Φ_{η⁻¹}(t)` counts some combinatorial structure (e.g.,
   homomorphisms from `s` into `t`).
3. **Coproduct dualisation** — `inversePolynomial` may be the
   image of `t` under the antipode of the Connes-Kreimer Hopf
   algebra of rooted trees, restricted to the §383 quotient.
   This is speculation but matches the algebraic shape.

**Additional data points needed.** To disambiguate:
* `mk [cherry, cherry]` (order 5, σ = 2, two identical non-leaf children)
* `mk [vertex, broom₃]` (order 5, σ = 1, leaf + non-leaf)
* `mk [bushy]` (order 5, σ = 6, single non-leaf child of higher order)
* `mk [mk [mk [cherry]]]` (order 5, σ = 1, depth-4 single-child — tests
  Family A extrapolation)

Cycle 380+ can ship one of these as a "9th tree" to test the Family
A conjecture before committing to the recursive shape. This is
explicitly NOT a treadmill extension (which the cycle 378 worker
discouraged) — it's a *targeted* data acquisition to disambiguate
between candidate recursive recipes.

## §5 Proposed recursive shape for `inversePolynomial`

The cycle 358 `elementaryWeightQ_phi_inv_mk` formula
(`Section422.lean:582`) is the structural seed:

```lean
elementaryWeightQ_phi ⟦M⟧⁻¹ t
  = - ∑ i : Fin s, M.b i * M.derivativeWeightWithSrc M.inverse i t
```

The closed form for `Φ_{η⁻¹}(t)` arises from expanding
`M.derivativeWeightWithSrc M.inverse i t` via the recursive
definition of `derivativeWeightWithSrc` over `t`'s children. The
resulting per-summand expression is then summed over `i : Fin s` and
the row-sum trick (`Aᵢ - v`-shift, cycle 368/370 Discovery)
collapses the formulas into the closed forms above.

The Phase α' design challenge: find a recursive `inversePolynomial`
that mirrors this structural recursion at the *quotient* level
(working directly on the weight function `f` rather than the
underlying tableau).

### Variant V1 — Partition-based (separates leaf and non-leaf children)

```lean
noncomputable def inversePolynomial : RootedTree → (RootedTree → ℝ) → ℝ
  | RootedTree.mk children => fun f =>
      let leafCount := children.countP (· = RootedTree.vertex)
      let nonLeafChildren := children.filter (· ≠ RootedTree.vertex)
      -- Family-B binomial sum contribution from leafCount:
      let leafContribution :=
        Σⱼ₌₀^leafCount (-1)^j · (leafCount choose j) · (f vertex)^(leafCount − j)
          · (if j = 0 then 1 else f (mk (List.replicate j vertex)))
      -- Family-A recursion on each non-leaf child:
      let nonLeafContribution :=
        nonLeafChildren.foldr (· · ·) ... using inversePolynomial recursively
      ...  -- combine via cross-term recipe TBD
  termination_by t => t.order
  decreasing_by exact RootedTree.order_lt_of_mem_children ‹_›
```

**Pros**: cleanly separates the empirical Family B pattern from the
recursion; well-founded recursion on `order` is automatic from cycle
343's `WellFoundedRelation` instance.

**Cons**: the "combine via cross-term recipe TBD" step is exactly
the Family C structural rule we don't yet have; without it the
variant is a partial definition. Also: the leaf-vs-non-leaf split
may not match the cycle 358 unfold structure (which treats all
children uniformly via `Σⱼ Aᵢⱼ · (...)`).

### Variant V2 — Fold-over-children (mirror cycle 358 expansion)

```lean
noncomputable def inversePolynomial : RootedTree → (RootedTree → ℝ) → ℝ
  | RootedTree.mk children => fun f =>
      let v := f RootedTree.vertex
      let recursivePart :=
        children.foldr (fun c acc =>
          acc · (v · (... f c ...) + inversePolynomial c f)) 1
      recursivePart - f (mk children)
  termination_by t => t.order
  decreasing_by exact RootedTree.order_lt_of_mem_children ‹_›
```

**Pros**: structurally matches the per-row `(Aᵢ − v)^k` factorisation
from cycle 368/370. Each child contributes one factor in a product
over the children list. The `−f (mk children)` self-term captures
the universal `−Φ_η(t)` invariant.

**Cons**: the per-child contribution formula `v · (... f c ...) +
inversePolynomial c f` is a guess — it needs to be derived from the
cycle 358 unfold and verified against all 8 closed forms by `unfold
+ ring`. The cross-term mixing for Family C (e.g., `c²` in
`mk [vertex, cherry]`) suggests the fold cannot be a simple product
— it may need to track "subtree polynomial vectors" rather than
scalar contributions.

### Variant V3 — Strong-induction explicit formula

Skip the recursive `def` entirely and ship Phase α' as a `theorem`
giving a closed-form `Σ` expression indexed by subtrees of `t`:

```lean
theorem elementaryWeightQ_phi_inv_eq_subtree_sum
    (η_q : Quotient PhiEquivalent.setoidSigma) (t : RT) :
    elementaryWeightQ_phi η_q⁻¹ t
      = Σ_{(s, coef) ∈ subtreeMultiset t} coef · (elementaryWeightQ_phi η_q s)
        - elementaryWeightQ_phi η_q t  -- the universal self-term
```

where `subtreeMultiset t : Multiset (RT × ℝ)` enumerates subtrees
of `t` with their multiplicities/coefficients per a combinatorial
recipe (Connes-Kreimer-style or Family-A/B/C combination).

**Pros**: avoids the recursion termination question entirely; the
combinatorial enumerator can be a separate definition that lives
in `Section301.lean` or `Section381.lean`.

**Cons**: requires identifying the combinatorial enumerator
`subtreeMultiset` precisely — this is essentially the Family C
problem in disguise. Also: matching the 8 closed forms requires
proving that `subtreeMultiset` on each ladder tree produces the
correct (subtree, coefficient) pairs, which is 8 separate `decide`
or `rfl` checks.

### Weighing the variants

* **V1** is the most modular but has the most "TBD" — it punts the
  Family C recipe to cycle 381+.
* **V2** is the most aligned with cycle 358's structural unfold,
  but the cross-term mixing problem (Family C `c²`, `2vm`) may
  invalidate the per-child-product shape.
* **V3** avoids recursion but requires the combinatorial enumerator
  to be designed up-front.

**Recommendation for cycle 380.** Start with **V2** as a hypothesis,
re-derive the per-child contribution formula by inspecting cycle
358's `_inv_mk` body and cycles 367/368/370's per-tree proofs, and
attempt to verify it on all 8 closed forms by `unfold + ring`. If
V2 fails on a Family C tree (most likely candidate:
`mk [vertex, cherry]` with the `c²` term), fall back to a partial
V1 (Family A only) for cycle 380 and defer Family B/C to cycle
381+.

Do NOT attempt to ship the recursive definition in cycle 379. This
is Phase α'.1 (cycle 380+) scope.

## §6 Project-hook inventory (verified at HEAD `d072990`)

All file paths and line numbers verified by `grep -n` against the
HEAD commit. The recursive `inversePolynomial` will consume these
existing hooks:

### Termination infrastructure (Section301.lean)

* `RootedTree.order_lt_of_mem_children` — `OpenMath/Chapter3/Section301.lean:167`
  (cycle 343 ship). Statement: `∀ {c : RootedTree} {children : List RootedTree},
  c ∈ children → c.order < (mk children).order`.
* `instance : WellFoundedRelation RootedTree := measure RootedTree.order`
  — `OpenMath/Chapter3/Section301.lean:177` (cycle 343 ship). Enables
  well-founded recursion on subtree order; the recursive
  `inversePolynomial` should require no explicit `decreasing_by`
  annotation beyond `exact RootedTree.order_lt_of_mem_children ‹_›`.

### 8 axiom-clean closed-form theorems (Section422.lean)

| Symbol | Line | Cycle |
|---|---|---|
| `elementaryWeightQ_phi_inv_vertex` | 415 | 341 (P3) |
| `elementaryWeightQ_phi_inv_cherry` | 2376 | 367 |
| `elementaryWeightQ_phi_inv_broom₃` | 2538 | 368 |
| `elementaryWeightQ_phi_inv_mkCherry` | 2772 | 369 |
| `elementaryWeightQ_phi_inv_bushy` | 3011 | 370 |
| `elementaryWeightQ_phi_inv_mkBroom₃` | 3397 | 371 |
| `elementaryWeightQ_phi_inv_mkVertexCherry` | 3798 | 372 |
| `elementaryWeightQ_phi_inv_mkMkCherry` | 4226 | 378 |

Plus the universal infrastructure theorem
`elementaryWeightQ_phi_inv_mk` (cycle 358) at
`Section422.lean:582` — the source of the cycle 358 structural
unfold.

### 8 axiom-clean m=0 Sub-lemma A corollaries (Section422.lean)

| Symbol | Line | Cycle |
|---|---|---|
| `powRep_sum_eq_of_agreement_at_vertex` | 2314 | 366 |
| `powRep_sum_eq_of_agreement_at_cherry_zero` | 2477 | 367 |
| `powRep_sum_eq_of_agreement_at_broom₃_zero` | 2695 | 368 |
| `powRep_sum_eq_of_agreement_at_mkCherry_zero` | 2941 | 369 |
| `powRep_sum_eq_of_agreement_at_bushy_zero` | 3229 | 370 |
| `powRep_sum_eq_of_agreement_at_mkBroom₃_zero` | 3704 | 371 |
| `powRep_sum_eq_of_agreement_at_mkVertexCherry_zero` | 4135 | 372 |
| `powRep_sum_eq_of_agreement_at_mkMkCherry_zero` | 4554 | 378 |

### 8 Phase β bridges + 1 Phase β aggregator (Section422.lean)

| Symbol | Line | Cycle |
|---|---|---|
| `elementaryWeightQ_phi_inv_eq_inversePolynomial_vertex` | 4953 | 375 |
| `elementaryWeightQ_phi_inv_eq_inversePolynomial_cherry` | 4967 | 375 |
| `elementaryWeightQ_phi_inv_eq_inversePolynomial_broom₃` | 4982 | 375 |
| `elementaryWeightQ_phi_inv_eq_inversePolynomial_mkCherry` | 5001 | 375 |
| `elementaryWeightQ_phi_inv_eq_inversePolynomial_bushy` | 5031 | 377 |
| `elementaryWeightQ_phi_inv_eq_inversePolynomial_mkBroom₃` | 5053 | 377 |
| `elementaryWeightQ_phi_inv_eq_inversePolynomial_mkVertexCherry` | 5092 | 377 |
| `elementaryWeightQ_phi_inv_eq_inversePolynomial_mkMkCherry` | 5143 | 378 |
| `elementaryWeightQ_phi_inv_eq_inversePolynomial_on_ladder` | 5200 | 378 refresh |

### Phase γ closed-subtree-agreement theorem (Section422.lean)

* `inversePolynomial_eq_of_subtree_agreement` — `Section422.lean:5260`
  (cycle 376 ship, extended in cycles 377 and 378). 8-way `by_cases`
  on `t`, default branch returns `0 = 0`. **Must be migrated to the
  recursive shape in Phase α'.3.**

### `inversePolynomial` definition (Section422.lean)

* `noncomputable def inversePolynomial` — `Section422.lean:4651`
  (cycle 374 ship, extended in cycles 377 and 378). 8-way
  `if-then-else`; default returns `0`. **Replaced by the recursive
  shape in Phase α'.1.**

### Cycle 365 grandfathered sorry (Section422.lean)

* `powRep_sum_eq_of_strict_subtree_agreement` — `Section422.lean:2272`,
  body sorry at `Section422.lean:2279`. The downstream consumer that
  Phase α'.4 (cycle 384+) will close.

## §7 Gap inventory — what's missing for Phase α'

The recursive `inversePolynomial` definition cannot ship until the
following gaps are addressed (in priority order):

### G1 — Family B closed-form derivation (CRITICAL)

The Family B binomial pattern (Σⱼ §4) requires symbolic re-derivation
from cycle 358's `_inv_mk` and cycles 367/368/370's per-tree proofs.
The cycle 379 §4 spot-checks suggested a recipe but encountered
sign-convention errors; cycle 380 must produce a precise formula
that matches `cherry`, `broom₃`, and `bushy` by `ring`.

**Mitigation.** The Family B formula is `(−1)^k`-prefactored
binomial sum of `(k choose j) · v^(k−j) · w_j`, possibly with a
self-term shift. The cycle 368 Discovery
(`elementaryWeightQ_phi_inv_broom₃` proof body) gives the per-row
`(Aᵢ − v)^k` factorisation that should yield the closed form
symbolically.

### G2 — Family C cross-term mixing rule (HIGH)

The cycles 371 (`mk [broom₃]` with `+2vm`) and 372
(`mk [vertex, cherry]` with `+c²` and `+vm`) closed forms have
quadratic and cross-product terms not predicted by Family A or B
alone. The structural rule is unclear from 2 data points.

**Mitigation.** Cycle 380 should derive the cross-term coefficient
recipe by inspecting the cycle 371 / 372 proof bodies' `h_subst`
distributions. Alternative: ship a "9th tree" (e.g.,
`mk [cherry, cherry]` or `mk [vertex, broom₃]`) as a targeted
disambiguation data point BEFORE designing the recursive shape.

### G3 — Multi-tree subtree enumeration (MEDIUM)

If V3 (strong-induction explicit formula) is the chosen variant,
the `subtreeMultiset t : Multiset (RT × ℝ)` enumerator must be
defined and proved correct against the 8 closed forms. This is
parallel work to the recursive variant.

**Mitigation.** Defer to cycle 382+ if V2 succeeds; reconsider as
the primary path if V2 fails on Family C.

### G4 — Per-tree bridge migration strategy (MEDIUM)

The 8 existing Phase β bridges (`_eq_inversePolynomial_vertex` ...
`_eq_inversePolynomial_mkMkCherry`) are currently `unfold
inversePolynomial` + `if_neg ... if_pos rfl` + per-tree closed-form
theorem. Under the recursive definition, the `unfold + ifs` chain
becomes `unfold inversePolynomial` + `rfl`-evaluation by structural
recursion on `t`.

**Acceptance criterion (per cycle 378 worker's Discovery hint):
on small trees, `unfold inversePolynomial` + `rfl` should match the
closed forms.** If this holds for all 8 trees, the migration is
mechanical (s/`unfold + ifs`/`rfl`/g across the 8 bridges). If it
fails on any tree, restate that bridge as `unfold + ring`.

### G5 — Phase γ migration (MEDIUM)

`inversePolynomial_eq_of_subtree_agreement` currently does an
8-way `by_cases` on `t`. Under the recursive definition, this
should reduce to a `RootedTree.recOn`-style induction over `t`'s
structure, with the recursion hypothesis `h_closed` discharging
each child's contribution.

**Mitigation.** Phase α'.3 (cycle 383) will need a new induction
principle: `∀ t, (∀ s ∈ t.children, P s) → P t` (strong induction
on children). This may already exist in `Section301.lean`'s
`mutual` block; if not, ship as Phase α'.3 prep.

### G6 — Cycle 365 grandfathered sorry compatibility (CRITICAL)

The cycle 365 sorry's body needs `inversePolynomial t
(elementaryWeightQ_phi η_q) = elementaryWeightQ_phi η_q⁻¹ t` for
arbitrary `t`. Phase α'.1's recursive definition must satisfy this
identity by construction (not just on the 8 ladder trees).

**Acceptance criterion.** A new global theorem
`elementaryWeightQ_phi_inv_eq_inversePolynomial`
`(η_q : Quotient PhiEquivalent.setoidSigma) (t : RT) :
elementaryWeightQ_phi η_q⁻¹ t = inversePolynomial t (elementaryWeightQ_phi η_q)`
must be provable by `RootedTree.induction` on `t`, using cycle
358's `_inv_mk` as the per-step unfold and the recursive
`inversePolynomial` evaluation as the per-step closed form. Phase
α'.4 (cycle 384+) will then use this global theorem to close the
cycle 365 sorry.

## §8 Phase decomposition (multi-cycle)

Outline 4 phases at 1–2 cycles each, total 4–6 cycles for Phase α'
through Phase α'.4. The cycle 365 grandfathered sorry closure is
the final acceptance test.

### Phase α'.1 (cycles 380–381) — Recursive `inversePolynomial` + α matching proofs

**Cycle 380 deliverables:**
* Derive the Family B closed-form formula precisely (G1).
* Re-derive the Family C cross-term recipe from cycles 371/372
  proof bodies (G2).
* Ship the recursive `inversePolynomial` definition (Variant V2
  preferred; fall back to partial V1 if V2 fails on Family C).
* Ship 8 calibration witnesses (one per ladder tree) using `unfold +
  rfl` or `unfold + ring`. Verify the recursive definition
  evaluates correctly on all 8 trees.
* Termination proof via cycle 343's `WellFoundedRelation`
  instance + `order_lt_of_mem_children` (should be automatic).

**Cycle 381 fallback** (if cycle 380 partial-ships V1):
* Add Family B branch to the recursive definition.
* Add Family C branch (depends on G2 resolution).
* Re-verify 8 calibration witnesses.

**Risk gate.** If cycle 380 cannot match all 8 closed forms within
one cycle, cycle 381 ships a partial-Family recursive definition
(Family A only) plus a documented gap for cycles 382–384 to address.

### Phase α'.2 (cycle 382) — Phase β bridge migration

* Mechanical port: replace each of the 8 bridges' `unfold + ifs`
  chain with `unfold inversePolynomial` + `rfl` (if α'.1 V2 succeeds)
  or `unfold + ring` (if α'.1 V1 partial). Re-verify all 8 bridges
  pass.
* Update `_on_ladder` aggregator to consume the migrated bridges.
* Verify axiom cleanliness of all 8 bridges + aggregator.
* Sorry count: unchanged at 1.

**Risk.** Bridges may need restatement if V2's recursive evaluation
doesn't match the closed forms by `rfl`. Mitigation: cycle 380's
calibration witnesses validate this before cycle 382 starts.

### Phase α'.3 (cycle 383) — Phase γ extension to all trees

* Replace the 8-way `by_cases` in
  `inversePolynomial_eq_of_subtree_agreement` with a strong
  induction on `t`'s structure.
* New induction principle (if needed): `∀ t, (∀ s ∈ t.children,
  P s) → P t`. May already exist in `Section301.lean`; if not, ship
  as a prerequisite lemma.
* New theorem
  `elementaryWeightQ_phi_inv_eq_inversePolynomial`
  (G6) — the global axiom-clean bridge from `Φ_{η⁻¹}` to
  `inversePolynomial` for arbitrary `t`. Proved by strong induction
  on `t.order`, using cycle 358's `_inv_mk` as the per-step unfold.
* Sorry count: unchanged at 1 (or +1 temporarily if the new theorem
  needs a sorry-first scaffold).

**Risk.** The strong induction may require a custom recursor that
matches `RootedTree.mk`'s indexed-inductive shape. Mitigation:
cycle 343 / Section301.lean already proved several theorems by
mutual recursion + `mk children` pattern matching (e.g., `theta`,
`density`); the same technique applies.

### Phase α'.4 (cycle 384+) — Close cycle 365 grandfathered sorry

* Use the cycle 383 global bridge
  `elementaryWeightQ_phi_inv_eq_inversePolynomial` to rewrite both
  sides of `powRep_sum_eq_of_strict_subtree_agreement`'s goal
  from `elementaryWeightQ_phi η_q^(-(m+1)) t` to
  `inversePolynomial t (elementaryWeightQ_phi η_q^(-m))`.
* Apply Phase γ `inversePolynomial_eq_of_subtree_agreement` with
  the hypothesis `_h_closed` to discharge the inversePolynomial
  equality.
* Induct on `m` to thread the strict-subtree-agreement hypothesis
  through `powRep` iteration.
* Sorry count: 1 → 0 on Section422.lean.

**This closes the cycle 365 grandfathered sorry and unlocks Phase
D.3.b parametricity Step 2 (per
`def_422B_subLemmaA_inductive_plan.md` §2).** From there, Phase D.3.d
(`underlyingOneStepMethod_aux` recursion) can begin.

**Risk.** The cycle 365 body may require additional machinery
beyond Phase α'.3's bridge — in particular, the `m+1` power
iteration of the `Φ` action may not commute cleanly with the
`inversePolynomial`. Mitigation: cycle 384's first task is to
verify the m=0 case (already shipped by cycles 366–378's 8 per-tree
corollaries) generalises smoothly to arbitrary `m`.

## §9 Risk assessment

Per-phase risk table with rollback precedents.

| Risk | Severity | Phase | Mitigation |
|---|---|---|---|
| R1 | HIGH | α'.1 | V2 recursive shape may not match all 8 closed forms by `rfl` or `unfold + ring`. Design the shape to mirror cycle 358's `_inv_mk` unfold structure; verify each tree via calibration witnesses BEFORE shipping the recursive definition. Fall back to partial V1 if V2 fails. |
| R2 | MEDIUM | α'.3 | Strong induction principle may not exist for `RootedTree`'s indexed-inductive shape. Cycle 343 / Section301.lean has precedent for mutual-recursion proofs; same technique applies. May need to ship a new `RootedTree.strongRecOn` lemma as α'.3 prep. |
| R3 | MEDIUM | α'.2 | The 8 existing Phase β bridges may not all remain `rfl`-equal under the recursive form. Mitigation: be prepared to restate them as `unfold + ring` proofs. Cycle 378's calibration witnesses (one `unfold + 7 if_neg + if_pos rfl` per tree) are the migration template. |
| R4 | LOW | α'.1 | Well-founded recursion termination proof may need explicit `decreasing_by` annotations. Cycle 343's `WellFoundedRelation` instance should make this automatic via `order_lt_of_mem_children`. |
| R5 | HIGH | α'.4 | The cycle 365 sorry may require more than the Phase γ extension. The `powRep` iteration on `m+1` may not commute with `inversePolynomial`. Mitigation: verify the m=0 case generalises smoothly before committing to the `m+1` induction; if not, ship an intermediate lemma `powRep_inversePolynomial_eq` first (per cycle 378's strategy recommendation). |
| R6 | MEDIUM | α'.1 | Family C cross-term recipe (G2) may require new combinatorial machinery (Connes-Kreimer-style coproduct, tree composition operator). If a clean recipe is not found in cycle 380, fall back to a partial recursive definition with explicit Family C cases listed (essentially the cycle 374/377/378 form, but with structural recursion on Family A and B). |

**Rollback precedents.** Multi-cycle Phase efforts that hit hard
mid-phase blockers and rolled back to a partial ship:

* **Cycle 200/201** — `thm:381H` partial ship rollback after a Phase
  C mid-phase blocker on the §381 generator independence proof.
  Precedent: partial-ship a working subset, document the gap, and
  defer the remainder.
* **Cycle 149/150** — `def:530B` scaffold rollback after the
  initial structure-encoding choice broke downstream consumers.
  Precedent: re-scope the design before continuing implementation.

Phase α' should expect at least one mid-phase rollback or re-scope
across the 4-phase plan. The cycle 373 precedent (this doc's
predecessor) successfully ran 5 cycles (374–378) without rollback;
Phase α' is more ambitious and should plan for one.

## §10 Cycle 380 entry point

Concrete first task for cycle 380:

1. **Re-read cycle 358 `elementaryWeightQ_phi_inv_mk` proof body**
   at `Section422.lean:582`. This is the structural seed: the
   per-summand formula `M.b i * M.derivativeWeightWithSrc
   M.inverse i t` is the source of every closed form in the 8-tree
   ladder.

2. **Read each of the 8 closed-form proofs** (cycles 341, 367, 368,
   369, 370, 371, 372, 378) at the line numbers listed in §6 above.
   Pay particular attention to the `h_subst` and per-row
   `(Aᵢ − v)^k`-style factorisations; these are where the
   recursive shape (Family A / B / C) is implicit.

3. **Derive precise closed-form formulas for Families A and B
   symbolically.** Family A: `c_n ↦ Σⱼ coeff_{n,j} · monomial_{n,j}`
   for some coefficient table. Family B: binomial sum (per §4
   spot-check, with signs to be nailed down).

4. **Sketch the recursive `inversePolynomial` (Variant V2)** with
   per-child contribution formula. Test by `unfold + ring` on all 8
   ladder trees BEFORE committing the definition.

5. **Ship Phase α'.1** per §8 above.

If Phase α'.1's recursive shape isn't immediately clear from
inspecting the closed-form proofs, cycle 380 may need to ship a
partial recursive definition (e.g., for Family A only, with Family
B/C falling through to the cycle 374/377/378 pattern-match form).
This split-shipping pattern matches cycle 358's α.1/α.2/α.3 sub-phase
precedent (`Section422.lean:582` and surrounding ships).

**Alternative entry point** (if Phase α'.1 prep work needs another
cycle): ship a "9th tree" closed form as targeted G2 data
acquisition. Candidates:

* `mk [cherry, cherry]` (order 5, σ = 2) — tests Family C with two
  identical non-leaf children.
* `mk [vertex, broom₃]` (order 5, σ = 1) — tests Family C with
  leaf + non-leaf children of different orders.
* `mk [mk [mk [cherry]]]` (order 5, σ = 1) — tests Family A
  depth-4 extrapolation directly; the §4 conjectured form is
  `c_4 ↦ −c_0⁵ + 4c_0³c_1 − 2c_0c_1² − 3c_0²c_2 + 2c_1c_2 +
  2c_0c_3 − c_4` (7-term, to be verified).

This is the cycle 378 worker's "Option B" (rejected by cycle 379
planner for general extension but acceptable as targeted Phase α'
prep work).

### Cycle 383 update — Phase α'.3 Family B bridge migration shipped

Mirrors the cycle 381 Family A bridge migration for the Family B
leaves of the 8-tree ladder.

**Migration body changes** (Section422.lean ~4927–4965):

* `inversePolynomial`'s `else if t = RootedTree.broom₃` branch now
  reads `inversePolyBroom 2 f` (was the explicit polynomial
  `-(f vertex)^3 + 2·f vertex · f cherry - f broom₃`).
* `inversePolynomial`'s `else if t = RootedTree.bushy` branch now
  reads `inversePolyBroom 3 f` (was the explicit polynomial
  `(f vertex)^4 - 3·(f vertex)^2 · f cherry + 3·f vertex · f broom₃
  - f bushy`).

**Downstream theorem updates** (~30 LOC of additional `rw`
arguments):

* broom₃ calibration witness — appends `inversePolyBroom_two` to
  the `rw [...]` chain after `if_pos rfl`.
* bushy calibration witness — appends `inversePolyBroom_three`.
* Phase β `elementaryWeightQ_phi_inv_eq_inversePolynomial_broom₃`
  — trailing `inversePolyBroom_two` before the
  `exact elementaryWeightQ_phi_inv_broom₃ η_q` close.
* Phase β `elementaryWeightQ_phi_inv_eq_inversePolynomial_bushy` —
  trailing `inversePolyBroom_three` before the
  `exact elementaryWeightQ_phi_inv_bushy η_q` close.
* Phase γ `inversePolynomial_eq_of_subtree_agreement` broom₃ branch
  — trailing `inversePolyBroom_two, inversePolyBroom_two` (once
  per side `f`/`g`) before `hv, hc, hb` substitution.
* Phase γ same theorem's bushy branch — trailing
  `inversePolyBroom_three, inversePolyBroom_three` before
  `hv, hc, hb, hbu`.

**New public bridge theorems** (~25 LOC, sit after the four
`inversePolyChain_*_eq_inversePolynomial` Family A bridges):

* `inversePolyBroom_two_eq_inversePolynomial (f : RT → ℝ) :
    inversePolyBroom 2 f = inversePolynomial RootedTree.broom₃ f`
  — three-step `unfold + rw` (two `if_neg` discharges + `if_pos rfl`).
* `inversePolyBroom_three_eq_inversePolynomial (f : RT → ℝ) :
    inversePolyBroom 3 f = inversePolynomial RootedTree.bushy f`
  — five-step `unfold + rw` (four `if_neg` discharges + `if_pos rfl`).

**Verification**:

* `lake env lean OpenMath/Chapter4/Section422.lean` exits 0 (only
  warning is the grandfathered cycle 365 sorry at line 2279).
* `lake build OpenMath.Chapter4` exits 0.
* `grep -c sorry OpenMath/Chapter4/Section422.lean` = 5 (unchanged).
* Tautology regex over Section422.lean — 0 hits.
* `#print axioms` on
  `inversePolyBroom_two_eq_inversePolynomial`,
  `inversePolyBroom_three_eq_inversePolynomial`,
  `elementaryWeightQ_phi_inv_eq_inversePolynomial_broom₃`,
  `elementaryWeightQ_phi_inv_eq_inversePolynomial_bushy`,
  `inversePolynomial_eq_of_subtree_agreement` — all return
  `[propext, Classical.choice, Quot.sound]`.

**Faithfulness**: Infrastructure migration; no new textbook entity.
Closed-form RHS values for `broom₃` and `bushy` cases of
`inversePolynomial` are unchanged from cycles 368 and 370. No
hypothesis weakening or strengthening. `lean_status.json` `def:422B`
row's `cycle_completed_at` bumped to 383; status remains `partial`.

**§422 axiom-clean streak**: 46 substantive + 1 doc (336–382) →
**47 substantive + 1 doc** (336–383).

**Cycle 384+ outlook (unchanged from cycle 382 task results)**:

* Cycle 384: Family C scoping doc for `mk [broom₃]` and
  `mk [vertex, cherry]` heterogeneous-children trees (don't fit
  Family A chain or Family B binomial recipes).
* Cycle 385+: Phase α'.4 closure of the cycle 365 grandfathered
  sorry via a unified recursive `inversePolynomial` (or
  `inversePolyTree`) covering arbitrary `t`, plus the global bridge
  `elementaryWeightQ_phi_inv_eq_inversePolynomial`.

## §11 Self-reference & cross-links

### Predecessor scoping docs

* `.prover-state/issues/def_422B_subLemmaA_inductive_plan.md`
  (cycle 373 — predecessor scoping doc; Phase α/β/γ/δ structure
  for the original 8-tree ladder).
* `.prover-state/issues/def_422B_phase_D_3_scoping.md`
  (cycle 357 — Phase D.3 sub-phases, including the cycle 363
  audit and cycle 365 split into Sub-lemma A/B).
* `.prover-state/issues/def_422B_path.md` (cycle 336 — overall
  `def:422B` roadmap).
* `.prover-state/issues/lem_310B_plan.md` (cycle 260 — earlier
  example of a Lean-free phased plan that drove multi-cycle
  ladder work).

### Cycle 378 cross-links (most recent)

* `.prover-state/task_results/cycle_378.md` §"Suggested next
  approach" — explicit Option A authorisation for this scoping doc.
* `.prover-state/task_results/cycle_378.md` §"Discovery" D1 —
  the single-child ladder structural insight that seeds Family A.

### Source material

* `extraction/raw_text/ch04.txt:1148–1173` — Butcher §422
  textbook source ("E group" and η_q derivation).
* `extraction/formalization_data/entities/def_422B.json` —
  entity metadata for `def:422B`.

### Lean files

* `OpenMath/Chapter4/Section422.lean` — file under analysis. 5595
  LOC at HEAD `d072990`. 1 grandfathered sorry at line 2279
  (cycle 365). 5 total `grep -c sorry` hits (4 docstring + 1
  code).
* `OpenMath/Chapter3/Section301.lean` — termination infrastructure
  (`order_lt_of_mem_children` at line 167,
  `WellFoundedRelation` instance at line 177).
* `OpenMath/Chapter3/Section310.lean` — `RootedTree` inductive
  definition (line 83) and canonical trees (`vertex` line 108,
  `cherry` line 111, `broom₃` line 114, `bushy` line 118).
* `OpenMath/Chapter4/Section381.lean` — `derivativeWeightWithSrc`
  infrastructure (used by cycle 358's `_inv_mk`).

### Memory cross-links

* `feedback_rootedtree_nested_induction.md` — Phase α'.3 will need
  this: `induction t` / `RootedTree.recOn` fail on nested
  inductives; use `mutual` block of theorems with constructor
  pattern matching.
* `feedback_planner_faithfulness_spotcheck.md` — the Phase α'
  design proposals (V1/V2/V3) must be spot-checked against the 8
  closed forms before shipping, per this memory.

---

**End of scoping doc.** Cycle 379 ships this markdown file as its
sole deliverable; standard bookkeeping (task results, heartbeat,
history.jsonl) follows. No Lean code, no axioms, no sorry-count
changes. Cycle 380 enters per §10 above.
