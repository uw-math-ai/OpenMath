# Issue: `def:422B` Phase α'.4 Family C scoping — unified `inversePolyTree` recursion

## §1 Status & blocker

**Scoping doc, cycle 385.** No Lean code shipped this cycle — this is a
markdown-only research doc distilling the three Family C closed-form
witnesses (cycles 371, 372, 384) into a concrete multi-cycle plan for
a unified `inversePolyTree` recursion that handles
heterogeneous-children trees. The cycle 384 worker's "Suggested next
approach" (`task_results/cycle_384.md`) explicitly named this scoping
doc as the next move; the cycle 385 planner authorised the
markdown-only ship in `strategy.md` §"Priority 1 — DELIVERABLE".

This doc follows two precedents:

* `.prover-state/issues/def_422B_subLemmaA_inductive_plan.md`
  (cycle 373 — 1399 lines, 11 sections; drove cycles 374–378's 8-tree
  ladder build-out).
* `.prover-state/issues/def_422B_phase_alpha_prime_scoping.md`
  (cycle 379 — 981 lines, 11 sections; drove cycles 380–383's
  Family A/B recursive helper ships).

Both scoping cycles shipped only markdown and were scored OK; the
cycle 385 ship is the next link in that chain, narrowing in on the
Family C heterogeneous-children case.

**§422 axiom-clean streak: 48 substantive + 1 doc (cycles 336–384).**
Single grandfathered sorry at `OpenMath/Chapter4/Section422.lean:2279`
(cycle 365's `powRep_sum_eq_of_strict_subtree_agreement` general body).
Section422.lean: 6520 LOC. `grep -c sorry` returns 5 (4 docstring
references + 1 actual code sorry).

**Phase α' progress to date.**

* Phase α'.1 (cycles 380–381 — Family A) — shipped
  `inversePolyChain : ℕ → (RT → ℝ) → ℝ` plus the cons-style
  convolution recurrence and four calibration witnesses
  (`inversePolyChain_{zero, one, two, three}`); Family A branches of
  `inversePolynomial` (`vertex`, `cherry`, `mk [cherry]`,
  `mk [mk [cherry]]`) now dispatch to `inversePolyChain k f`.
* Phase α'.2 (skipped — `bichildPolynomial` design deferred until
  cycle 385's scoping doc; see §4 below).
* Phase α'.3 (cycles 382–383 — Family B) — shipped
  `inversePolyBroom : ℕ → (RT → ℝ) → ℝ` (binomial closed form, NOT a
  convolution recurrence — the broom family lacks single-child
  structure) plus four calibration witnesses and two bridge migrations
  for `broom₃` and `bushy`.
* **Phase α'.4 (this scope — Family C)** — the unified recursion for
  heterogeneous-children trees, covering the three witnesses below.

**Blocker.** Without Phase α'.4, `inversePolynomial` cannot evaluate
correctly on arbitrary heterogeneous-children trees outside the
9-tree ladder. The cycle 365 grandfathered sorry's body needs
`inversePolynomial t f` to evaluate to the *correct* closed form for
every `t`, not `0`; Family C trees are the last structural shape not
covered by Families A and B. The Phase α'.4 deliverable is a
recursive definition whose evaluation on every heterogeneous-children
tree matches the algebraic closed form derivable from cycle 358's
`elementaryWeightQ_phi_inv_mk`.

## §2 The three Family C witnesses (full catalog)

The three closed forms shipped in cycles 371, 372, 384 form the
empirical input to the Phase α'.4 recursion design.

| Cycle | Tree | Order | σ(t) | Children list | Self-term |
|---|---|---|---|---|---|
| 371 | `mk [broom₃]` | 4 | 1 | `[broom₃]` | `−Φ_η(mk [broom₃])` |
| 372 | `mk [vertex, cherry]` | 4 | 1 | `[vertex, cherry]` | `−Φ_η(mk [vertex, cherry])` |
| 384 | `mk [cherry, cherry]` | 5 | 2 | `[cherry, cherry]` | `−Φ_η(mk [cherry, cherry])` |

### §2.1 Cycle 371: `Φ_{η_q⁻¹}(mk [broom₃])`

Source: `Section422.lean:3397–3624` (theorem
`elementaryWeightQ_phi_inv_mkBroom₃`).

```
Φ_{η_q⁻¹}(mk [broom₃])
   =  (Φ_η(vertex))^4
    − 3 · (Φ_η(vertex))^2 · Φ_η(cherry)
    +     Φ_η(vertex) · Φ_η(broom₃)
    + 2 · Φ_η(vertex) · Φ_η(mk [cherry])
    −     Φ_η(mk [broom₃])
```

* Distinct elementary-weight kernels on RHS: **5** (vertex, cherry,
  broom₃, mk[cherry], mk[broom₃]).
* Leading sign: `+ v⁴` (positive — order-4 parity).
* Self-term sign: `−1` (uniform across all three witnesses).
* Cross-term coefficients: `−3, +1, +2` (the substantive content).
* Children list: `[broom₃]` (single non-leaf child); strict
  heterogeneity classification: **single-child, depth-2 ladder with
  broom₃-shape inner subtree**.

### §2.2 Cycle 372: `Φ_{η_q⁻¹}(mk [vertex, cherry])`

Source: `Section422.lean:3798–4051` (theorem
`elementaryWeightQ_phi_inv_mkVertexCherry`).

```
Φ_{η_q⁻¹}(mk [vertex, cherry])
   =  (Φ_η(vertex))^4
    − 3 · (Φ_η(vertex))^2 · Φ_η(cherry)
    +     (Φ_η(cherry))^2
    +     Φ_η(vertex) · Φ_η(broom₃)
    +     Φ_η(vertex) · Φ_η(mk [cherry])
    −     Φ_η(mk [vertex, cherry])
```

* Distinct elementary-weight kernels on RHS: **6** (vertex, cherry,
  broom₃, mk[cherry], mk[vertex,cherry], plus the `c²` self-quadratic).
* Leading sign: `+ v⁴` (positive — order-4 parity).
* Self-term sign: `−1`.
* Cross-term coefficients: `−3, +1, +1, +1` (the substantive content;
  note the `+1·v·b'` and `+1·v·m` coefficients are *both* `+1`, in
  contrast to cycle 371's `+1, +2` split).
* Children list: `[vertex, cherry]` (asymmetric two-child); strict
  heterogeneity classification: **binary, leaf + cherry**. **First
  asymmetric two-child witness**.
* New kernel introduced: `(Φ_η(cherry))²` — the first `c²` quadratic
  self-term in any closed form to date.

### §2.3 Cycle 384: `Φ_{η_q⁻¹}(mk [cherry, cherry])`

Source: `Section422.lean:4655–4961` (theorem
`elementaryWeightQ_phi_inv_mkCherryCherry`).

```
Φ_{η_q⁻¹}(mk [cherry, cherry])
   = − (Φ_η(vertex))^5
    + 4 · (Φ_η(vertex))^3 · Φ_η(cherry)
    − 3 · Φ_η(vertex) · (Φ_η(cherry))^2
    −     (Φ_η(vertex))^2 · Φ_η(broom₃)
    − 2 · (Φ_η(vertex))^2 · Φ_η(mk [cherry])
    + 2 · Φ_η(cherry) · Φ_η(mk [cherry])
    + 2 · Φ_η(vertex) · Φ_η(mk [vertex, cherry])
    −     Φ_η(mk [cherry, cherry])
```

* Distinct elementary-weight kernels on RHS: **6** (vertex, cherry,
  broom₃, mk[cherry], mk[vertex,cherry], mk[cherry,cherry]).
* Leading sign: `− v⁵` (negative — order-5 parity).
* Self-term sign: `−1` (consistent with cycles 371, 372).
* Cross-term coefficients: `+4, −3, −1, −2, +2, +2` (the substantive
  content; mixed signs).
* Children list: `[cherry, cherry]` (symmetric two-child); strict
  heterogeneity classification: **binary, two identical non-leaf
  children**. **First symmetric two-non-leaf-children witness**.
* New kernel introduced: `Φ_η(mk [vertex, cherry])` — the cross-term
  from §3.2 block (4) below. **This is the cycle 384 surprise**: the
  planner's `mk [cherry, cherry]`-only speculative recipe didn't
  anticipate that the bilinear cross-term would surface
  `mk [vertex, cherry]` as a dependency.

### §2.4 Coverage gap

The three witnesses span:

* Single non-leaf child (cycle 371: `[broom₃]`).
* Asymmetric two-child mixing one leaf and one non-leaf (cycle 372:
  `[vertex, cherry]`).
* Symmetric two-non-leaf-children (cycle 384: `[cherry, cherry]`).

Not yet covered:

* Asymmetric two-non-leaf-children with **distinct** non-leaf subtrees
  (e.g. `mk [broom₃, cherry]`, `mk [cherry, broom₃]`,
  `mk [vertex, broom₃]`).
* Three-or-more-child trees (e.g. `mk [vertex, vertex, cherry]`,
  `mk [cherry, cherry, cherry]`).
* Depth-3 heterogeneous trees (the cycle 378 witness
  `mk [mk [cherry]]` is depth-3 but is Family A — single child).

## §3 Structural observations (the analysis)

### §3.1 The `(per-child)`-product pattern (from cycles 368/370)

For any `t = mk children`, cycle 358's `elementaryWeightQ_phi_inv_mk`
unfolds the per-row representative form of
`derivativeWeightWithSrc M.inverse i t` as a product over children:

```
M.inverse.derivativeWeightWithSrc i (mk [c₁, …, cₖ])
  = Πℓ ( M.inverse.elementaryWeight cℓ
       + Σⱼ M.A i j · M.inverse.derivativeWeight j cℓ )
```

Under `inv_v = −v`, each child-factor `Fℓ` takes one of two shapes:

* **Leaf child** (`cℓ = vertex`):
  `Fℓ = − Φ_η(vertex) + Σⱼ Aᵢⱼ`. Linear in `A`.
* **Non-leaf child** (`cℓ = mk [...]` with at least one own child):
  `Fℓ = M.inverse.elementaryWeight cℓ + Σⱼ Aᵢⱼ · (...)`. The
  `(...)` is itself a product of cycle-358-unfolds for `cℓ`'s
  children — recursive structure.

The summand `M.b i · Πℓ Fℓ` then distributes into a polynomial sum
over `{i}, {j₁, …, jₖ}` indices. For each `Fℓ` we choose either the
constant term `M.inverse.elementaryWeight cℓ` (= the closed form at
`cℓ`'s inverse, recursively) or the `Σⱼ Aᵢⱼ · …` term. The number of
multiplicative blocks scales as `2^k` where `k = #children`.

### §3.2 Cross-term cataloging (binary case)

For `t = mk [t₁, t₂]` (binary case), the expansion of the two-factor
product yields four blocks per `i`:

| Block | Selection | Algebraic shape | Comment |
|---|---|---|---|
| (1) | const · const | `inv₁ · inv₂` | Pure subtree-inverse product |
| (2) | const · A-sum | `inv₁ · Σⱼ Aᵢⱼ · dw(t₂, j)` | Linear in `A`, on `t₂` |
| (3) | A-sum · const | `(Σⱼ Aᵢⱼ · dw(t₁, j)) · inv₂` | Linear in `A`, on `t₁` |
| (4) | A-sum · A-sum | `(Σⱼ Aᵢⱼ · dw(t₁, j)) · (Σⱼ Aᵢⱼ · dw(t₂, j))` | **Bilinear cross-term** |

Notation:

* `inv_ℓ := M.inverse.elementaryWeight tℓ` (closed form at the
  inverse of subtree `tℓ`, recursively known by Phase α'.1/α'.3).
* `dw(tℓ, j) := M.inverse.derivativeWeight j tℓ` (per-row weight at
  stage `j`).

After multiplying through by `M.b i` and summing over `i`:

* Block (1) → `Σᵢ bᵢ · inv₁ · inv₂` (independent of `i`-row data) =
  `(Σᵢ bᵢ) · inv₁ · inv₂` = `Φ_η(vertex) · inv₁ · inv₂`. Pure scalar
  multiple of the recursive product.
* Block (2) → `inv₁ · Σᵢ bᵢ · Σⱼ Aᵢⱼ · dw(t₂, j)` =
  `inv₁ · Φ_η(mk [t₂])` (the parent of `t₂`-only). Linear in the
  one-child closed form.
* Block (3) → symmetric to (2): `inv₂ · Φ_η(mk [t₁])`.
* Block (4) → `Σᵢ bᵢ · (Σⱼ Aᵢⱼ · dw(t₁, j)) · (Σⱼ Aᵢⱼ · dw(t₂, j))` =
  `Φ_η(mk [t₁, t₂])` evaluated under η (not η_q⁻¹)? **No — this is
  the *original* η-image, not the inverse**: the bilinear sum is
  exactly the cycle-358 unfold of `derivativeWeightWithSrcProd` for
  the two-child tree `mk [t₁, t₂]`. Hence block (4) contributes
  `Φ_η(mk [t₁, t₂])` (with a sign coming from the recursion).

Concretely for cycle 384 (`t = mk [cherry, cherry]`):

* Block (1) collapses to `Φ_η(vertex) · inv_c² = v · (v² − c)² =
  v⁵ − 2v³c + vc²`.
* Blocks (2) and (3) are equal (by symmetry): each contributes
  `inv_c · Φ_η(mk [cherry]) = (v² − c) · m`.
* Block (4) contributes `Φ_η(mk [cherry, cherry])` *with the η-image
  (not inverse)* — but wait, the cycle 384 closed form does *not*
  feature `Φ_η(mk [cherry, cherry])` on RHS except in the
  self-term. Re-examining cycle 384's recipe: **the bilinear block
  (4) instead surfaces `Φ_η(mk [vertex, cherry])`** via the
  cons-case unfold of `derivativeWeightWithSrcProd` — specifically,
  `Σⱼ Aᵢⱼ · dw(cherry, j) = Σⱼ Aᵢⱼ · Σₖ Aⱼₖ`, and squaring this then
  summing against `bᵢ` gives the binary derivative-weight expansion
  of `mk [vertex, cherry]`'s elementary weight.

The detail of *which* third-tree-shape surfaces in block (4) is the
key empirical question Phase α'.4 must resolve. Cycle 384's discovery
(see `task_results/cycle_384.md` §Discovery) was that the answer is
**not** symmetric: for `mk [cherry, cherry]` the bilinear block
surfaces `mk [vertex, cherry]`, not `mk [cherry, cherry]` itself.

### §3.3 Why Families A and B miss this

**Family A** (single-child chain — cycle 380's `inversePolyChain`):

* Only blocks (1) and (2) of §3.2 contribute (no second child).
* The convolution-style recurrence
  `inversePolyChain (n+1) f = −Σₚ inversePolyChain (n−p) f · f (chainTree p)`
  captures exactly this: each summand is a constant-times-constant
  product against the parent of `chainTree p`. No bilinear-in-A
  block ever appears.
* Consequence: `inversePolyChain` has no cross-term machinery.

**Family B** (k identical leaf-children — cycle 382's
`inversePolyBroom`):

* Block (4) collapses under binomial expansion: every leaf-factor is
  `(−v + Σⱼ Aᵢⱼ) = (Aᵢ − v)`, identical for each child.
* The product `(Aᵢ − v)^k` expands as a binomial sum
  `Σⱼ C(k, j) · (Aᵢ)^j · (−v)^(k−j)`.
* Each `(Aᵢ)^j` term, summed against `bᵢ`, contributes exactly
  `Φ_η(broomTree j)` (the order-`(j+1)` broom). No cross-tree-shape
  contribution arises because every child has the same `dw` profile.
* Consequence: `inversePolyBroom` uses a non-convolution closed form
  (binomial sum), not a recurrence over different subtree shapes.

**Family C** is the **genuine multi-child heterogeneous case** where
block (4) (and its higher-arity analogues for `k ≥ 3` children)
produces new elementary-weight kernels that are neither in the
A-chain's left-most-descendant trail nor in the B-broom's binomial
expansion. The cycle 384 surprise is the empirical proof that even
the *binary symmetric two-cherry* case requires `mk [vertex, cherry]`
in its closed form — a kernel that has no analogue in Family A or B.

## §4 Conjectured `inversePolyTree` recursion

The Phase α'.4 deliverable will be a recursive definition that
handles arbitrary heterogeneous-children trees. Building on cycles
380's `inversePolyChain` (Family A) and 382's `inversePolyBroom`
(Family B), the proposal is **Variant V4** (extending §5 of cycle
379's scoping doc with three new variants V1/V2/V3 superseded):

### §4.1 Variant V4 sketch

```lean
noncomputable def inversePolyTree (t : RT) (f : RT → ℝ) : ℝ :=
  match t with
  | RootedTree.mk children =>
      -- Dispatch on heterogeneity shape:
      --   * Family A: 0-child or single-child chain → inversePolyChain
      --   * Family B: k identical leaf-children → inversePolyBroom
      --   * Family C: mixed children → recursive child-product
      --     unfold with bilinear cross-term helper.
      sorry  -- design pending; see §4.2 below
```

The cycle 385 scoping does **not** lock the exact Lean syntax — the
recursion shape needs more data points (see §5/§6) before
single-cycle implementation is safe.

### §4.2 What needs to be added beyond Families A and B

The Family A `inversePolyChain` and Family B `inversePolyBroom` both
have **no bilinear-in-A machinery**. Family C requires a new helper:

**`bichildPolynomial : (RT × RT) → (RT → ℝ) → ℝ`** —

Conjectured shape:

```
bichildPolynomial (t₁, t₂) f
   =   Φ_η(vertex) · inversePoly(t₁) · inversePoly(t₂)
     + inversePoly(t₁) · f (mk [t₂])
     + inversePoly(t₂) · f (mk [t₁])
     + crossTermKernel(t₁, t₂) f
     − f (mk [t₁, t₂])
```

where `crossTermKernel(t₁, t₂) f` is the block-(4) bilinear sum that
surfaces an extra elementary-weight kernel determined by the pair
`(t₁, t₂)`. Empirically (cycle 384):

* `crossTermKernel(cherry, cherry) f = 2 · Φ_η(vertex) · f (mk [vertex, cherry])` — but
  the actual cycle 384 closed form has *additional* terms beyond
  this naive sketch, including a `+2 · Φ_η(cherry) · Φ_η(mk [cherry])`
  contribution. The naive bichild recipe is incomplete.

Two interpretations of the cycle 384 closed form:

1. The "extra" cross-term `+ 2 · Φ_η(cherry) · Φ_η(mk [cherry])` is a
   block-(4) sub-component picked up by a particular factorisation
   of the cherry-cherry product (one cherry contributes its
   `inv_c = v² − c` term, the other contributes its A-sum).
2. The naive product decomposition above is correct *modulo*
   reassociating which terms count as "blocks (2)/(3)" vs "block
   (4)". The cycle 384 closed form's `+2cm` and `−2v²m` terms both
   originate from block-(2)/(3) interactions with the inverse-child
   constant.

The right way to pin which interpretation is correct is to ship one
more data point with **distinct** non-leaf children — see §5.

### §4.3 Higher-arity children (k ≥ 3)

For three-or-more-child trees, blocks (4) generalize to trilinear
(and higher) cross-term blocks. The number of blocks scales as
`2^k`. Empirically uncharted — no order-6+ multi-child witness exists
in the ladder yet.

Mitigation: defer `k ≥ 3` heterogeneous-children handling to Phase
α'.5 (post-α'.4). Phase α'.4 focuses on binary-children Family C
trees; this covers `mk [broom₃]` (k=1), `mk [vertex, cherry]` (k=2),
`mk [cherry, cherry]` (k=2), and the cycle 386 witness (k=2). All
three shipped witnesses have `k ≤ 2`.

## §5 Phase decomposition

Three sub-phases, 1–2 cycles each:

| Sub-phase | Cycle(s) | Deliverable |
|---|---|---|
| α'.4.0 | 1 (cycle 386) | One more Family C witness: `mk [broom₃, cherry]` (order 6, k=2, asymmetric two-non-leaf-children). Pin the cross-term recipe. |
| α'.4.1 | 1–2 (cycle 387+) | Ship recursive `inversePolyTree` (Variant V4) with `bichildPolynomial` helper. Calibration witnesses against all 10 ladder trees. |
| α'.4.2 | 1 (cycle 388+) | Migrate `inversePolynomial`'s Family C branches (`mk [broom₃]`, `mk [vertex, cherry]`, `mk [cherry, cherry]`) to dispatch to `inversePolyTree`. Phase β bridge updates. |

### §5.1 α'.4.0 — fourth Family C witness

**Target tree**: `mk [broom₃, cherry]` (order 6, σ = 1).

* Why this tree: it is the smallest order-6 two-non-leaf-children
  tree with **distinct** non-leaf subtrees. Cycle 384's
  `mk [cherry, cherry]` had two identical cherry children; cycle
  386's `mk [broom₃, cherry]` will have one `broom₃` and one
  `cherry`. Tests the bilinear block (4) at non-symmetric inputs.
* Symmetry control: also consider shipping `mk [cherry, broom₃]` as
  a redundancy check — by commutativity of `derivativeWeightProd`
  over a list and `Finset.sum` over a finite `Fin s`, the closed
  form must be identical modulo argument order (modulo Lean's
  `List.Perm` not being definitionally equal — see §6 R2).

**Predicted closed form shape** (from extrapolating cycles 371/372):

* Distinct elementary-weight kernels: 8–10 (extrapolating from
  6 at order 5 to ~10 at order 6).
* Self-term sign: `−1` (uniform).
* Leading sign: `+v⁶` (order-6 even parity).
* New kernels potentially introduced: `mk [broom₃]`,
  `mk [vertex, cherry]`, `mk [broom₃, cherry]` itself, possibly
  `mk [vertex, broom₃]` (the analogue of cycle 372's surprise).

LOC budget for α'.4.0: ~250 LOC (per the cycle 384 ship's +521 LOC
budget; cycle 386 is one step further out so closer to ~250).

### §5.2 α'.4.1 — recursive `inversePolyTree` ship

**Deliverable**: noncomputable def `inversePolyTree`, the
`bichildPolynomial` helper, plus 10 calibration witnesses
`inversePolyTree_eq_*` matching each currently-shipped closed form.

**Pre-conditions**:

* Cycle 386's α'.4.0 witness shipped (to pin the cross-term recipe).
* Phase α'.4 cross-term symmetry empirically validated against at
  least one asymmetric and one symmetric two-non-leaf-children pair.

**Conjectured LOC budget**: ~300–500 LOC. May need to split across
two cycles if the recursive `noncomputable def` proves heavy in Lean
elaboration (the cycle 379 design discussion flagged this concern).

### §5.3 α'.4.2 — Family C branch migration

**Deliverable**: `inversePolynomial`'s Family C branches now dispatch
to `inversePolyTree (mk [...])`. Parallel to cycles 381 (Family A
migration) and 383 (Family B migration).

**LOC budget**: ~100–150 LOC. Three bridge theorems
`inversePolyTree_{mkBroom₃, mkVertexCherry, mkCherryCherry}_eq_inversePolynomial`,
plus rewrite trail through Phase β bridges
(`elementaryWeightQ_phi_inv_eq_inversePolynomial_{mkBroom₃, mkVertexCherry, mkCherryCherry}`)
and the Phase γ `inversePolynomial_eq_of_subtree_agreement` heterogeneous
branches.

## §6 Risk assessment

| Risk | Severity | Mitigation |
|---|---|---|
| R1: recursion shape under-determined by 3 data points | HIGH | Ship 4th witness (cycle 386's `mk [broom₃, cherry]`) before designing recursion. |
| R2: cross-term symmetry under child-permutation | MEDIUM | Ship symmetry-witness pair (`mk [broom₃, cherry]` and `mk [cherry, broom₃]`) at cycle 386–386b. Tests block (4) under list-order swap. |
| R3: order-6+ trees have new elementary-weight dependencies | MEDIUM | Witness-accumulation discipline + scoping refinement at end of α'.4.0. |
| R4: `bichildPolynomial` LOC budget exceeds single cycle | LOW | α'.4.1 estimate already allows 1–2 cycles. |
| R5: `inversePolyTree`'s `noncomputable def` elaboration time | LOW | Mathlib's `WellFoundedRelation` instance on `RootedTree.order` (from cycle 336 Phase 0) handles termination; cycle 379's α' design already exercised this. |
| R6: `k ≥ 3` heterogeneous children surfaces in mid-α'.4 | LOW | Explicitly deferred to Phase α'.5; no `k ≥ 3` witness in ladder yet. |
| R7: cycle 386 ship surfaces a NEW order-5 kernel not in cycle 384's RHS | MEDIUM | Treat as expected (extrapolating cycle 384's surprise pattern); ship the witness with the new kernel and update §3.2 cross-term taxonomy. |

### §6.1 R1 mitigation detail

Three data points (cycles 371, 372, 384) constrain the recursion
shape, but two of them (cycles 371, 372) share the same parity (both
order 4) and one is single-child (cycle 371). The bilinear block (4)
only manifests visibly in cycle 384 (k=2 two-non-leaf-children, the
first such case). One additional data point with **distinct
non-leaf** children is the minimum needed to disambiguate symmetric
vs asymmetric cross-term contributions.

### §6.2 R2 mitigation detail

If `Φ_{η_q⁻¹}(mk [broom₃, cherry]) = Φ_{η_q⁻¹}(mk [cherry, broom₃])`
(modulo the `mk [...]` argument order), then the cross-term is
symmetric. This is expected from the underlying mathematical content
(rooted trees are unordered multisets of children at the §383
quotient level — `PhiEquivalent` quotients out child permutations).
But Lean's `RootedTree.mk` is built on `List`, not `Multiset`, so
the two trees may **not** be definitionally equal. The witness pair
would empirically confirm whether the bilinear block is
permutation-symmetric in its inputs.

## §7 Cycle 386 entry point

**Recommended target tree**: `mk [broom₃, cherry]` (order 6, σ = 1).

* Children list: `[broom₃, cherry]` (asymmetric two-non-leaf-children).
* Order: 6 = `order(broom₃) + order(cherry) + 1 = 3 + 2 + 1`.
* σ: 1 (children are distinct, so no symmetry factor).
* 10th data point in the cycle 366 §G Route B hypothesis ladder.

**Predicted closed form** (extrapolating cycles 371/372/384):

* Leading term: `+v⁶` (order-6 even parity, sign positive).
* Self-term: `−Φ_η(mk [broom₃, cherry])`.
* Number of distinct elementary-weight kernels: 7–8.
* Anticipated new kernels: possibly `mk [vertex, broom₃]` (the
  block-(4) cross-term analogue of cycle 384's surprise).
* Number of terms in the polynomial: 10–12.

**Proof template**: cycle 384's recipe (lines 4680–4961) with the
binary product over `(broom₃, cherry)` instead of `(cherry, cherry)`.
The asymmetric child types mean:

* No squaring shortcut — both factor unfolds differ.
* Inner cherry-factor handled via cycle 367's `h_dws_cherry`.
* Inner broom₃-factor handled via cycle 368's `h_dws_broom₃` (or its
  derivative; cycle 371 already exercised this for the
  single-child case `mk [broom₃]`).

**LOC budget**: ~250 LOC (one closed-form theorem + m=0 corollary +
non-vacuity at `⟦explicitEuler⟧`).

**Alternative target** (if cycle 386 has slack): also ship
`mk [cherry, broom₃]` as the R2 symmetry-pair check. ~100 LOC
additional (the proof is identical modulo factor reordering).

## §8 Cross-references

### Predecessor scoping docs (in chronological order)

* `.prover-state/issues/def_422B_path.md` (cycle 336) — overall
  `def:422B` Phases A–E roadmap.
* `.prover-state/issues/def_422B_phase_D_3_scoping.md` (cycle 357) —
  Phase D.3 sub-phases.
* `.prover-state/issues/def_422B_subLemmaA_inductive_plan.md` (cycle
  373) — Sub-lemma A inductive plan; precedent for markdown-only
  scoping cycle.
* `.prover-state/issues/def_422B_phase_alpha_prime_scoping.md` (cycle
  379) — Phase α' recursive `inversePolynomial` design; direct
  predecessor for this Family C narrowing.

### Lean ship locations (cycles 371, 372, 384)

* `OpenMath/Chapter4/Section422.lean:3351–3624` —
  `elementaryWeightQ_phi_inv_mkBroom₃` (cycle 371).
* `OpenMath/Chapter4/Section422.lean:3748–4051` —
  `elementaryWeightQ_phi_inv_mkVertexCherry` (cycle 372).
* `OpenMath/Chapter4/Section422.lean:4603–4961` —
  `elementaryWeightQ_phi_inv_mkCherryCherry` (cycle 384).

### Phase α' shipped infrastructure

* `OpenMath/Chapter4/Section422.lean:5124–5400` (approx) — Phase α'.1
  `inversePolyChain` and calibration theorems (cycle 380).
* `OpenMath/Chapter4/Section422.lean:5500–5700` (approx) — Phase α'.1
  Family A bridge migration (cycle 381).
* `OpenMath/Chapter4/Section422.lean:5800–6100` (approx) — Phase α'.3
  `inversePolyBroom` and calibration theorems (cycle 382), Family B
  bridge migration (cycle 383).

### Cycle 384 task results (entry-point reference)

* `.prover-state/task_results/cycle_384.md` §"Suggested next
  approach" — explicit endorsement of this scoping doc.
* `.prover-state/task_results/cycle_384.md` §"Discovery" — the
  cross-tree-shape dependency observation that motivates §3.2 R1.

### Source material

* `extraction/raw_text/ch04.txt:1148–1173` — Butcher §422 textbook
  source ("E group" and η_q derivation).
* `extraction/formalization_data/entities/def_422B.json` — entity
  metadata for `def:422B`.

### Memory cross-links

* `feedback_rootedtree_nested_induction.md` — Phase α'.4.1 will need
  this: `induction t` / `RootedTree.recOn` fail on nested
  inductives; use `mutual` block of theorems with constructor
  pattern matching.
* `feedback_planner_faithfulness_spotcheck.md` — Variant V4 must be
  spot-checked against all 9 shipped closed forms before α'.4.1
  ships.
* `feedback_simp_recursive_def_overunfolds.md` — Phase α'.4.1's
  calibration theorems must use targeted `rw [name-eq-thm-...]`
  rather than `simp [inversePolyTree, ...]`; the cycle 382
  Discovery applies verbatim to the new `inversePolyTree` def.

## §9 Self-reference

* Cycle 385 ships this doc as its sole deliverable (no Lean code).
* Cycle 386 ships the 10th-tree Family C witness per §7
  (`mk [broom₃, cherry]`, ~250 LOC).
* Cycle 386b (optional, if cycle 386 has slack) ships the symmetry
  pair `mk [cherry, broom₃]` per §6.2.
* Cycle 387 (or 388) ships Phase α'.4.1 — recursive `inversePolyTree`
  + `bichildPolynomial` helper.
* Cycle 388 (or 389) ships Phase α'.4.2 — Family C branch migration.
* Post-Phase α'.4: Phase α'.5 (k ≥ 3 children) per §4.3, then Phase
  β/γ extension to close the cycle 365 grandfathered sorry.

### §9.1 Success criteria (cycle 385)

* One new markdown file at
  `.prover-state/issues/def_422B_phase_alpha_prime_family_C_scoping.md`
  (this file).
* 400–600 lines covering §1–§9.
* All three Family C witnesses transcribed verbatim from
  Section422.lean cycles 371/372/384 (cross-checked against the
  theorem statements above).
* Cycle 386 entry point with concrete tree name and LOC budget.
* Zero Lean changes (`git diff --stat` should show only
  `.prover-state/` paths).
* `lean_status.json` `def:422B` row unchanged (status `partial`,
  `cycle_completed_at` updated to 385).
* §422 axiom-clean streak advances: 48 substantive + 1 doc → **48
  substantive + 2 doc** (cycles 336–385).

### §9.2 What this doc deliberately does NOT do

* Does NOT lock the exact Lean syntax of `inversePolyTree`. Cycle 386
  needs to ship its empirical witness first.
* Does NOT propose a single-cycle Lean implementation of the unified
  recursion. Phase α'.4.1 estimates 1–2 cycles minimum.
* Does NOT touch the cycle 365 grandfathered sorry. That closure is
  multi-cycle (Phase α'.4 + Phase α'.5 + Phase β/γ).
* Does NOT attempt the cycle 370 broom-family general theorem on
  `broomTree k`. Family B's general inductive form is deferred to
  post-Phase α'.4 (a parallel work track to Family C).
* Does NOT pivot to a fresh entity. The §422 streak is productive
  and compound momentum is on this track.

---

**End of scoping doc.** Cycle 385 ships this markdown file as its
sole deliverable; standard bookkeeping (task results, heartbeat,
history.jsonl) follows. No Lean code, no axioms, no sorry-count
changes. Cycle 386 enters per §7 above.
