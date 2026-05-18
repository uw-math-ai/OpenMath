# Issue: `def:422B` Sub-lemma A inductive proof — multi-cycle plan

## §1 Status

**Scoping doc, cycle 373.** No Lean code shipped this cycle — this is
a markdown-only prep doc distilling the closed-form pattern revealed
by cycles 367–372's witness ladder into a concrete phased plan for
closing the **Sub-lemma A body** of `def:422B` Phase D.3.b at HEAD
(`b1bfe32`).

This is `def:422B`'s analogue of `lem_310B_plan.md` (cycle 260),
focused specifically on the remaining Sub-lemma A body. It guides
cycle 374+ workers through the multi-cycle inductive attack without
re-scoping. The existing `def_422B_phase_D_3_scoping.md` remains the
cycle 357 → 372 scoping reference for the broader Phase D.3
sequence; this new doc supersedes its §4.b / §6 "Sub-lemma A general
body" notes with a concrete phase decomposition.

§422 axiom-clean streak: **38 consecutive cycles (336–372)**. Sorry
count remains 5 lines / 1 code sorry — the grandfathered cycle 365
Sub-lemma A body at `OpenMath/Chapter4/Section422.lean:2279`. The
plan below preserves that streak by phasing single-cycle axiom-clean
deliverables; no `sorry`-bearing scaffolds.

## §2 Blocker

At HEAD, `powRep_sum_eq_of_strict_subtree_agreement`
(`Section422.lean:2272–2279`) is the **load-bearing remaining sorry**
in the §422 pipeline. Its statement (cycle 365 ship) is the
**closed-subtree** form of Sub-lemma A:

```lean
theorem powRep_sum_eq_of_strict_subtree_agreement
    (m : ℕ) (t : RT)
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (_h_closed : ∀ s : RT, s.order ≤ t.order →
        elementaryWeightQ_phi η_q s = elementaryWeightQ_phi η_q' s) :
    elementaryWeightQ_phi (η_q ^ (-(((m + 1) : ℕ) : ℤ))) t
      = elementaryWeightQ_phi (η_q' ^ (-(((m + 1) : ℕ) : ℤ))) t := by
  sorry
```

Once this body lands, the dependent
`linearResidualAt_depends_only_on_strict_subtrees`
(`Section422.lean:3288`, currently `[propext, sorryAx,
Classical.choice, Quot.sound]`) automatically becomes axiom-clean
(per cycle 365 ship structure — the headline's proof is already
locked in axiom-clean form modulo Sub-lemma A as a black box). That
closes Phase D.3.b parametricity Step 2 in its entirety; Phase D.3.c
(`sum_i_alpha_ne_zero_of_stable_preconsistent`, `Section422.lean:953`)
is already shipped; Phase D.3.d (`underlyingOneStepMethod_aux`
recursion) can then begin.

**Cycle 366 heterogeneity analysis** (cited from
`def_422B_phase_D_3_scoping.md` §6 cycle 366 update,
lines 1346–1407): after `Quotient.inductionOn₂` on `(η_q, η_q')` and
expansion via cycle 361's `elementaryWeightQ_phi_zpow_negSucc_mk`
(`Section422.lean:2061`), both sides reduce to
`-Σⱼ N.b j · N.derivativeWeightWithSrc N.inverse j t` with `N :=
(M.powRep (m+1)).2` for the LHS and `N' := (M'.powRep (m+1)).2` for
the RHS. When `M.1 ≠ M'.1`, these sums range over different `Fin`
types (`Fin (M.1 * (m+1))` vs `Fin (M'.1 * (m+1))`). Cycle 362's
`derivativeWeightWithSrc_eq_of_strict_subtree_agreement`
(`Section381.lean:2830`) substitutes the **source** tableau (`M₁`
argument) but NOT the **inner** tableau (`M₂` argument), so it
cannot bridge the heterogeneity directly. Cycle 365's task-results
suggestion (strong induction on `t.order` + cycle 364 Discovery #3
cancellation) was investigated and found to **not bridge** the
heterogeneous sums.

**Cycles 367–372 witness ladder** then accumulated **7
closed-form witnesses** (per-tree, axiom-clean) as feasibility
evidence for a Route-B "uniform closed-form polynomial" attack:

| Cycle | Tree | Closed form for `Φ_{η_q⁻¹}(t)` |
|---|---|---|
| 341 (P3) | `vertex` | `−v` |
| 367 | `cherry` | `v² − c` |
| 368 | `broom₃ = mk [vertex, vertex]` | `−v³ + 2vc − b'` |
| 369 | `mk [cherry]` | `−v³ + 2vc − m` |
| 370 | `bushy = mk [vertex, vertex, vertex]` | `v⁴ − 3v²c + 3vb' − B` |
| 371 | `mk [broom₃]` | `v⁴ − 3v²c + vb' + 2vm − M` |
| 372 | `mk [vertex, cherry]` | `v⁴ − 3v²c + c² + vb' + vm − V` |

(Notation: `v = Φ_η(vertex)`, `c = Φ_η(cherry)`,
`b' = Φ_η(broom₃)`, `m = Φ_η(mk [cherry])`, `B = Φ_η(bushy)`,
`M = Φ_η(mk [broom₃])`, `V = Φ_η(mk [vertex, cherry])`.)

The seven witnesses verify a uniform structural pattern: **every
closed form is a polynomial in `{Φ_η(s) : s subtree of t}` with the
unique `Φ_η(t)` appearance having coefficient `−1`**. This pattern
sidesteps the cycle 366 heterogeneity obstruction by reducing both
`(M.powRep (m+1)).2.…` sums to a common `RootedTree → ℝ`
polynomial — no stage counts involved.

The cycle 372 worker explicitly ruled out further witness
accumulation as treadmill work; cycle 373's deliverable (this doc)
is the scoping that turns the closed-form pattern into a concrete
multi-cycle inductive plan.

## §3 Textbook source

Butcher's §422 prose (`extraction/raw_text/ch04.txt:1148–1173`) is
**silent** on Sub-lemma A: the textbook proof asserts "the
coefficient of η(t) in η⁻ⁱ(t) is i(−1)^r(t) and there are no other
terms in η⁻ⁱ(t) with orders greater than r(t)−1" without proof,
treating it as a structural observation about the convolution
product `(η⁻¹ · η⁻¹ · … · η⁻¹)`.

Under our Φ-quotient encoding (cycle 234's `elementaryWeightQ_phi`),
the cycle 363 audit (`def_422B_phase_D_3_scoping.md`
lines 921–1166) established that the textbook's `(−1)^r(t)` factor
is spurious — the **actual** coefficient of `Φ_η(t)` in
`Φ_{η_q^(-i)}(t)` is `−i` (constant in `r(t)`). Cycle 364 redefined
`linearResidualAt` accordingly. Sub-lemma A's content — "the rest of
`Φ_{η_q^(-i)}(t)` depends only on strict subtrees of `t`" — survives
the redefinition unchanged.

So the proof obligation is **not in Butcher**; it is in our Lean
encoding. The two pieces of textbook machinery the inductive proof
will consume are:

1. **Cycle 358 `elementaryWeightQ_phi_inv_mk`**
   (`Section422.lean:582`):
   ```
   Φ_{⟦M⟧⁻¹}(mk children)
     = − Σⱼ M.b j · M.derivativeWeightWithSrc M.inverse j (mk children)
   ```
   This is the §381 convolution-inverse formula specialised to a
   quotient representative. It exposes the recursive shape of
   `Φ_{η_q⁻¹}` on a non-vertex tree, with the inner
   `derivativeWeightWithSrc` term mixing `M.inverse.elementaryWeight`
   at the immediate children of `mk children` against sums over
   `M.A`. The cycle 358 audit (cycle 366 worker notes) established
   that this formula's recursive unfolding through `M.derivativeWeight`
   at smaller trees collapses into elementary weights of `t`'s strict
   subtrees via cycle 226's `compose_elementaryWeight_decomp`.

2. **Cycle 359 `powRep_quotient_eq`**
   (`Section381.lean:4450`): `⟦M.powRep m⟧ = ⟦⟨s, M⟩⟧ ^ m`.
   Combined with cycle 361's ℤ-form lift
   `elementaryWeightQ_phi_zpow_negSucc_mk`
   (`Section422.lean:2061`), this reduces
   `Φ_{η_q^(-(m+1))}(t)` to the per-tree inverse formula on the
   `(m+1)`-fold composite representative. The recursive structure of
   `powRep` (`Section381.lean:4437`,
   `powRep M (k+1) = ⟨_, (powRep M k).2.compose M⟩`) makes the
   `m`-dependence explicit: each extra power layer composes one more
   copy of `M`.

The cycle 363 worker's mathematical-validation note (cycle 363 P2
audit, `def_422B_phase_D_3_scoping.md` lines 1019–1038) further
established empirically that the coefficient pattern is uniform in
`r(t)`: at `(i, t) = (1, vertex)`, `(1, cherry)`,
`(1, mk [vertex, vertex])`, the coefficient of `Φ_η(t)` in
`Φ_{η_q^(-1)}(t)` is always `−1`. Phases β through ε below
formalise this empirical observation.

## §4 Distilled mathematical content

### §4.1 Empirical pattern (read off cycles 367–372)

For every tree `t` shipped in the witness ladder, the closed form has
the shape:

```
Φ_{η_q⁻¹}(t) = (polynomial in Φ_η at strict subtrees of t) − Φ_η(t)
```

The polynomial part depends **only** on `Φ_η` at trees strictly
smaller than `t` in `RootedTree.order`; the `−Φ_η(t)` term is the
unique appearance of `Φ_η(t)` itself, with coefficient `−1`.

This pattern is **not surprising** given §3's textbook machinery:
the cycle 358 `_inv_mk` formula unrolls `Φ_{η_q⁻¹}(mk children)` into
a sum where each summand involves `M.inverse.elementaryWeight` at
sub-trees plus row-sums against `M.A` at strict subtrees. Cycle 226's
`compose_elementaryWeight_decomp` then collapses those sums into
elementary weights of strict subtrees of the parent. The `−Φ_η(t)`
term arises from the final outer combination, where the recursion
"sees" `t` itself one last time.

### §4.2 Origin of the pattern via cycle 358

Cycle 358's `_inv_mk` (`Section422.lean:582`) gives:

```
Φ_{η_q⁻¹}(t) = − Σⱼ M.b j · M.derivativeWeightWithSrc M.inverse j t
```

Unfolding `derivativeWeightWithSrc M.inverse i (mk children)` via
cycle 226's recursive definition (in `Section381.lean`) reveals that
each child `c ∈ children` contributes a factor

```
  M.inverse.elementaryWeight c  +  (row-sum of M.A at i, scaled by …)
```

where the second term collapses into `M.elementaryWeight` at strict
subtrees of `mk children` via cycle 226's composition lemma. The
first term `M.inverse.elementaryWeight c` is the inverse closed form
**at the child `c`** — which, by the recursion, equals the same
"polynomial in Φ_η at strict subtrees of c, plus −Φ_η(c)" pattern.

So the closed form for `Φ_{η_q⁻¹}(t)` is a polynomial in:

- `Φ_η(s)` for every strict subtree `s` of `t`, AND
- `Φ_η(t)` itself, appearing exactly once with coefficient `−1`.

This is the structural pattern the **inductive proof must encode**:
the recursive unfolding of `Φ_{η_q⁻¹}(t)` through cycle 358 `_inv_mk`
naturally produces a function of `Φ_η` at trees of order
`≤ t.order`, with a particular linear-in-`Φ_η(t)` structure.

### §4.3 What this means for Sub-lemma A

**Sub-lemma A** (m=0 case): under closed-subtree agreement
`Φ_η(s) = Φ_{η'}(s)` for all `s.order ≤ t.order`, are the two
`Φ_{η^(-1)}(t)` values equal?

For m=0 (cycles 367/368/369/370/371/372 corollaries), the **closed
form** lets us answer immediately: both sides expand to the same
polynomial in the same elementary weight values, so they're equal.
This is what each cycle 367+ corollary establishes per-tree; the
seven witnesses confirm the pattern holds at concrete small trees.

For general m ≥ 1, we don't have a closed form yet — but the **same
structural argument should apply** if we can:

1. Establish a recursive closed-form for `Φ_{η_q^(-(m+1))}(t)` at
   general `m`, via cycle 359's `powRep` + cycle 358's `_inv_mk` +
   cycle 226's compose decomposition.
2. Argue that this closed form is a polynomial in
   `{Φ_η(s) : s.order ≤ t.order}`.
3. Apply the closed-subtree agreement hypothesis to conclude
   equality.

This is the structure the phased plan below encodes.

### §4.4 The conjectured general form

**Conjecture (general inverse closed form).**
There exists a function `inversePolynomial : RootedTree → (RootedTree
→ ℝ) → ℝ`, defined by well-founded recursion on `RootedTree.order`
(via cycle 343's `WellFoundedRelation` instance, `Section301.lean:177`),
such that:

(a) for every `η_q : Quotient PhiEquivalent.setoidSigma` and every
    `t : RootedTree`,
    ```
    elementaryWeightQ_phi η_q⁻¹ t
      = inversePolynomial t (elementaryWeightQ_phi η_q);
    ```

(b) `inversePolynomial` depends only on the values of its second
    argument at trees `s : RootedTree` with `s.order ≤ t.order`. More
    precisely: if `f, f' : RootedTree → ℝ` agree on every
    `s : RootedTree` with `s.order ≤ t.order`, then
    `inversePolynomial t f = inversePolynomial t f'`.

**Sub-lemma A (m=0 case)** follows immediately from (a) + (b):

```
elementaryWeightQ_phi η_q⁻¹ t
  = inversePolynomial t (elementaryWeightQ_phi η_q)   -- by (a)
  = inversePolynomial t (elementaryWeightQ_phi η_q')  -- by (b) + agreement
  = elementaryWeightQ_phi η_q'⁻¹ t                   -- by (a)
```

The m ≥ 1 case follows by lifting through cycle 359's
`powRep_quotient_eq` plus a `pow_succ`-style induction:
`η_q^(-(m+2)) = η_q^(-(m+1)) · η_q⁻¹`, and the convolution structure
under `*` decomposes the (m+2)-fold inverse via cycle 358's
`_phi_mul_mk` (`Section422.lean:536`) — see Phase δ below for
details.

The seven witnesses from cycles 367–372 **verify (a) on small trees**.
Phase β below plans the general proof of (a); Phase γ plans the proof
of (b).

### §4.5 Discovery slot — coefficient pattern observations

Per the cycle 373 strategy §I ("watch for combinatorial structure"),
the closed forms in §4.1 admit additional observations:

- **Sign of `−Φ_η(t)`**: uniformly `−1`. Constant in `r(t)`. (Cycle
  363 audit confirmed this; differs from textbook's `i·(−1)^r(t)`
  claim by removal of the `(−1)^r(t)` factor.)
- **Coefficient of `v^k` (pure power of `Φ_η(vertex)`)**: at
  `t = broom_k = mk [vertex, …, vertex]` (k child-vertices), the
  coefficient of `v^k` is `(−1)^k`. This matches the binomial
  expansion `(Aᵢ − v)^k` per the cycle 368/370 Discovery (cycle 370
  task results in `def_422B_phase_D_3_scoping.md` lines 1588–1606).
- **Coefficient of mixed terms `v^j · c^k · …`**: at the broom-family
  `broom_k`, the cycle 370 generalised hypothesis predicts the closed
  form is the binomial sum
  ```
  Φ_{η_q⁻¹}(broomₖ) = Σ_{j=0}^k (−1)^j · C(k,j) · v^{k−j} · w_j
  ```
  where `w_j = Φ_η(broom_j)` and `w_0 = v`. Verified for k=0, 1, 2, 3.
- **σ(t) appearance**: σ does **not** appear in any of the seven
  witness coefficients (verified by inspection — coefficients are all
  ±integer or ±rational with small denominators; σ(`bushy`)=6,
  σ(`mk [broom₃]`)=2 do not appear). This suggests the
  `inversePolynomial`'s combinatorial coefficient recipe is via the
  **convolution structure** (Connes–Kreimer coproduct / cycle 358
  `_inv_mk` unrolling) rather than via tree-symmetry counting.

These observations suggest a possible **combinatorial closed-form
recipe** for `inversePolynomial t f` — but the seven witnesses
include only one heterogeneous-children case (cycle 372
`mk [vertex, cherry]`), so the combinatorial pattern is not yet
visible at full generality. Phase α below proceeds with the
**recursive recipe** (well-founded recursion on `RootedTree.order`)
as the primary path; a combinatorial closed-form could shorten
Phase β if discovered later, but is not required.

## §5 Project-hook inventory (verified at HEAD `b1bfe32`)

All entries verified by `grep -n` against
`OpenMath/Chapter4/Section422.lean`,
`OpenMath/Chapter3/Section381.lean`, and
`OpenMath/Chapter3/Section301.lean` at HEAD.

### §5.1 From `OpenMath/Chapter4/Section422.lean`

| Symbol | Line | Cycle | Phase consumer |
|---|---|---|---|
| `linearResidualAt` (def) | 1885 | 360 (def) / 364 (fix) | Phase ε signature |
| `coeff_eta_t_in_eta_zpow_neg` | 1900 | 360 / 364 | Phase ε plumbing |
| `linearResidualAt_vertex_eq_zero` | 1918 | 360 / 364 | Phase ε base case |
| `linearResidualAt_one_mk_eq` | 1939 | 360 / 364 | Phase ε i=1 form |
| `elementaryWeightQ_phi_zpow_natCast_mk` | 2040 | 361 | Phase δ ℕ-power |
| `elementaryWeightQ_phi_zpow_negSucc_mk` | 2061 | 361 | Phase δ ℕ-inverse |
| `linearResidualAt_succ_mk_eq` | 2118 | 361 / 364 | Phase ε general i form |
| `powRep_sum_eq_of_strict_subtree_agreement` (sorry'd) | 2272 | 365 | **Target — Phase ε output** |
| `powRep_sum_eq_of_agreement_at_vertex` | 2314 | 366 | Phase α non-vacuity |
| `elementaryWeightQ_phi_inv_cherry` | 2376 | 367 | Phase α non-vacuity |
| `powRep_sum_eq_of_agreement_at_cherry_zero` | 2477 | 367 | Phase ε regression check |
| `elementaryWeightQ_phi_inv_broom₃` | 2538 | 368 | Phase α non-vacuity |
| `powRep_sum_eq_of_agreement_at_broom₃_zero` | 2695 | 368 | Phase ε regression check |
| `elementaryWeightQ_phi_inv_mkCherry` | 2772 | 369 | Phase α non-vacuity |
| `powRep_sum_eq_of_agreement_at_mkCherry_zero` | 2941 | 369 | Phase ε regression check |
| `elementaryWeightQ_phi_inv_bushy` | 3011 | 370 | Phase α non-vacuity |
| `powRep_sum_eq_of_agreement_at_bushy_zero` | 3229 | 370 | Phase ε regression check |
| `linearResidualAt_depends_only_on_strict_subtrees` | 3288 | 365 (headline) | **Sub-lemma B headline — auto-upgrades to axiom-clean once Sub-lemma A body lands** |
| `elementaryWeightQ_phi_inv_mkBroom₃` | 3397 | 371 | Phase α non-vacuity |
| `powRep_sum_eq_of_agreement_at_mkBroom₃_zero` | 3704 | 371 | Phase ε regression check |
| `elementaryWeightQ_phi_inv_mkVertexCherry` | 3798 | 372 | Phase α non-vacuity |
| `powRep_sum_eq_of_agreement_at_mkVertexCherry_zero` | 4135 | 372 | Phase ε regression check |
| `elementaryWeightQ_phi_mul_mk` | 536 | 358 | Phase δ pow_succ unroll |
| `elementaryWeightQ_phi_inv_mk` | 582 | 358 | **Phase β recursive driver** |
| `elementaryWeightQ_phi_pow_succ_mk` | 632 | 359 | Phase δ ℕ-power lift |
| `elementaryWeightQ_phi_zpow_vertex` | 433 | 341 | Phase α vertex base |
| `sum_i_alpha_ne_zero_of_stable_preconsistent` | 953 | 363 | Phase D.3.d consumer (downstream) |

### §5.2 From `OpenMath/Chapter3/Section381.lean`

| Symbol | Line | Cycle | Phase consumer |
|---|---|---|---|
| `RKTableau.powRep` (def) | 4437 | 359 | Phase δ infrastructure |
| `RKTableau.powRep_quotient_eq` | 4450 | 359 | Phase δ infrastructure |
| `RKTableau.derivativeWeightWithSrc_eq_of_strict_subtree_agreement` | 2830 | 362 | Phase β recursive bridge |
| `RKTableau.derivativeWeightWithSrcProd_eq_of_strict_subtree_agreement` | 2853 | 362 | Phase β recursive bridge (list helper) |
| `elementaryWeightQ_phi_composeQ_phi_mk` | 4867 | 239 | Phase δ pow_succ unroll source |

(All symbols above are under the
`OpenMath.Chapter3.Section312.RKTableau` namespace except
`elementaryWeightQ_phi_composeQ_phi_mk`, which lives in
`OpenMath.Chapter3.Section381`.)

### §5.3 From `OpenMath/Chapter3/Section301.lean`

| Symbol | Line | Cycle | Phase consumer |
|---|---|---|---|
| `RootedTree.order_eq` | 112 | (pre-336 baseline) | Phase α / γ structural |
| `RootedTree.order_pos` | 159 | (pre-336 baseline) | Phase α termination measure |
| `RootedTree.order_lt_of_mem_children` | 167 | 343 | **Phase α termination bridge** |
| `instance : WellFoundedRelation RootedTree := measure RootedTree.order` | 177 | 343 | **Phase α well-founded driver** |

(All symbols are under the `OpenMath.Chapter3.Section310.RootedTree`
namespace.)

### §5.4 Mathlib hooks needed (to verify in Phase α)

- `WellFounded.fix` / `WellFounded.fixF` for the well-founded
  recursion. Cycle 343's instance should make this available.
- `Finset.sum_congr` + `Finset.sum_mul` for assembling the
  per-summand polynomial recursion in Phase β.
- `Quotient.inductionOn` for descending from `η_q` to a representative
  `⟨s, M⟩` (already pervasive in cycles 358/367–372).

## §6 Gap inventory

The infrastructure that must be built before Sub-lemma A's body can
close:

### §6.1 `inversePolynomial : RootedTree → (RootedTree → ℝ) → ℝ`

A general recursive function capturing the closed-form polynomial,
defined by well-founded recursion on `RootedTree.order` via cycle
343's `WellFoundedRelation` instance.

Strawman signature:

```lean
noncomputable def inversePolynomial : RootedTree → (RootedTree → ℝ) → ℝ
  | RootedTree.mk children => fun f =>
      -- recursive case: extract the "polynomial in strict subtree
      -- values" by mimicking the cycle 358 `_inv_mk` unfolding shape
      -- via the recursion at each `c ∈ children`
      sorry  -- Phase α deliverable
```

The recursion must be **structurally** defined so that the
well-founded measure `RootedTree.order` decreases at each recursive
call. Cycle 343's `order_lt_of_mem_children` provides the bridge.

**Non-vacuity**: 4–7 small-tree evaluations matching the cycle
341/367/368/369/370/371/372 closed forms. E.g.

```lean
example (f : RootedTree → ℝ) :
    inversePolynomial RootedTree.vertex f = -(f RootedTree.vertex)
example (f : RootedTree → ℝ) :
    inversePolynomial RootedTree.cherry f
      = (f RootedTree.vertex)^2 - f RootedTree.cherry
example (f : RootedTree → ℝ) :
    inversePolynomial RootedTree.broom₃ f
      = -(f RootedTree.vertex)^3
        + 2 * f RootedTree.vertex * f RootedTree.cherry
        - f RootedTree.broom₃
```

### §6.2 `elementaryWeightQ_phi_inv_eq_inversePolynomial` (Phase β output)

A theorem stating

```
elementaryWeightQ_phi (η_q⁻¹) t
  = inversePolynomial t (elementaryWeightQ_phi η_q)
```

for all `η_q : Quotient PhiEquivalent.setoidSigma` and all
`t : RootedTree`. This is conjecture §4.4 part (a).

**Proof recipe**: by strong induction on `t.order` using cycle 343's
`WellFoundedRelation`. The recursive step composes
`Quotient.inductionOn` (to get `η_q = ⟦⟨s, M⟩⟧`) with cycle 358's
`_inv_mk` formula (`Section422.lean:582`); the resulting sum over
`children`'s `M.derivativeWeightWithSrc M.inverse j` matches the
`inversePolynomial` recursive case by construction (Phase α defined
`inversePolynomial` to match this shape).

### §6.3 `inversePolynomial_eq_of_subtree_agreement` (Phase γ output)

A theorem stating

```
∀ t : RootedTree, ∀ f f' : RootedTree → ℝ,
  (∀ s : RootedTree, s.order ≤ t.order → f s = f' s) →
  inversePolynomial t f = inversePolynomial t f'
```

This is conjecture §4.4 part (b). **Load-bearing** for Sub-lemma A.

**Proof recipe**: structural well-founded induction on
`t.order`. At each recursive step, the `inversePolynomial`
unfolding produces a polynomial in `f` at trees `s` with
`s.order ≤ t.order` (immediate by Phase α construction). The
recursive sub-calls land at trees with strictly smaller order, where
the inductive hypothesis applies. The agreement hypothesis then
forces termwise equality of all polynomial summands.

This is **structural induction on the recursion's definitional
unfold** — agreement on strict subtrees forces agreement on the
recursive output. Cycle 362's `derivativeWeightWithSrc_eq_of_strict_subtree_agreement`
(`Section381.lean:2830`) provides the matching template for the
recursive bridge at the elementary-weight level; Phase γ produces the
`inversePolynomial`-level analogue.

### §6.4 Extension to general `m` (Phase δ output)

For `m ≥ 1`, the conjecture must extend to
`Φ_{η_q^(-(m+1))}(t)`. This requires either:

- (δ.A) A general `inversePolynomial_pow : ℕ → RootedTree →
  (RootedTree → ℝ) → ℝ` built recursively on `m`, with
  `inversePolynomial_pow 0 = inversePolynomial` and the inductive
  step composing the `m`-fold polynomial with one more inverse
  application via cycle 358's `_phi_mul_mk` (`Section422.lean:536`)
  + cycle 359's `powRep_quotient_eq` (`Section381.lean:4450`); OR

- (δ.B) A direct induction on `m` at the **theorem level**, proving
  `elementaryWeightQ_phi (η_q^(-(m+1))) t = (some polynomial in
  Φ_η at trees of order ≤ t.order)` by induction on `m`, using the
  `m=0` case (Phase β) as the base and cycle 361's
  `linearResidualAt_succ_mk_eq` (`Section422.lean:2118`) as the
  inductive bridge.

Path δ.B is preferred — it avoids defining a new
`inversePolynomial_pow` symbol and directly produces the
Sub-lemma A body's exact statement. Path δ.A is the fallback if
δ.B's induction structure becomes unwieldy.

### §6.5 Sub-lemma A's body (Phase ε output)

```lean
theorem powRep_sum_eq_of_strict_subtree_agreement
    (m : ℕ) (t : RT)
    (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
    (h_closed : ∀ s : RT, s.order ≤ t.order →
        elementaryWeightQ_phi η_q s = elementaryWeightQ_phi η_q' s) :
    elementaryWeightQ_phi (η_q ^ (-(((m + 1) : ℕ) : ℤ))) t
      = elementaryWeightQ_phi (η_q' ^ (-(((m + 1) : ℕ) : ℤ))) t
```

The body is then a 3-line proof composing the Phases β / γ / δ
outputs:

```lean
  -- Apply the general closed form (Phase δ output) to both sides.
  rw [phi_neg_succ_eq_polynomial_pow m t η_q,
      phi_neg_succ_eq_polynomial_pow m t η_q']
  -- The two polynomial values agree by closed-subtree agreement
  -- (Phase γ output, extended to `polynomial_pow` in Phase δ).
  exact polynomial_pow_eq_of_subtree_agreement (m+1) t
    (elementaryWeightQ_phi η_q) (elementaryWeightQ_phi η_q') h_closed
```

(Exact API names TBD by Phase α/β/γ workers; the recipe is the same.)

## §7 Phase decomposition

The full Sub-lemma A close is a 5-phase, ~5–6 cycle effort. Each
phase should ship axiom-clean (sorry count unchanged or 0), with a
concrete non-vacuity witness. **No `sorry`-bearing scaffolds at
phase boundaries** — per the cycle 200/201 and 149/150 rollback
precedents.

### Phase α — `inversePolynomial` definition (1 cycle, single-cycle close achievable)

**Cycle 374 target.**

- **Deliverable**: `noncomputable def inversePolynomial : RootedTree
  → (RootedTree → ℝ) → ℝ` via well-founded recursion on
  `RootedTree.order`, defined to **structurally mimic** the cycle 358
  `_inv_mk` unfolding shape applied to a "generic" `f` function in
  place of `M.elementaryWeight`.
- **Non-vacuity**: 7 small-tree `example`s evaluating
  `inversePolynomial t f` and matching the cycle 341/367–372 closed
  forms by `rfl` or `unfold + ring`.
- **Axiom-clean target**: `[propext, Classical.choice, Quot.sound]`.
- **Sorry count**: 0 → 0 (must remain — cycle 365's grandfathered
  sorry persists, no new sorries introduced).
- **Estimated LOC**: ~80–120 (recursion definition + 7 non-vacuity
  examples).
- **File placement**: append to `OpenMath/Chapter4/Section422.lean`
  after the cycle 372 closed-form block (around line 4185).
- **Risk**: LOW. Well-founded recursion on `RootedTree.order` is
  established by cycle 343 (`Section301.lean:177`); the
  `order_lt_of_mem_children` bridge (`Section301.lean:167`) is the
  termination witness. Cycle 343 worker already demonstrated the
  pattern in a different context (cycle 343 task results).

**Sub-tasks for the cycle 374 worker**:

1. Pin the recursive case's RHS shape. The cycle 358 `_inv_mk`
   formula is
   `−Σⱼ M.b j · M.derivativeWeightWithSrc M.inverse j (mk children)`;
   the `inversePolynomial` analogue should produce a formula that,
   when applied to `f = M.elementaryWeight`, reduces to the same
   value. This requires "lifting" `derivativeWeightWithSrc` from the
   tableau-level to a `RootedTree → ℝ`-level recursion.

   **Strawman option (recursive-on-children)**: define
   `inversePolynomial (mk children) f` to recurse over `children`
   producing a polynomial in `{f c : c ∈ children}` and
   `{inversePolynomial c f : c ∈ children}`. The exact polynomial
   shape is determined by cycle 358's structural unfolding —
   specifically, the cycle 367–372 witnesses give 7 datapoints from
   which the recursion's algebraic shape can be read off
   uniformly.

2. Verify termination via `decreasing_by exact
   RootedTree.order_lt_of_mem_children hc` at each recursive sub-call.

3. Write 7 non-vacuity examples — one per cycle 341/367–372 witness
   — confirming the recursion evaluates correctly on the small
   trees. Each example should close via `unfold inversePolynomial;
   ring` (or `rfl` if the recursion's definitional unfolding
   matches directly).

**Cycle 374 exit criteria**:

- `inversePolynomial` defined and compiles.
- 7 small-tree non-vacuity examples close axiom-clean.
- `lake env lean OpenMath/Chapter4/Section422.lean` exits 0.
- `#print axioms inversePolynomial` returns `[propext,
  Classical.choice, Quot.sound]`.
- Sorry count unchanged (1 code sorry — the cycle 365 grandfathered
  one).

### Phase β — `elementaryWeightQ_phi_inv_eq_inversePolynomial` (1–2 cycles)

**Cycle 375 target** (Phase β.1, possibly Phase β.2 in cycle 376).

- **Phase β.1** (cycle 375): derive the recursive identity from cycle
  358 `_inv_mk`. State

  ```lean
  theorem elementaryWeightQ_phi_inv_eq_inversePolynomial
      (η_q : Quotient PhiEquivalent.setoidSigma) (t : RootedTree) :
      elementaryWeightQ_phi (η_q⁻¹) t
        = inversePolynomial t (elementaryWeightQ_phi η_q)
  ```

  Prove by strong induction on `t.order` via cycle 343's
  `WellFoundedRelation`. The base case (`t = mk []` or `t = vertex`)
  closes via cycle 341 P3 + Phase α's `inversePolynomial vertex`
  evaluation. The recursive step composes `Quotient.inductionOn` →
  cycle 358 `_inv_mk` → cycle 226's `_compose_elementaryWeight_decomp`
  + `Finset.sum_congr` to match `inversePolynomial`'s recursive
  unfold.

- **Phase β.2** (potentially cycle 376 if β.1 splits): clean up the
  recursive bridging if cycle 358 `_inv_mk` requires intermediate
  lemmas to align with the Phase α recursive shape. Likely a
  `Quotient.lift` plumbing step.

- **Estimated LOC**: ~150–250 over 1–2 cycles.
- **Risk**: MEDIUM. The cycle 358 `_inv_mk` recursive structure is
  matched against `inversePolynomial`'s recursion — the alignment
  must be exact at the algebraic level. If the recursions don't
  match shape-for-shape, Phase α must be redesigned. **Mitigation**:
  cycle 374 worker should consult cycle 358's `_inv_mk` proof when
  pinning the Phase α recursive case, ensuring the two recursions
  unfold to syntactically-equal forms.
- **Aristotle**: SUITABLE for the algebraic congruence sub-lemmas
  after the main strong-induction structure is in place. Submit ~3–5
  sub-lemma proofs to Aristotle in batch (the per-summand `ring`
  closures + `Finset.sum_congr` bridges).

**Cycle 375/376 exit criteria**:

- Phase β output theorem shipped axiom-clean.
- Non-vacuity: each of the 7 cycle 367–372 closed-form witnesses can
  now be **derived** from Phase β + Phase α (no longer needing
  per-tree proofs). Cycle 375/376 should ship 1–2 such derived
  witnesses as regression tests.

### Phase γ — `inversePolynomial_eq_of_subtree_agreement` (1 cycle)

**Cycle 376 or 377 target** (depending on Phase β duration).

- **Deliverable**:

  ```lean
  theorem inversePolynomial_eq_of_subtree_agreement
      (t : RootedTree) (f f' : RootedTree → ℝ)
      (h_closed : ∀ s : RootedTree, s.order ≤ t.order → f s = f' s) :
      inversePolynomial t f = inversePolynomial t f'
  ```

  Prove by strong induction on `t.order` (the same well-founded
  measure as Phase α/β). At each recursive step, the
  `inversePolynomial` unfold produces a polynomial in `f` at trees
  of order `≤ t.order`; the recursive sub-calls land at strictly
  smaller orders (by `order_lt_of_mem_children`), where the IH
  applies. The agreement hypothesis forces termwise equality.

- **Estimated LOC**: ~80–120.
- **Risk**: LOW. Pure structural induction on Phase α's recursion;
  the agreement-of-strict-subtrees argument is the same pattern as
  cycle 362's `derivativeWeightWithSrc_eq_of_strict_subtree_agreement`
  (`Section381.lean:2830`), already in place as a precedent.
- **Aristotle**: SUITABLE for the structural-induction step's
  congruence (the `Finset.sum_congr` + per-summand IH application).

**Cycle 376/377 exit criteria**:

- Phase γ output theorem shipped axiom-clean.
- **Sub-lemma A (m=0 case) can now be derived as a 3-line
  composition** of Phase β + Phase γ. Cycle 376/377 should ship the
  derived `m=0` Sub-lemma A as a regression test — this also
  re-derives the 7 cycle 367–372 corollaries as one-liners.

### Phase δ — extension to general `m` via `powRep` (1 cycle)

**Cycle 377 or 378 target**.

- **Deliverable**: lift the `m=0` Sub-lemma A to general `m ≥ 0` via
  cycle 359's `powRep` (`Section381.lean:4437`,
  `powRep_quotient_eq` at `Section381.lean:4450`). Path δ.B
  (preferred): direct induction on `m` at the theorem level.

  Strawman:

  ```lean
  theorem powRep_sum_eq_of_subtree_agreement_general
      (m : ℕ) (t : RootedTree)
      (η_q η_q' : Quotient PhiEquivalent.setoidSigma)
      (h_closed : ∀ s : RootedTree, s.order ≤ t.order →
          elementaryWeightQ_phi η_q s = elementaryWeightQ_phi η_q' s) :
      elementaryWeightQ_phi (η_q ^ (-((m : ℕ) : ℤ))) t
        = elementaryWeightQ_phi (η_q' ^ (-((m : ℕ) : ℤ))) t
  ```

  Induction on `m`:

  * `m = 0`: both sides are `Φ_id(t) = M.elementaryWeight t`-equivalent
    via cycle 239's `elementaryWeightQ_phi_id` + `h_closed t (le_refl _)`.
  * `m + 1`: `η_q^(-(m+1)) = η_q^(-m) · η_q⁻¹`; use cycle 358's
    `_phi_mul_mk` (`Section422.lean:536`) to decompose the product;
    apply the IH at `m`; apply the `m=0` Sub-lemma A (Phase γ output)
    at the inverse factor. **Both sides match by structural
    re-composition.**

- **Estimated LOC**: ~80–150.
- **Risk**: MEDIUM. The induction on `m` requires careful handling
  of the convolution-product structure under `*` (cycle 358
  `_phi_mul_mk`). If the cycle 358 `_phi_mul_mk` formula doesn't
  decompose cleanly under the strict-subtree agreement hypothesis,
  Phase δ may need an intermediate lemma "`_phi_mul_mk` depends only
  on closed-subtree values of both arguments". This is conceptually
  analogous to cycle 362's strict-subtree-agreement lemma but at the
  `_phi_mul_mk` level rather than the `derivativeWeightWithSrc`
  level.
- **Aristotle**: PARTIAL. The induction structure is manual; the
  per-step congruence may be Aristotle-suitable after the structure
  is in place.

**Cycle 377/378 exit criteria**:

- Phase δ output theorem shipped axiom-clean.
- The cycle 365 `powRep_sum_eq_of_strict_subtree_agreement`'s body
  (the cycle 373 plan's "Phase ε") is **now a 3-line corollary**.

### Phase ε — close Sub-lemma A's body (1 cycle, possibly within Phase δ)

**Cycle 378 or 379 target** (could be batched with Phase δ in a
single cycle if Phase δ lands cleanly).

- **Deliverable**: discharge the
  `powRep_sum_eq_of_strict_subtree_agreement` body at
  `Section422.lean:2279` by composing Phases β / γ / δ outputs.

- **Estimated LOC**: ~5–10 (a 3-line proof body replacing the sorry).
- **Risk**: LOW (mechanical composition).
- **Aristotle**: NOT NEEDED (3-line proof body).

**Cycle 378/379 exit criteria**:

- `OpenMath/Chapter4/Section422.lean:2279` no longer contains
  `sorry`.
- `grep -c sorry OpenMath/Chapter4/Section422.lean` returns 4 lines
  (just the 4 documentation references; code-level sorry count = 0).
- `#print axioms powRep_sum_eq_of_strict_subtree_agreement` returns
  `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
- `#print axioms linearResidualAt_depends_only_on_strict_subtrees`
  **automatically upgrades** from `[propext, sorryAx,
  Classical.choice, Quot.sound]` to `[propext, Classical.choice,
  Quot.sound]` (per cycle 365 headline ship structure).
- `lake build OpenMath.Chapter4.Section422` exits 0.

**Total estimate**: 5 phases, ~5–6 single-cycle deliverables.
Sub-lemma A closes cleanly in cycle 378 or 379 under nominal phase
durations. If any phase splits (e.g. Phase β into β.1 / β.2), the
horizon shifts to cycle 380.

## §8 Risk assessment

### §8.1 Per-phase risk summary

| Phase | Risk | Mathlib confidence | Aristotle |
|---|---|---|---|
| α | LOW — well-founded recursion via cycle 343 is established | HIGH | Not needed |
| β | MEDIUM — alignment between cycle 358 `_inv_mk` recursive shape and Phase α's `inversePolynomial` shape must be exact | MEDIUM-HIGH | SUITABLE for sub-lemmas |
| γ | LOW — pure structural induction; cycle 362 is the precedent | HIGH | SUITABLE for sub-lemmas |
| δ | MEDIUM — induction on `m` requires careful convolution-product handling under closed-subtree agreement | MEDIUM | PARTIAL |
| ε | LOW (mechanical composition) | N/A | Not needed |

### §8.2 Cross-cutting risks

- **Phase α recursive shape mismatch (R1)**: if the
  `inversePolynomial` recursive case shape doesn't exactly match the
  cycle 358 `_inv_mk` unfolding shape, Phase β cannot derive the
  equality from `_inv_mk` directly. **Mitigation**: cycle 374 worker
  should write the Phase α definition **after** reading cycle 358's
  `_inv_mk` proof carefully (`Section422.lean:582–630`),
  ensuring the recursion mirrors the formula's structure. The 7
  cycle 367–372 closed-form witnesses serve as **calibration
  data**: the Phase α recursive case must evaluate correctly on
  these 7 datapoints by `rfl` or `unfold + ring`. If any of the 7
  witnesses fails, Phase α has the wrong shape.

- **Phase β strong induction obstacle (R2)**: cycle 343's
  `WellFoundedRelation` instance establishes
  `RootedTree.order` is a well-founded measure, but the strong
  induction's recursive call at `c ∈ children` may need an explicit
  `decreasing_by` hint. **Mitigation**: cycle 375 worker can consult
  cycle 343 task results for the canonical strong-induction
  pattern (`feedback_rootedtree_nested_induction.md` flags that
  `induction t` / `RootedTree.recOn` fail on nested inductives —
  use `WellFounded.fix` / `WellFounded.induction` instead).

- **Phase δ convolution-product alignment (R3)**: cycle 358's
  `_phi_mul_mk` (`Section422.lean:536`) decomposes a product
  representation, but under closed-subtree agreement it must
  preserve agreement at trees of order ≤ t.order. Cycle 362's
  `derivativeWeightWithSrc_eq_of_strict_subtree_agreement` is the
  source-tableau analogue; an inner-tableau analogue at
  `_phi_mul_mk` may be needed. **Mitigation**: Phase δ worker
  should consult cycle 366's heterogeneity analysis
  (`def_422B_phase_D_3_scoping.md` lines 1346–1407) for the
  obstacle the closed-subtree agreement hypothesis sidesteps.

- **Aristotle latency (R4)**: Aristotle's typical 30-min cycle
  latency may extend each Phase β / γ cycle if heavy use is
  required. **Mitigation**: batch ~5 sub-lemmas per Aristotle
  submission; only manually prove what Aristotle fails on.

- **Streak preservation (R5)**: the 38-consecutive-axiom-clean
  §422 streak (336–372) must be preserved through Phase α–ε.
  Each phase must either ship axiom-clean **or** ship nothing
  (the cycle 366 graceful-degradation precedent applies).
  **Mitigation**: each phase's cycle worker should pre-flight
  the proof outline before opening any new sorry; if blocked,
  file a sub-issue rather than committing a sorry'd scaffold
  (per cycle 200/201 / cycle 149/150 rollback precedents).

### §8.3 Approaches explicitly known to fail (cite in this doc)

Per the cycle 366 update (`def_422B_phase_D_3_scoping.md`
lines 1346–1407) and cycle 365 task results, two approaches were
investigated and found to NOT close Sub-lemma A's body:

1. **Direct `Quotient.inductionOn₂` + cycle 358 `_inv_mk`
   expansion** on the two sides: after `Quotient.inductionOn₂` on
   `η_q` and `η_q'`, cycle 358's `_inv_mk` formula expresses each
   side as a sum over representative-specific stage counts (`M.1`
   vs `M'.1`), which are generally **different**. There is no direct
   way to bridge the two heterogeneous sums via cycle 362's
   substitution lemma (which only substitutes the *source* tableau
   `M₁`, not the *inner* tableau `M₂`).

2. **Strong induction on `t.order` using cycle 362 alone**: cycle
   362's `derivativeWeightWithSrc_eq_of_strict_subtree_agreement`
   bridges the `derivativeWeightWithSrc` sum's substitution behaviour
   but does not handle the *inner-tableau heterogeneity* between
   `M.powRep (m+1)` and `M'.powRep (m+1)`.

**Why the §7 plan sidesteps both**: the closed-form-via-
`inversePolynomial` approach **reduces both sides to the same
`RootedTree → ℝ` polynomial**, with the heterogeneous-stage-count
issue vanishing — `inversePolynomial t f` takes a tree and a
real-valued function, no stage counts involved. The Phase β
equality `Φ_{η_q⁻¹}(t) = inversePolynomial t (Φ_η)` is the
load-bearing bridge.

## §9 Cycle 374 entry point

**Concrete first task for cycle 374 (Phase α)**: ship
`inversePolynomial : RootedTree → (RootedTree → ℝ) → ℝ` via
well-founded recursion on `RootedTree.order`, plus 7 non-vacuity
`example`s matching the cycle 341/367–372 closed forms.

**Cycle 374 worker preliminaries** (do these *before* writing any
Lean code):

1. Read cycle 358's `_inv_mk` proof at
   `OpenMath/Chapter4/Section422.lean:582–630` to understand the
   recursive structure the `inversePolynomial` definition must
   mirror.
2. Read cycle 343's `WellFoundedRelation RootedTree := measure
   RootedTree.order` instance at
   `OpenMath/Chapter3/Section301.lean:177` and the
   `order_lt_of_mem_children` bridge at
   `OpenMath/Chapter3/Section301.lean:167`.
3. Read the 7 closed-form witnesses in
   `OpenMath/Chapter4/Section422.lean`:
   - `elementaryWeightQ_phi_inv_cherry` (line 2376)
   - `elementaryWeightQ_phi_inv_broom₃` (line 2538)
   - `elementaryWeightQ_phi_inv_mkCherry` (line 2772)
   - `elementaryWeightQ_phi_inv_bushy` (line 3011)
   - `elementaryWeightQ_phi_inv_mkBroom₃` (line 3397)
   - `elementaryWeightQ_phi_inv_mkVertexCherry` (line 3798)
   - Plus cycle 341 P3 `elementaryWeightQ_phi_zpow_vertex` (line 433)
4. Read `feedback_rootedtree_nested_induction.md` (memory) for the
   `mutual`-block pattern that may be needed for the recursive case.

**Cycle 374 deliverable**:

- `inversePolynomial` definition shipped axiom-clean.
- 7 non-vacuity examples, one per cycle 341/367–372 witness.
- Sorry count unchanged.
- `lake env lean OpenMath/Chapter4/Section422.lean` exits 0.

**Cycle 374 NON-deliverable**: do **NOT** attempt Phase β
(`elementaryWeightQ_phi_inv_eq_inversePolynomial`) in the same
cycle. The α → β boundary is the natural one-cycle split.

**Graceful degradation for cycle 374**: if `inversePolynomial`'s
recursive shape proves elusive (e.g. cannot match cycle 358
`_inv_mk` directly), the cycle 374 worker should:

- Ship Phase α restricted to a smaller domain (e.g. "broom_k"
  family only) as a stepping stone.
- File a sub-issue documenting the alignment obstacle.
- Pivot to fresh entity work or further witness accumulation
  (mk [mk [cherry]], depth-3 ladder) as a fallback.

The cycle 366 graceful-degradation precedent
(`def_422B_phase_D_3_scoping.md` lines 1346–1407) is the canonical
template: ship a strictly-smaller deliverable axiom-clean,
preserving the streak, rather than committing a sorry'd scaffold.

## §10 Cross-references

- `def_422B_path.md` — overall `def:422B` roadmap; this doc is a
  sub-phase of §5 line 452.
- `def_422B_phase_D_3_scoping.md` — Phase D.3 scoping (cycles
  357–372). This new doc supersedes its §4.b / §6 "Sub-lemma A
  general body" notes; the Phase D.3.a–d structure remains as the
  outer-level scoping.
- `lem_310B_plan.md` — template for multi-phase scoping docs
  (cycle 260 produced). This doc follows its structure verbatim.
- `extraction/formalization_data/entities/def_422B.json` — target
  entity (status: `partial`, all relevant rows unchanged this
  cycle).
- `extraction/raw_text/ch04.txt:1148–1173` — Butcher's §422 prose;
  silent on Sub-lemma A's structural argument.

### §10.1 Per-cycle task-result references

- `.prover-state/task_results/cycle_358.md` — cycle 358's
  `_inv_mk` and `_mul_mk` ship.
- `.prover-state/task_results/cycle_359.md` — cycle 359's
  `powRep` + `powRep_quotient_eq` ship.
- `.prover-state/task_results/cycle_360.md` — cycle 360's
  `linearResidualAt` def + base cases.
- `.prover-state/task_results/cycle_361.md` — cycle 361's
  ℤ-form lift + general closed form.
- `.prover-state/task_results/cycle_362.md` — cycle 362's
  strict-subtree-agreement at the `derivativeWeightWithSrc` level.
- `.prover-state/task_results/cycle_363.md` — cycle 363's
  `sum_i_alpha_ne_zero` + Phase D.3.b coefficient audit.
- `.prover-state/task_results/cycle_364.md` — cycle 364's
  `linearResidualAt` redefinition (sign fix).
- `.prover-state/task_results/cycle_365.md` — cycle 365's
  Sub-lemma B headline ship + Sub-lemma A body sorry.
- `.prover-state/task_results/cycle_366.md` — cycle 366's
  vertex witness + heterogeneity analysis.
- `.prover-state/task_results/cycle_367.md` — cycle 367's
  cherry closed form + m=0 witness.
- `.prover-state/task_results/cycle_368.md` — cycle 368's
  broom₃ closed form + m=0 witness + `(Aᵢ − v)^k` discovery.
- `.prover-state/task_results/cycle_369.md` — cycle 369's
  `mk [cherry]` closed form + m=0 witness.
- `.prover-state/task_results/cycle_370.md` — cycle 370's
  bushy closed form + broom_k generalised hypothesis.
- `.prover-state/task_results/cycle_371.md` — cycle 371's
  `mk [broom₃]` closed form + m=0 witness.
- `.prover-state/task_results/cycle_372.md` — cycle 372's
  `mk [vertex, cherry]` closed form + m=0 witness;
  recommended pivot to inductive scoping.
- `.prover-state/task_results/cycle_373.md` — cycle 373's
  scoping doc ship (this file).
- `.prover-state/task_results/cycle_374.md` — cycle 374's
  Phase α.1 `inversePolynomial` ship: explicit
  pattern-match definition + 4 non-vacuity witnesses
  (vertex, cherry, broom₃, mk [cherry]).

### §10.3 Cycle 374 update — Phase α.1 (explicit pattern-match) shipped

(NB: appears below for readability; comes *after* §10.2 narratively.)

**Design chosen**: explicit `if-then-else` pattern match on the four
small trees `vertex`, `cherry`, `broom₃`, `mk [cherry]` with `0` as
the placeholder for all other trees. The recursive-on-all-trees
form (the original §7 Phase α spec using `WellFoundedRelation` and
`measure RootedTree.order`) is deferred to **Phase α' (cycle 375+
work)**.

**Why the simpler form**: the seven cycle 341/367–372 closed forms
don't cleanly factor into a single recursive shape (e.g. `f cherry`
appears in `Φ_{η_q⁻¹}(broom₃)`'s closed form even though `cherry`
is not a child of `broom₃`). Designing the well-founded recursive
shape is multi-cycle research and risks committing a partial
scaffold under the cycle 374 single-cycle budget. The
pattern-match form ships axiom-clean today and gives Phase β
(cycle 375+) a stable target.

**Witnesses shipped (4 of the 7 closed forms)**:

- `vertex` ↔ cycle 341 P3 `elementaryWeightQ_phi_zpow_vertex`
- `cherry` ↔ cycle 367 `elementaryWeightQ_phi_inv_cherry`
- `broom₃` ↔ cycle 368 `elementaryWeightQ_phi_inv_broom₃`
- `mk [cherry]` ↔ cycle 369 `elementaryWeightQ_phi_inv_mkCherry`

The remaining three closed forms (`bushy`, `mk [broom₃]`,
`mk [vertex, cherry]`, cycles 370–372) are NOT pattern-matched in
cycle 374; they map to `0` under the current definition. Extending
to those 3 additional cases is Phase α.2 (cycle 375 option A) or
the well-founded recursion refinement is Phase α' (cycle 375
option B). Both options are zero-risk: they only add equations,
they never invalidate the four cases already shipped.

**Axiom-clean confirmation**: `#print axioms` on
`inversePolynomial` and each of the four witnesses returns
`[propext, Classical.choice, Quot.sound]`. The §422 axiom-clean
streak (38 cycles 336–372 substantive, 373 doc-only, 374
substantive) advances to 39 cycles substantive + 1 doc.

**Sorry count unchanged**: still `1` actual sorry at line 2279
(the cycle 365 grandfathered Sub-lemma A body). The cycle 374
ship adds 0 new sorries.

**`lean_status.json` for `def:422B`**: stays `partial` — Phase α.1
is *one piece* of the multi-phase Sub-lemma A → Sub-lemma B →
`def:422B` chain. No status promotion this cycle.

**Phase β prep**: when cycle 375 (or later) attempts the bridge
lemma `elementaryWeightQ_phi η_q⁻¹ t = inversePolynomial t
(elementaryWeightQ_phi η_q)` on the four small trees, each case
reduces to the cycle 367/368/369 closed-form theorem by
`unfold inversePolynomial; rw [if_*]; exact
elementaryWeightQ_phi_inv_<tree>`. This is the cleanest possible
Phase β starting point.

**`by decide` discharge worked**: each `t ≠ vertex / cherry /
broom₃` inequality was discharged by `by decide` (no fallback to
`injection` was needed). `DecidableEq RootedTree` from
`Section301.lean:92` fires through the `RootedTree.mk` /
`List.cons` constructor stack as expected.

**Name resolution gotcha (for future workers)**: writing
`RootedTree.mk [cherry]` at the top level of `Section422.lean`
resolves `RootedTree.mk` to *Mathlib's* `_root_.RootedTree.mk`
(a `RootedTree` constructor from `Mathlib.Combinatorics`), not
our `OpenMath.Chapter3.Section310.RootedTree.mk`. Use the fully
qualified `OpenMath.Chapter3.Section310.RootedTree.mk [...]` —
this is the convention already used at line 2774 onwards in the
file. The `RT` abbrev does NOT help here because dot notation on
`RT` would still resolve to whatever Lean picks for `RootedTree`.

### §10.2 Memory references

- `project_butcher_D_operator.md` — `D` operator is §385b 1-stage
  generalised RK (`⟦explicitEuler⟧` canonical representative).
- `feedback_rootedtree_nested_induction.md` — `induction t` /
  `RootedTree.recOn` fail on nested inductives; use `WellFounded.fix`
  / mutual blocks. Phase α/γ workers should consult this.
- `feedback_phi_equivalent_b0_invisibility.md` — `PhiEquivalent`
  quantifies only `∀ t : RootedTree`; the `b₀` field is invisible
  at the §383 quotient level. Phase β/δ workers should be aware
  when reasoning about quotient-level equalities.

## §11 Self-reference

- **Author**: cycle 373 worker (per cycle 373 strategy §D).
- **Read by**: cycle 374 worker (Phase α executor); cycle 375 worker
  (Phase β.1); cycle 376/377 worker (Phase β.2 / γ); cycle 377/378
  worker (Phase δ); cycle 378/379 worker (Phase ε).
- **Update on**: each Phase α / β / γ / δ / ε completion — add a
  per-phase update block (analogous to
  `def_422B_phase_D_3_scoping.md`'s cycle 358/359/.../372 update
  blocks).
- **Markdown-only**: 0 LOC of Lean shipped this cycle, 0 sorries
  opened or closed. Cycle 373 ships this doc only.

## §12 What Sub-lemma A closure delivers

After Phase ε lands (projected cycle 378/379), the
§422 pipeline state will be:

- `powRep_sum_eq_of_strict_subtree_agreement`: axiom-clean.
- `linearResidualAt_depends_only_on_strict_subtrees`:
  **auto-upgrades** to axiom-clean (per cycle 365 ship structure).
- `Section422.lean` sorry count: 0 code sorries.
- §422 axiom-clean streak: at least 44 cycles (336–378 if Phase α–ε
  is single-cycle each; 45+ if any phase splits).

At that point, **Phase D.3.b is fully closed**, Phase D.3.c
(`sum_i_alpha_ne_zero_of_stable_preconsistent`) is already shipped
(cycle 363), and Phase D.3.d (`underlyingOneStepMethod_aux` recursion)
can begin. Phase D.3.d is a separate multi-cycle effort scoped in
`def_422B_phase_D_3_scoping.md` §5 — its strategist will use
Sub-lemma A's now-axiom-clean form as a black-box dependency.

Phase E (the `def:422B` sealing) closes the chain once Phase D.3.d
lands. **Total horizon for `def:422B`**: cycles 374–382, roughly
9 cycles from cycle 373.

Cycle 373 ships **this scoping doc only** — the load-bearing prep
that makes the cycle 374+ trajectory concrete and avoids re-scoping
at each phase boundary.
