# Issue: `def:422B` Phase α'.5.2 scoping — `tetrachildPolynomial` / `tetrachildCrossTerm` for k = 4 children

## §1 Status & blocker

**Scoping doc, cycle 498.** No Lean code shipped this cycle — this is a
markdown-only research doc that distills the cycle 497 worker's
findings (and the cycle 358 / 387 / 399 / 491–494 empirical surface)
into a concrete multi-cycle plan for extending `inversePolyTree`
from its current 5-arm pattern match (k ∈ {0, 1, 2, 3}, catch-all
k ≥ 4 → 0) into a 6-arm pattern match that also handles k = 4
heterogeneous children correctly.

This doc is the direct continuation of the markdown-only scoping
precedent established by cycles 373, 379, 385, 398, 402, and 495:

* `.prover-state/issues/def_422B_subLemmaA_inductive_plan.md` (cycle
  373 — 1399 lines, drove cycles 374–378's 8-tree ladder).
* `.prover-state/issues/def_422B_phase_alpha_prime_scoping.md` (cycle
  379 — 1373 lines, drove cycles 380–383's Family A/B helpers).
* `.prover-state/issues/def_422B_phase_alpha_prime_family_C_scoping.md`
  (cycle 385 — 894 lines, drove cycles 386–397's Family C ladder).
* `.prover-state/issues/def_422B_phase_alpha_prime_family_bushy_scoping.md`
  (cycle 398 — 938 lines, drove cycles 399–401's `bushy` migration).
* `.prover-state/issues/def_422B_phase_alpha_prime_5_scoping.md`
  (cycle 402 — 1299 lines, drove cycles 403/491–494's k=3
  non-symmetric calibration ladder).
* `.prover-state/issues/def_422B_phase_beta_gamma_scoping.md`
  (cycle 495 — 868 lines, drove cycles 496/497's Phase β.1 + γ
  ships; flagged R6.B falsity in its §12 update).

**§422 axiom-clean streak: 70 substantive + 5 doc (cycles 336–497)**,
advancing to **70 substantive + 6 doc (336–498)** after this ship.
Single grandfathered sorry at `OpenMath/Chapter4/Section422.lean:2279`
(cycle 365's `powRep_sum_eq_of_strict_subtree_agreement` general
body); `grep -c sorry` returns **5** (4 docstring references + 1
actual code sorry). Section422.lean: 12564 LOC (current).

### §1.1 R6.B falsity recap (cycle 497 worker's finding)

Cycle 497 (Phase γ ship of `inversePolyTree_eq_of_subtree_agreement`)
confirmed that cycle 495's Phase β.2 plan is **structurally
impossible** as scoped:

> Cycle 495 R6.B claim:
> `inversePolyTree (mk (c₁::c₂::c₃::c₄::cs)) f = 0` matches
> `Φ_{η⁻¹}(mk (c₁::c₂::c₃::c₄::cs))` because the latter "vanishes
> on k ≥ 4 children".

This claim is **false**. Cycle 358's `elementaryWeightQ_phi_inv_mk`
(`Section422.lean:582`) shows that, for any RKTableau `M` and tree
`t = mk children`,
```
Φ_{⟦M⟧⁻¹}(mk children)
  = -Σᵢ M.b i · M.derivativeWeightWithSrc M.inverse i (mk children)
```
where the inner factor expands as
`Πℓ (M.inverse.elementaryWeight cℓ + Σⱼ A_{ij} · M.inverse.derivativeWeight j cℓ)`,
which is **generically nonzero** for every k ≥ 0 (e.g. take all
`cℓ = vertex`: the per-row factor is `-v + Σⱼ A_{ij} · (-v)` which
is nonzero in general).

Meanwhile `inversePolyTree`'s catch-all
`mk (_::_::_::_::_) → 0` (Section422.lean:9732) returns `0` on every
k ≥ 4 children tree. So the Phase β.2 equality
`Φ_{η⁻¹}(t) = inversePolyTree t (Φ_η ·)` is **false** on
quadchild-or-larger trees until `inversePolyTree` is extended
beyond k = 3.

### §1.2 What this means for cycle 365's grandfathered sorry

`powRep_sum_eq_of_strict_subtree_agreement` (Section422.lean:2272–2279)
quantifies over **arbitrary** `t : RT`, including quadchild and
larger trees. Any structural-induction proof eventually requires
`inversePolyTree`'s value to match `Φ_{η⁻¹}` at every step. Phase
α'.5.2/3 — the k = 4 (and k ≥ 5) extensions of `inversePolyTree` —
are therefore strict prerequisites for the cycle 365 closure plan.

The cycle 497 task results §"Discovery #3" and the cycle 495 scoping
doc §12.2/12.3 both endorse exactly this resolution path.

### §1.3 Scope of this doc

Phase α'.5.2 designs the k = 4 extension. Phase α'.5.3 (k ≥ 5)
is deferred until α'.5.2 is fully shipped (cycle ~509–510 per §6).

This doc:

* Enumerates the 16 blocks of the k = 4 `_inv_mk` expansion.
* Strawmans `tetrachildPolynomial` (the absorbed-blocks body) and
  `tetrachildCrossTerm` (the bilinear + trilinear cross-kernel
  cascade).
* Decomposes Phase α'.5.2 into sub-phases α'.5.2.0 through
  α'.5.2.k, each one cycle, mirroring cycles 370 / 387 / 399 /
  400 / 403 / 491–494's per-arity templates.
* Pins cycle 499 to the empirical `bushy₄ = mk [v,v,v,v]`
  closed-form ship (the symmetric k = 4 anchor, analogous to
  cycle 370's `bushy` for k = 3).
* Reserves cycle 500 for the `tetrachildPolynomial` /
  `tetrachildCrossTerm` definition + 6-arm `inversePolyTree`
  extension + first calibration witness ship.
* Sketches cycles 501+'s k = 4 non-symmetric witness ladder
  (analogous of cycles 403 / 491–494 for k = 3).

## §2 What needs to be built

The current `inversePolyTree` (cycle 387 + 399 extension at
`Section422.lean:9718–9733`) has **5 arms**:

```lean
noncomputable def inversePolyTree : RT → (RT → ℝ) → ℝ
  | mk [],            f => -f vertex
  | mk [c],           f => -(f vertex * inversePolyTree c f)
                            + monochildCrossTerm c f
                            - f (mk [c])
  | mk [c₁, c₂],      f => bichildPolynomial c₁ c₂
                            (inversePolyTree c₁ f)
                            (inversePolyTree c₂ f) f
  | mk [c₁, c₂, c₃],  f => trichildPolynomial c₁ c₂ c₃
                            (inversePolyTree c₁ f)
                            (inversePolyTree c₂ f)
                            (inversePolyTree c₃ f) f
  | mk (_::_::_::_::_), _ => 0
```

Phase α'.5.2 extends this to a **6-arm** match:

```lean
noncomputable def inversePolyTree : RT → (RT → ℝ) → ℝ
  | mk [],                f => -f vertex
  | mk [c],               f => ...                                -- unchanged
  | mk [c₁, c₂],          f => bichildPolynomial ...              -- unchanged
  | mk [c₁, c₂, c₃],      f => trichildPolynomial ...             -- unchanged
  | mk [c₁, c₂, c₃, c₄],  f => tetrachildPolynomial c₁ c₂ c₃ c₄  -- NEW
                                (inversePolyTree c₁ f)
                                (inversePolyTree c₂ f)
                                (inversePolyTree c₃ f)
                                (inversePolyTree c₄ f) f
  | mk (_::_::_::_::_::_), _ => 0                                 -- catch-all bumped to k ≥ 5
```

with two new helpers `tetrachildPolynomial` and `tetrachildCrossTerm`
(plus optional sub-helpers `tetrachildBilinear` and
`tetrachildTrilinear` per §4/§5 below).

## §3 The k = 4 block decomposition

For `t = mk [t₁, t₂, t₃, t₄]`, cycle 358's `_inv_mk`
(`Section422.lean:582`) unfolds (after `_mk × k` plus the per-row
factorisation):
```
M.inverse.derivativeWeightWithSrc M.inverse i (mk [t₁, t₂, t₃, t₄])
  = Π_{ℓ∈{1,2,3,4}} ( M.inverse.elementaryWeight tℓ
                    + Σⱼ M.A i j · M.inverse.derivativeWeight j tℓ )
  = Π_ℓ ( inv_ℓ + S_ℓ(i) )
```
where `inv_ℓ := M.inverse.elementaryWeight tℓ` (independent of `i`)
and `S_ℓ(i) := Σⱼ M.A i j · M.inverse.derivativeWeight j tℓ`
(linear in `i`'s row of `M.A`).

Expanding the product gives 2⁴ = **16 blocks** indexed by a subset
`S ⊆ {1, 2, 3, 4}` (representing the positions where the `A-sum`
factor is selected; complement `Sᶜ` selects the constant `inv_ℓ`
factor):

| # | S | |S| | Per-row factor | Outer-sum contribution shape |
|---|---|---|---|---|
| (1) | `∅` | 0 | `inv₁ · inv₂ · inv₃ · inv₄` | `-Φ_η(v) · inv₁ · inv₂ · inv₃ · inv₄` |
| (2) | `{1}` | 1 | `S₁(i) · inv₂ · inv₃ · inv₄` | `-inv₂ · inv₃ · inv₄ · f(mk [t₁])` |
| (3) | `{2}` | 1 | `inv₁ · S₂(i) · inv₃ · inv₄` | `-inv₁ · inv₃ · inv₄ · f(mk [t₂])` |
| (4) | `{3}` | 1 | `inv₁ · inv₂ · S₃(i) · inv₄` | `-inv₁ · inv₂ · inv₄ · f(mk [t₃])` |
| (5) | `{4}` | 1 | `inv₁ · inv₂ · inv₃ · S₄(i)` | `-inv₁ · inv₂ · inv₃ · f(mk [t₄])` |
| (6) | `{1,2}` | 2 | `S₁(i) · S₂(i) · inv₃ · inv₄` | bilinear `(t₁, t₂)` kernel, weighted by `inv₃ · inv₄` |
| (7) | `{1,3}` | 2 | `S₁(i) · inv₂ · S₃(i) · inv₄` | bilinear `(t₁, t₃)` kernel, weighted by `inv₂ · inv₄` |
| (8) | `{1,4}` | 2 | `S₁(i) · inv₂ · inv₃ · S₄(i)` | bilinear `(t₁, t₄)` kernel, weighted by `inv₂ · inv₃` |
| (9) | `{2,3}` | 2 | `inv₁ · S₂(i) · S₃(i) · inv₄` | bilinear `(t₂, t₃)` kernel, weighted by `inv₁ · inv₄` |
| (10) | `{2,4}` | 2 | `inv₁ · S₂(i) · inv₃ · S₄(i)` | bilinear `(t₂, t₄)` kernel, weighted by `inv₁ · inv₃` |
| (11) | `{3,4}` | 2 | `inv₁ · inv₂ · S₃(i) · S₄(i)` | bilinear `(t₃, t₄)` kernel, weighted by `inv₁ · inv₂` |
| (12) | `{1,2,3}` | 3 | `S₁(i) · S₂(i) · S₃(i) · inv₄` | trilinear `(t₁, t₂, t₃)` kernel, weighted by `inv₄` |
| (13) | `{1,2,4}` | 3 | `S₁(i) · S₂(i) · inv₃ · S₄(i)` | trilinear `(t₁, t₂, t₄)` kernel, weighted by `inv₃` |
| (14) | `{1,3,4}` | 3 | `S₁(i) · inv₂ · S₃(i) · S₄(i)` | trilinear `(t₁, t₃, t₄)` kernel, weighted by `inv₂` |
| (15) | `{2,3,4}` | 3 | `inv₁ · S₂(i) · S₃(i) · S₄(i)` | trilinear `(t₂, t₃, t₄)` kernel, weighted by `inv₁` |
| (16) | `{1,2,3,4}` | 4 | `S₁(i) · S₂(i) · S₃(i) · S₄(i)` | quadrilinear self-kernel; `-f(mk [t₁, t₂, t₃, t₄])` |

**Counts**: 1 all-const + 4 single-A-sum + 6 two-A-sum + 4
three-A-sum + 1 four-A-sum = 16 = C(4,0) + C(4,1) + C(4,2) +
C(4,3) + C(4,4) = 2⁴. Matches the k = 3 pattern (`1 + 3 + 3 + 1 =
8` blocks per cycle 402 scoping §2.1).

### §3.1 Per-block kernel identification

Following cycle 387/399's pattern, each block's "outer-sum
contribution" is a sum-over-`i`-of-`Σⱼ M.b i · (per-row factor)`,
which by cycle 358's machinery folds into named `f` evaluations
when the per-row factor matches a recognised tree shape:

* **Block (1)** (all-const): outer factor is `Σᵢ M.b i = M.elementaryWeight vertex = Φ_η(vertex)`,
  so contributes `-Φ_η(vertex) · inv₁ · inv₂ · inv₃ · inv₄` to the
  closed form. **Absorbed** into `tetrachildPolynomial` directly.

* **Blocks (2)–(5)** (single-A-sum at position ℓ): outer factor is
  `Σᵢ M.b i · S_ℓ(i)` = `Σᵢ Σⱼ M.b i · M.A i j · M.inverse.derivativeWeight j tℓ`,
  which by D.3.a.1 (`elementaryWeightQ_phi_mul_mk`) collapses to
  `Φ_η(mk [tℓ])` weighted by the product of the three "non-selected"
  `inv_k` values. **Absorbed** into `tetrachildPolynomial`.

* **Blocks (6)–(11)** (two-A-sum at positions `{ℓ₁, ℓ₂}`): outer
  factor is `Σᵢ M.b i · S_{ℓ₁}(i) · S_{ℓ₂}(i)`, which expands as
  a double-`Σⱼ`-`Σₖ` of `M.b i · M.A i j · M.A i k ·
  M.inverse.derivativeWeight j t_{ℓ₁} · M.inverse.derivativeWeight k t_{ℓ₂}`.
  This is a **bilinear cross-kernel** in the pair `(t_{ℓ₁}, t_{ℓ₂})`,
  weighted by `inv_{k₁} · inv_{k₂}` for `{k₁, k₂} = {1,2,3,4} \
  {ℓ₁, ℓ₂}` (the "non-selected" positions). **Not absorbed** —
  this is the `tetrachildBilinear` cross-term.

* **Blocks (12)–(15)** (three-A-sum at positions `{ℓ₁, ℓ₂, ℓ₃}`):
  outer factor is `Σᵢ M.b i · S_{ℓ₁}(i) · S_{ℓ₂}(i) · S_{ℓ₃}(i)`,
  expanding as a triple-`Σⱼ`-`Σₖ`-`Σₗ` sum. This is a **trilinear
  cross-kernel** in the triple `(t_{ℓ₁}, t_{ℓ₂}, t_{ℓ₃})`, weighted
  by the single non-selected `inv_{ℓ₄}`. **Not absorbed** — this
  is the `tetrachildTrilinear` cross-term.

* **Block (16)** (all-A-sum): outer factor is
  `Σᵢ M.b i · S₁(i) · S₂(i) · S₃(i) · S₄(i)`, which is a
  **quadrilinear self-kernel** that by the cycle 358 unfold pattern
  matches `Φ_η(mk [t₁, t₂, t₃, t₄])` (up to a sign). **Absorbed**
  as the explicit `- f(mk [t₁, t₂, t₃, t₄])` self-term in
  `tetrachildPolynomial`.

### §3.2 Bilinear cross-kernel structural shape

For Block (6) `S = {1, 2}`, the outer factor is
```
Σᵢ M.b i · S₁(i) · S₂(i) · inv₃ · inv₄
= inv₃ · inv₄ · Σᵢ M.b i · (Σⱼ A_{ij} · M.inverse.dW j t₁)
                          · (Σₖ A_{ik} · M.inverse.dW k t₂)
```
By the cycle 387/399 pattern, this fold to a sum of products of
`Φ_η`-values at named trees. The exact shape depends on `t₁, t₂`:

* **Both vertex** (`t₁ = t₂ = vertex`):
  `inv₃ · inv₄ · Σᵢ M.b i · (Σⱼ A_{ij})² = inv₃ · inv₄ · Φ_η(broom₃)`.
* **One vertex, one cherry** (`t₁ = vertex, t₂ = cherry`):
  By the cycle 388 / 403 pattern, this folds into a polynomial
  combination of `Φ_η(broom₃)`, `Φ_η(mk [v, c])` (the
  `mk [vertex, cherry]` kernel), and others. See cycle 403's
  `(v, v, c)` analysis for the structural form.
* **Other named pairs**: each pair `(t_a, t_b)` requires
  empirical derivation; the `bichildCrossTerm` dispatch
  (`Section422.lean:9455–9519`, cycles 387/388/391/393/396) is
  the precedent reference.

The `tetrachildBilinear` helper will need its own per-pair
dispatch table. Phase α'.5.2's empirical surface is enumerated
in §6.

### §3.3 Trilinear cross-kernel structural shape

For Block (12) `S = {1, 2, 3}`, the outer factor is
```
inv₄ · Σᵢ M.b i · S₁(i) · S₂(i) · S₃(i)
```
At `(t₁, t₂, t₃) = (vertex, vertex, vertex)` this is
`inv₄ · Σᵢ M.b i · (Σⱼ A_{ij})³ = inv₄ · Φ_η(bushy)` (the cycle 370
bushy kernel). Other triples reuse the cycle 399 / 403 / 491–494
empirical surface for `trichildCrossTerm`. So `tetrachildTrilinear`
can dispatch via `trichildCrossTerm` for the trilinear part:
```
tetrachildTrilinear t₁ t₂ t₃ t₄ inv₁ inv₂ inv₃ inv₄ f
  = inv₄ · trichildCrossTerm-like(t₁, t₂, t₃, f) + ...  (4 trilinear blocks)
```
**Possible**: `tetrachildTrilinear`'s 4 blocks may collapse into 4
reuses of `trichildCrossTerm`, with one for each `{ℓ₁, ℓ₂, ℓ₃}`
triple (omitting position ℓ₄). **To be verified at α'.5.2.1
implementation time.** This would reduce `tetrachildTrilinear` to
~20 LOC if the reuse identity holds; otherwise it needs an
independent per-triple dispatch table.

### §3.4 Sign convention

Following cycle 358's `_inv_mk` outer prefix `-Σᵢ M.b i · (...)`,
each block contributes with the inverse sign:

* Blocks (1) and (2)–(5): contribute negatively (the outer `-`
  flips the per-row factor).
* Blocks (6)–(11) and (12)–(15): the per-row factor is positive
  (product of positives), so they contribute negatively after
  the outer `-`.
* Block (16): the quadrilinear self-kernel matches
  `Φ_η(mk [t₁, t₂, t₃, t₄])`, contributing `-Φ_η(mk [...])` after
  the outer `-`.

Cycle 399's `trichildPolynomial` follows the **same** convention:
absorbed Blocks (1)–(4) have leading `-` signs; the
`+trichildCrossTerm` and `-f (mk [...])` terms in the body match
the sign convention. `tetrachildPolynomial` mirrors this.

## §4 `tetrachildPolynomial` strawman

Following the cycle 387/399 pattern (`bichildPolynomial`,
`trichildPolynomial`), the strawman definition is:

```lean
noncomputable def tetrachildPolynomial
    (t₁ t₂ t₃ t₄ : RT) (inv₁ inv₂ inv₃ inv₄ : ℝ) (f : RT → ℝ) : ℝ :=
  -(f RootedTree.vertex * inv₁ * inv₂ * inv₃ * inv₄)        -- Block (1)
    - inv₂ * inv₃ * inv₄ * f (mk [t₁])                       -- Block (2)
    - inv₁ * inv₃ * inv₄ * f (mk [t₂])                       -- Block (3)
    - inv₁ * inv₂ * inv₄ * f (mk [t₃])                       -- Block (4)
    - inv₁ * inv₂ * inv₃ * f (mk [t₄])                       -- Block (5)
    + tetrachildCrossTerm t₁ t₂ t₃ t₄ f                      -- Blocks (6)–(15) packaged
    - f (mk [t₁, t₂, t₃, t₄])                                -- Block (16) self-term
```

The Block (1)–(5) terms are absorbed into the body verbatim
(parametric in `tᵢ` and `invᵢ`). The Block (16) self-term is the
explicit subtraction. Blocks (6)–(15) — the 6 bilinear + 4
trilinear cross-kernels — are packaged into `tetrachildCrossTerm`.

**Why one combined `tetrachildCrossTerm` instead of separate
`tetrachildBilinear` + `tetrachildTrilinear`?** Two design options:

* **Option A** (combined): `tetrachildCrossTerm t₁ t₂ t₃ t₄ f`
  returns the sum of all 10 cross-kernel contributions. Pro:
  matches cycle 399's `trichildCrossTerm` mono-helper pattern.
  Con: each `if-then-else` branch needs ~10–15 cross-kernel
  coefficients (vs cycle 399's ~5).

* **Option B** (split): `tetrachildCrossTerm = tetrachildBilinear + tetrachildTrilinear`.
  Pro: each sub-helper has a cleaner per-position-set structure
  (6 bilinear + 4 trilinear branches). Con: two helper defs
  to maintain.

**Recommendation**: ship **Option A** initially (mirror cycle 399
exactly) to minimise the design surface. If empirical evidence
(cycle 501+'s second non-symmetric witness) shows that the
combined dispatch is hard to extend, refactor to Option B in a
subsequent cycle.

### §4.1 Why `inv_ℓ`-explicit, not parametric

`tetrachildPolynomial` takes the four `inv_ℓ` values **explicitly**
as arguments rather than re-invoking `inversePolyTree tℓ f` inside
the body. This matches the cycle 399 `trichildPolynomial`
convention (`Section422.lean:9686`) and is required for the
recursive structure: `inversePolyTree (mk [c₁, c₂, c₃, c₄]) f`
must pass `inversePolyTree cᵢ f` to `tetrachildPolynomial`, which
then uses each as `inv_ℓ`. This also ensures that the recursion
terminates via Lean's default `sizeOf` measure (the recursive
calls are at `cᵢ`, which is strictly smaller than `mk [c₁, c₂, c₃, c₄]`).

### §4.2 Aristotle compatibility

`tetrachildPolynomial` is a pure polynomial expression in
`f, inv₁, inv₂, inv₃, inv₄, t₁, t₂, t₃, t₄`. Once shipped, the
calibration witness `inversePolyTree_bushy₄` (cycle 500) should be
Aristotle-discoverable by direct `unfold` + `ring`. Estimated
~30–50 LOC for the calibration witness.

## §5 `tetrachildCrossTerm` strawman

Following cycle 387 / 388 / 391 / 393 / 396's `bichildCrossTerm`
and cycle 399 / 403 / 491–494's `trichildCrossTerm` patterns, the
strawman is an `if-then-else` cascade over named quadruples
`(t₁, t₂, t₃, t₄)`:

```lean
noncomputable def tetrachildCrossTerm
    (t₁ t₂ t₃ t₄ : RT) (f : RT → ℝ) : ℝ :=
  if t₁ = RootedTree.vertex ∧ t₂ = RootedTree.vertex
      ∧ t₃ = RootedTree.vertex ∧ t₄ = RootedTree.vertex then
    -- Symmetric (v, v, v, v) case (cycle 499 deliverable):
    -- Block (6)–(11) bilinear contributions: 6 × b' (each is
    --   `inv₃ · inv₄ · b'` at (v, v, *, *) → b' / each pair).
    -- Block (12)–(15) trilinear contributions: 4 × bushy.
    -- Closed form computed in cycle 499 derivation.
    6 * f RootedTree.broom₃ + 4 * f RootedTree.bushy
  else if t₁ = vertex ∧ t₂ = vertex ∧ t₃ = vertex ∧ t₄ = cherry then
    -- Cycle 501 deliverable (non-symmetric (v,v,v,c) case)
    -- closed-form cross-term derived in cycle 501.
    <coefficient-pattern from §3.2 / §3.3 derivation>
  else if ... (more branches per cycles 502–509+) ...
  else 0
```

The number of named branches grows by 1 per α'.5.2.k cycle (k ≥ 0).
Cycle 499 ships the first branch `(v,v,v,v)`; cycle 501 ships
`(v,v,v,c)`; subsequent cycles ship one new quadruple per cycle.

### §5.1 Symmetric `(v,v,v,v)` strawman derivation

At `(t₁, t₂, t₃, t₄) = (v, v, v, v)`:

* `inv_v = -v` (cycle 367 lift, `Section422.lean:2376`'s
  `elementaryWeightQ_phi_inv_vertex`).

* **Block (1)**: `-(v · (-v)⁴) = -v⁵`. Absorbed into
  `tetrachildPolynomial` body.

* **Blocks (2)–(5)**: each `-(inv_others · f(mk [vertex])) = -((-v)³ · c) = v³c`,
  where `c = f(cherry) = Φ_η(cherry)`. Four such terms: `4 · v³c`.
  Absorbed.

* **Blocks (6)–(11) (bilinear)**: each pair `{i, j}` contributes
  `inv_k · inv_l · b' = (-v)² · b' = v² · b'` where
  `b' = f(broom₃) = Φ_η(broom₃)`. Six such terms: `6 · v² · b'`.
  Goes into `tetrachildCrossTerm` since the bilinear kernel is
  non-absorbed.

  **Wait — sign check**. The block contributes positively in the
  pre-outer-prefix expansion, so after the `-Σᵢ M.b i · (...)`
  outer prefix flips, the closed form has `-(6 · v² · b')`. Let
  me re-derive the convention.

  Per cycle 358's `_inv_mk`, the formula is
  `Φ_{η⁻¹}(t) = -Σᵢ M.b i · M.derivativeWeightWithSrc M.inverse i t`.
  At `t = mk [v,v,v,v]`, the inner factor is `(inv_v + S_v(i))⁴ =
  (-v + Σⱼ A_{ij})⁴`. Expanding:
  `(-v)⁴ + 4·(-v)³·(Σⱼ A_{ij}) + 6·(-v)²·(Σⱼ A_{ij})² + 4·(-v)·(Σⱼ A_{ij})³ + (Σⱼ A_{ij})⁴`
  `= v⁴ - 4v³·(Σⱼ A_{ij}) + 6v²·(Σⱼ A_{ij})² - 4v·(Σⱼ A_{ij})³ + (Σⱼ A_{ij})⁴`.

  Summing against `M.b i` and using the cycle 358 / 370 helpers:
  * `Σᵢ M.b i · 1 = Φ_η(vertex) = v`.
  * `Σᵢ M.b i · (Σⱼ A_{ij}) = Φ_η(cherry) = c`.
  * `Σᵢ M.b i · (Σⱼ A_{ij})² = Φ_η(broom₃) = b'`.
  * `Σᵢ M.b i · (Σⱼ A_{ij})³ = Φ_η(bushy) = bu` (the §422 cycle 370
    kernel; let me call it `bu := Φ_η(bushy)`).
  * `Σᵢ M.b i · (Σⱼ A_{ij})⁴ = Φ_η(bushy₄)` where `bushy₄ := mk [v, v, v, v]`.
    **This is a NEW named kernel** — does it have a Lean name yet?
    Per `Section422.lean` `grep`, **no**: `bushy₄`-like names do
    not yet appear. Cycle 499's first task is to either define
    `bushy₄ := mk [v, v, v, v]` in `Section310` / `Section301` (the
    `RootedTree.bushy` definition lives in Section301; cycle 499
    worker should grep) or reference the constructor form
    `OpenMath.Chapter3.Section310.RootedTree.mk [vertex, vertex, vertex, vertex]`
    directly.

  Combining with the outer `-` prefix:
  `Φ_{η⁻¹}(mk [v,v,v,v])
     = -[v · v⁴ − 4v³ · c + 6v² · b' − 4v · bu + Φ_η(bushy₄)]`
   (the leading `v` comes from `Σᵢ M.b i · constant = constant · Σᵢ M.b i = v · constant`
     when the constant is the `v⁴ = (-v)⁴` coefficient).

  Wait — re-deriving: the leading constant block is `(-v)⁴ = v⁴`,
  and `Σᵢ M.b i · v⁴ = v⁴ · Σᵢ M.b i = v⁴ · v = v⁵`.
  Then `Σᵢ M.b i · (-4v³ · Σⱼ A_{ij}) = -4v³ · c`.
  Then `Σᵢ M.b i · 6v² · (Σⱼ A_{ij})² = 6v² · b'`.
  Then `Σᵢ M.b i · (-4v) · (Σⱼ A_{ij})³ = -4v · bu`.
  Then `Σᵢ M.b i · (Σⱼ A_{ij})⁴ = Φ_η(bushy₄)`.

  Sum: `v⁵ - 4v³ · c + 6v² · b' - 4v · bu + Φ_η(bushy₄)`.

  Apply the outer `-` prefix:
  `Φ_{η⁻¹}(mk [v,v,v,v])
     = -v⁵ + 4v³ · c - 6v² · b' + 4v · bu - Φ_η(bushy₄)`.

### §5.2 Strawman for `tetrachildPolynomial` at (v,v,v,v)

The closed form from §5.1 should be reproduced by evaluating
`tetrachildPolynomial v v v v (-v) (-v) (-v) (-v) f` (the four
`inv_ℓ` values at `vertex`). Let's check:

* Block (1) term: `-(v · (-v)⁴) = -(v · v⁴) = -v⁵`. ✓
* Block (2) term: `-(inv₂ · inv₃ · inv₄ · f(mk [vertex])) = -((-v)³ · c) = -(-v³) · c = v³ · c`. ✓
* Blocks (3)/(4)/(5) terms: identical. Total: `4v³ · c`. ✓
* `+ tetrachildCrossTerm v v v v f`: should equal `-6v² · b' + 4v · bu`.
* Block (16) term: `-f(mk [v,v,v,v]) = -Φ_η(bushy₄)`. ✓

So `tetrachildCrossTerm v v v v f = -6v² · b' + 4v · bu`.

But wait, the `inv_ℓ` factors in Blocks (6)–(11) are `(-v)²` not
`-(-v)²`. The `-` sign in the closed form `-6v² · b'` comes from
the outer `-Σᵢ` of cycle 358. So `tetrachildCrossTerm` (which is
**added** to `tetrachildPolynomial`'s body, not subtracted) should
carry the `inv_others`-weighted bilinear / trilinear sum **with
the per-block signs from the post-outer-prefix expansion**.

Let me re-check: in cycle 399's `trichildPolynomial` body
(`Section422.lean:9686–9693`), the cross-term is `+ trichildCrossTerm t₁ t₂ t₃ f`.
And cycle 400's `inversePolyTree_bushy` calibration shows
`trichildCrossTerm v v v f = 3 · f vertex · f broom₃ = 3v · b'`.
The closed form for `Φ_{η⁻¹}(bushy) = v⁴ - 3v² · c + 3v · b' - bu`
includes the `+3v · b'` term. So `trichildCrossTerm`'s value
**absorbs** the per-block outer-sign flip and represents the
positive contribution to the closed form.

So for `tetrachildCrossTerm v v v v f`:

* Bilinear contribution (Blocks (6)–(11)): each pair contributes
  `+inv_k · inv_l · b' = +v² · b'` (the `(-v)²` factor is `v²`
  positive). Six pairs: `+6v² · b'`.
* Trilinear contribution (Blocks (12)–(15)): each triple
  contributes `+inv_l · bu = +(-v) · bu = -v · bu`. Four triples:
  `-4v · bu`.

Wait — `(-v)` is negative. Re-checking: `inv₄ = -v` for `t₄ = vertex`.
So the `inv_ℓ`-weight for Block (12) is `inv₄ = -v`, and the
trilinear contribution is `inv₄ · (Σᵢ M.b i · S₁ · S₂ · S₃) = -v · bu`.

Sum of bilinear + trilinear: `6v² · b' - 4v · bu`.

After the outer `-` prefix in cycle 358's formula:
`-(6v² · b' - 4v · bu) = -6v² · b' + 4v · bu`. This matches §5.1's
closed form for the cross-term part. ✓

So **`tetrachildCrossTerm v v v v f = 6 · f broom₃ + 4 · f bushy`**.

Wait — I want to be careful. Cycle 400's `trichildCrossTerm v v v f = 3 · f vertex · f broom₃ = 3v · b'`.
But §5.1's bushy closed form has `+3v · b'`, which is the same.
The factor of `v` in front of `b'` matches.

For tetrachild: bilinear is `6v² · b'`. So
`tetrachildCrossTerm v v v v f = 6 · (f vertex)² · f broom₃ - 4 · f vertex · f bushy`?

Let me re-derive carefully. Closed form is `Φ_{η⁻¹}(mk [v,v,v,v]) = -v⁵ + 4v³c - 6v²b' + 4v·bu - Φ_η(bushy₄)`.

Verify: `tetrachildPolynomial v v v v (-v) (-v) (-v) (-v) f` should equal this.

* Block (1): `-(v · (-v) · (-v) · (-v) · (-v)) = -(v · v⁴) = -v⁵`. ✓
* Blocks (2)–(5): each is `-(inv_others · f(mk[vertex])) = -((-v)³ · c) = -(-v³ · c) = v³c`.
  Four such → `4v³c`. ✓ (Matches `+4v³c` in closed form.)
* `+ tetrachildCrossTerm` should equal `-6v²b' + 4v · bu`.
* Block (16): `-f(mk [v,v,v,v]) = -Φ_η(bushy₄)`. ✓

So `tetrachildCrossTerm v v v v f = -6v²b' + 4v · bu = -6·v²·b' + 4·v·bu`.

In Lean notation, this is
`-6 · (f vertex)^2 · f broom₃ + 4 · f vertex · f bushy`.

Wait — but cycle 400's `trichildCrossTerm v v v f` is **positive**
`+3v · b'`, not negative. Let me re-check cycle 370's bushy.

Cycle 370's `elementaryWeightQ_phi_inv_bushy` (Section422.lean:3011–3019):
```
Φ_{η⁻¹}(bushy) = v⁴ - 3v²c + 3v·b' - bu
```

And cycle 399's trichildPolynomial body is:
```
-(f vertex * inv₁ * inv₂ * inv₃)
  - inv₂ * inv₃ * f (mk [t₁])
  - inv₁ * inv₃ * f (mk [t₂])
  - inv₁ * inv₂ * f (mk [t₃])
  + trichildCrossTerm t₁ t₂ t₃ f
  - f (mk [t₁, t₂, t₃])
```

At (v, v, v) with `inv_ℓ = -v`:
* Block (1): `-(v · (-v)³) = -(v · -v³) = v⁴`. ✓ (matches `+v⁴`).
* Blocks (2)–(4): each `-((-v)² · c) = -v² · c`. Three of them → `-3v²c`. ✓
* `+ trichildCrossTerm v v v f` should equal `+3v·b'`.
* Block (8): `-f(bushy) = -bu`. ✓

So `trichildCrossTerm v v v f = 3v · b'`, **positive**. This is
because the trichild bilinear cross-terms (Blocks 5/6/7) have the
`inv_unselected` weight `inv_k = -v`, so `inv_k · b' = -v · b'`.
Three blocks: `-3v · b'`. After outer `-`: `+3v · b'`. Hmm — but
my §5.1 analysis for tetrachild says the bilinear is `6v² · b'`,
not `-6v² · b'`. Let me re-check.

Re-deriving trichild (v,v,v) cross-term carefully:

`Φ_{η⁻¹}(bushy) = -Σᵢ M.b i · ∏_{ℓ=1}^{3} (inv_v + S_v(i))`
                = `-Σᵢ M.b i · (-v + S_v(i))³`
                where `S_v(i) = Σⱼ A_{ij} · (-v) · 1 = -v · Σⱼ A_{ij}`?

Wait, I need to re-check. `S_ℓ(i) = Σⱼ A_{ij} · M.inverse.derivativeWeight j tℓ`.

For `tℓ = vertex`, `M.inverse.derivativeWeight j vertex = 1` (cycle 370
helper `h_inner_sum`: `Σⱼ A_{ij} · M.inverse.dW j vertex = Σⱼ A_{ij}`).

So `S_v(i) = Σⱼ A_{ij}`, NOT `−v · Σⱼ A_{ij}`.

OK, so for `tℓ = vertex`:
* `inv_v + S_v(i) = -v + Σⱼ A_{ij}` (cycle 370's `h_dws_bushy` confirms this).

Now `Σᵢ M.b i · (-v + Σⱼ A_{ij})⁴`:
Expanding `(-v + s)⁴ = v⁴ − 4v³s + 6v²s² − 4v·s³ + s⁴`, then summing `M.b i ·` each term:
* `Σᵢ M.b i · v⁴ = v⁴ · v = v⁵`. 
* `Σᵢ M.b i · (−4v³ · s) = −4v³ · Σᵢ M.b i · Σⱼ A_{ij} = −4v³ · c`.
* `Σᵢ M.b i · 6v² · s² = 6v² · b'`.
* `Σᵢ M.b i · (−4v) · s³ = −4v · bu`.
* `Σᵢ M.b i · s⁴ = Φ_η(bushy₄) = Σᵢ M.b i · (Σⱼ A_{ij})⁴`.

Total: `v⁵ − 4v³c + 6v²b' − 4v · bu + Φ_η(bushy₄)`.

After outer `-` prefix:
`Φ_{η⁻¹}(mk [v,v,v,v]) = -v⁵ + 4v³c − 6v²b' + 4v · bu − Φ_η(bushy₄)`.

So the closed form is **`-v⁵ + 4v³c − 6v²b' + 4v · bu − Φ_η(bushy₄)`**.

Now, `tetrachildPolynomial v v v v (-v) (-v) (-v) (-v) f`:
* Block (1): `-(v · (-v)⁴) = -(v · v⁴) = -v⁵`. ✓
* Blocks (2)–(5): each `-(inv_others · f(mk[vertex])) = -((-v)³ · c) = -(-v³c) = +v³c`.
  Total: `+4v³c`. ✓
* `+ tetrachildCrossTerm v v v v f` should equal `−6v²b' + 4v · bu`.
* Block (16): `-f(mk[v,v,v,v]) = -Φ_η(bushy₄)`. ✓

So `tetrachildCrossTerm v v v v f = −6v²b' + 4v · bu`, i.e.,
`tetrachildCrossTerm v v v v f = -6 · (f vertex)^2 · f broom₃ + 4 · f vertex · f bushy`
in Lean syntax.

**Compare to trichild**: cycle 400 has `trichildCrossTerm v v v f = 3 · f vertex · f broom₃ = +3v · b'`. Different sign! Why?

Re-derive: `Φ_{η⁻¹}(bushy) = -Σᵢ M.b i · (-v + S_v(i))³`
            = `-Σᵢ M.b i · ((-v)³ + 3(-v)²s + 3(-v)s² + s³)`
            = `-Σᵢ M.b i · (-v³ + 3v²s - 3v·s² + s³)`
            = `-[(-v³ · v) + 3v² · c − 3v · b' + bu]`
            = `+v⁴ - 3v²c + 3v·b' - bu`.

OK so closed form is `v⁴ - 3v²c + 3v·b' - bu`. ✓ matches cycle 370.

Now `trichildPolynomial v v v (-v) (-v) (-v) f`:
* Block (1): `-(v · (-v)³) = -(v · -v³) = v⁴`. ✓
* Blocks (2)–(4): each `-(inv_others · f(mk[v])) = -((-v)² · c) = -v²c`.
  Three of them: `-3v²c`. ✓
* `+ trichildCrossTerm v v v f` should equal `+3v·b'`.
* Block (8): `-f(bushy) = -bu`. ✓

So `trichildCrossTerm v v v f = +3v · b'`, **positive**.

So the **sign convention flips parity** between odd-k and even-k in
the cross-term cascade:

* k = 3 (odd) bushy: `+3v · b'`.
* k = 4 (even) bushy₄: `−6v²b' + 4v · bu`.

Why? Because the cross-term coefficient pattern in the expansion
of `(-v + s)^k` is `(k choose j) · (-v)^(k-j) · s^j`. For `(-v)^(k-j)`,
the sign alternates with `(k-j)`'s parity:

* k = 3, j = 2 (bilinear): `(-v)^1 = -v`. So the bilinear factor is
  `-v`, and outer `-` flips it to `+v`. Hence `+3v · b'`.
* k = 4, j = 2 (bilinear): `(-v)^2 = +v²`. So the bilinear factor
  is `+v²`, and outer `-` flips it to `−v²`. Hence `−6v² · b'`.
* k = 4, j = 3 (trilinear): `(-v)^1 = -v`. So the trilinear factor
  is `-v`, and outer `-` flips it to `+v`. Hence `+4v · bu`.

**Conclusion**: `tetrachildCrossTerm v v v v f = -6·(f vertex)²·f broom₃ + 4·f vertex · f bushy`.

This is the **cycle 499 deliverable closed form**.

### §5.3 Empirical surface beyond (v,v,v,v)

After cycle 499 ships the `(v,v,v,v)` branch, subsequent α'.5.2.k
cycles ship non-symmetric k=4 quadruples in increasing
combinatorial complexity:

| Cycle | Quadruple | Order | Notes |
|---|---|---|---|
| 499 | `(v, v, v, v)` | 5 | Symmetric anchor (`bushy₄`). |
| ~501 | `(v, v, v, c)` | 6 | First non-symmetric; reuses bushy + broom₃ kernels. |
| ~502 | `(v, v, c, c)` | 7 | Two-cherry; reuses `mk [v,c]` cross-kernel. |
| ~503 | `(v, c, c, c)` | 8 | Three-cherry; reuses `mk [c,c]` kernel. |
| ~504 | `(c, c, c, c)` | 9 | All-cherry symmetric; pure-cherry tetrachild. |
| ~505 | `(v, v, v, mk[c])` | 7 | `mk[c]`-child analogue of cycle 493. |
| ~506 | `(v, v, v, broom₃)` | 7 | `broom₃`-child analogue of cycle 494. |
| ~507 | `(v, v, v, bushy)` | 8 | Bushy-child (cross-kernel surprise risk). |
| ~508 | `(v, v, c, mk[c])` | 8 | Mixed-child; full bilinear test. |
| ~509 | `(v, v, c, broom₃)` | 8 | Mixed-child variant. |

Each cycle's deliverable shape is: (i) a closed-form
`elementaryWeightQ_phi_inv_*` theorem (~200–300 LOC), (ii) a
calibration witness `inversePolyTree_*` theorem (~30–50 LOC),
(iii) one new `else if` branch in `tetrachildCrossTerm`'s dispatch.

## §6 Phase decomposition

Phase α'.5.2 decomposes into sub-phases α'.5.2.0 through α'.5.2.k,
mirroring cycle 402's Phase α'.5.1 decomposition for k=3:

### §6.1 α'.5.2.0 — empirical `mk [v,v,v,v]` (`bushy₄`) closed form

**One cycle (cycle 499)**, estimated ~150–250 LOC.

* **Deliverable**: `elementaryWeightQ_phi_inv_bushy₄` — the
  closed-form theorem for `Φ_{η_q⁻¹}(mk [v, v, v, v])` per the
  §5.1 derivation.
* **Proof template**: mirror cycle 370's `elementaryWeightQ_phi_inv_bushy`
  (`Section422.lean:3011–3168`, 159 LOC) verbatim, with one extra
  layer in the `h_dws_bushy₄` helper.
* **Sub-steps**:
  1. `h_dw_bushy₄ : M.derivativeWeight i (mk [v,v,v,v]) = (Σⱼ A_{ij})⁴`.
     Mirror cycle 370's `h_dw_bushy` at `Section422.lean:3075–3104`,
     adding a `h_prod_step_3` for the third product step.
  2. `h_bushy₄ : M.elementaryWeight (mk [v,v,v,v]) = Σᵢ M.b i · (Σⱼ A_{ij})⁴`.
     Mirror cycle 370's `h_bushy` at `Section422.lean:3099–3104`.
  3. `h_dws_bushy₄ : M.derivativeWeightWithSrc M.inverse i (mk [v,v,v,v])
       = (inv_v + Σⱼ A_{ij})⁴`. Mirror cycle 370's `h_dws_bushy`
     at `Section422.lean:3105–3140`, adding a `h_prod_step_3`.
  4. Main computation: `_inv_mk` + `_mk × 5` + `Finset.sum_*_distrib`
     + `Finset.mul_sum` algebra + `ring`. Mirror cycle 370's
     `h_sum` at `Section422.lean:3141–3169`.
* **LOC budget**: 159 LOC (cycle 370) + ~30–50 LOC (extra layer) =
  ~190–210 LOC. Strict upper bound: 250 LOC.
* **Aristotle**: try submitting `h_dw_bushy₄`, `h_dws_bushy₄`, and
  the main theorem to Aristotle in batch (3 jobs). Sleep 30 min.
  Cycle 370/372 did NOT use Aristotle; cycle 499 is the first
  opportunity in the bushy-family lineage. Worst case: manual
  proof mirrors cycle 370 verbatim.
* **Non-vacuity**: add an `example` at `⟦explicitEuler⟧` matching
  cycle 370's non-vacuity reference (`Section422.lean:3176–3220`).
  At explicit Euler: `Σ b = 1, A = 0`, so all `Σⱼ A_{ij} = 0`, and
  `Φ_{η⁻¹}(mk[v,v,v,v]) = -1⁵ + 4·1³·0 - 6·1²·0 + 4·1·0 - 0 = -1`.
  Wait, but `Φ_η(bushy₄) = 0` since `A = 0` makes the kernel zero;
  let me re-check by direct evaluation. At explicit Euler with
  `b₀ = [1], A = [[0]], c = [0]`:
  * `Φ_η(vertex) = 1`.
  * `Φ_η(cherry) = 1 · 0 = 0`.
  * `Φ_η(broom₃) = 1 · 0² = 0`.
  * `Φ_η(bushy) = 1 · 0³ = 0`.
  * `Φ_η(bushy₄) = 1 · 0⁴ = 0`.
  So closed form: `-(1)⁵ + 4·(1)³·0 - 6·(1)²·0 + 4·(1)·0 - 0 = -1`.
  And `⟦explicitEuler⟧⁻¹ = ⟦explicitEuler.inverse⟧`, whose value
  on `mk[v,v,v,v]` evaluates to... requires direct computation.
  Cycle 499 worker: verify the `-1` non-vacuity numerically before
  shipping.

### §6.2 α'.5.2.1 — `tetrachildPolynomial` + `tetrachildCrossTerm` def + `inversePolyTree` extension + first calibration

**One cycle (cycle 500)**, estimated ~80–150 LOC.

* **Deliverable 1**: define `tetrachildCrossTerm` per §5 strawman
  (with the `(v,v,v,v)` branch). LOC: ~30.
* **Deliverable 2**: define `tetrachildPolynomial` per §4 strawman.
  LOC: ~20.
* **Deliverable 3**: extend `inversePolyTree`'s pattern match to
  6 arms per §2. LOC: ~10 (adds one `match` arm, bumps catch-all
  from `(_::_::_::_::_)` to `(_::_::_::_::_::_)`).
* **Deliverable 4**: `inversePolyTree_bushy₄` calibration witness —
  prove `inversePolyTree (mk [v,v,v,v]) f = <closed form from §5.2>`.
  LOC: ~30–50. Template: cycle 400's `inversePolyTree_bushy`
  (Section422.lean:9909+).
* **Total LOC**: ~90–110. Strict upper bound: 150 LOC.
* **Risk**: equation-compiler cost — adding a 6th arm to
  `inversePolyTree` will compound the cycle 401 measured 1165s
  warm rebuild cost. Cycle 500 worker should measure and report;
  if cost exceeds 1500s, consider extracting the new helpers into
  a sibling file (e.g. `OpenMath/Chapter4/Section422/TetraChild.lean`).
* **Aristotle**: low utility — these are definitional + mechanical
  unfold proofs. Skip Aristotle for this cycle.

### §6.3 α'.5.2.k for k ≥ 2 — k=4 non-symmetric witnesses

**Multi-cycle (cycles 501–509+)**, estimated ~250–400 LOC each.

Each cycle ships:

1. A new `elementaryWeightQ_phi_inv_<treename>` closed-form
   theorem mirroring cycle 403/491–494's structure (per the
   relevant quadruple from §5.3's empirical surface table).
2. A new `inversePolyTree_<treename>` calibration witness.
3. One new `else if` branch in `tetrachildCrossTerm`'s dispatch
   cascade.
4. Non-vacuity `example` at `⟦explicitEuler⟧`.

**Cycle 501** entry point: `(v, v, v, c) = mk [v, v, v, cherry]`.
Per the cycle 402 §6.1 template for k=3 entry points, this is the
"first non-symmetric heterogeneous quadruple" — combines
`bushy`/`broom₃`/`cherry` kernels per the §3 block decomposition.

**Total Phase α'.5.2 budget**: ~7–12 cycles, ~1500–3500 LOC.

### §6.4 α'.5.2.k+1 — Phase β.1 + γ extension to k=4 (DEFERRED)

**One or two cycles (cycles ~510–511)**, no LOC estimate yet.

Once Phase α'.5.2 has accumulated sufficient k=4 empirical surface
(~6–8 calibration witnesses, mirroring the cycle 403/491–494 k=3
ladder which yielded 5 calibration witnesses → cycle 495's
Phase β.1 scope), the planner should:

* **Extend `inversePolynomial_eq_of_phi_inv`** (Section422.lean
  Phase β.1, cycle 496) — dispatch the k=4 case with one branch
  per α'.5.2 ladder tree, analogous to the cycle 496 k=3 branches.
* **Extend `inversePolyTree_eq_of_subtree_agreement`** (Phase γ,
  cycle 497) — add a `[c₁, c₂, c₃, c₄]` arm to the strong-induction
  proof, mirroring the cycle 497 strategy for the k=3 arm.

Both extensions are mechanical (cycle 496's k=3 branches are ~5
LOC each; cycle 497's k=3 arm is ~30 LOC). LOC budget: ~100–200
each.

### §6.5 Phase β.2 unblock (DEFERRED, cycle ~512+)

Once Phase α'.5.2's full ladder lands (cycles 499–509+) AND the
Phase β.1/γ extensions of §6.4 land (cycles ~510–511), the cycle
495 scoping doc's Phase β.2 plan **can be reattempted**, but
only at a specific tree-shape stratification:

* For trees of order ≤ O (where O is the maximum order on the
  α'.5.2 ladder, ~9), the Phase β.2 structural induction can
  proceed normally — `inversePolyTree` is now point-wise correct
  at every tree of order ≤ O.
* For trees of order > O, the catch-all `(_ :: _ :: _ :: _ :: _ :: _) → 0`
  remains incorrect. The cycle 365 sorry closure is therefore
  still NOT achievable at full generality without a deeper
  structural argument (likely a uniform `nchildPolynomial`
  parametric in k, per cycle 402 scoping §2.3).

**Conclusion**: cycle 365 sorry closure requires either (a) the
order ≤ O case carved out explicitly (which may suffice for
downstream consumers like `thm:422A`), or (b) the `nchildPolynomial`
infrastructure ship (a Phase α'.7+ multi-cycle effort, not in
α'.5.2's scope).

## §7 LOC budgets per sub-phase

| Sub-phase | Cycle(s) | Deliverable | LOC |
|---|---|---|---|
| α'.5.2.0 | 499 | `elementaryWeightQ_phi_inv_bushy₄` closed form | ~190–210 |
| α'.5.2.1 | 500 | `tetrachildPolynomial` + `tetrachildCrossTerm` defs + `inversePolyTree` 6-arm + `inversePolyTree_bushy₄` calibration | ~90–110 |
| α'.5.2.2 | 501 | `(v,v,v,c)` quadruple witness | ~250–300 |
| α'.5.2.3 | 502 | `(v,v,c,c)` quadruple witness | ~250–300 |
| α'.5.2.4 | 503 | `(v,c,c,c)` quadruple witness | ~250–350 |
| α'.5.2.5–.k | 504–509 | additional non-symmetric quadruples | ~250–400 each |
| α'.5.2.k+1 | ~510 | Phase β.1 + γ k=4 extensions | ~100–200 |
| α'.5.2.k+2 | ~511 | (TBD) | TBD |
| **Total** | **499–510+** | **Phase α'.5.2 full closure** | **~2000–3500** |

Section422.lean projection: 12564 (current) → 14000–15500 (post-α'.5.2).
Warm rebuild cost projection: ~1200s (current) → 1600–2200s (post-α'.5.2).

## §8 Risk inventory

### §8.1 R1 — Kernel surprise

**Severity: MEDIUM (precedent-supported)**.

Cycle 384's "`mk [vertex, cherry]` kernel surprise" precedent
(see `feedback_dws_cherry_factor_includes_v_aᵢ.md`) showed that k=3
cross-kernels surface tree shapes (like `mk [v, c]` and `bushy`)
that were not in the pre-derivation kernel matrix. Cycle 403/491's
extension confirmed the pattern: every new heterogeneous triple
introduced 1–2 new named kernels.

For k=4, the combinatorial surface is larger: 6 bilinear + 4
trilinear = 10 cross-kernels per quadruple, vs k=3's 3+1=4. Each
new quadruple may surface 2–4 new named kernels.

**Mitigation**: cycle 499 worker should pre-enumerate the expected
kernels from §5.1 (only `vertex`, `cherry`, `broom₃`, `bushy`,
`bushy₄`). For `(v,v,v,v)` no surprise is expected (all symmetric).
For cycle 501+ (`(v,v,v,c)` and onward), the cycle 503/504+ worker
should expect new kernels and budget LOC for their named-form
verification.

### §8.2 R2 — Equation-compiler build-cost escalation

**Severity: MEDIUM**.

Cycle 401 measured ~1165s warm rebuild for Section422.lean with
5-arm `inversePolyTree`. Cycle 500 extends to 6 arms, which (per
cycle 399's empirical 5-arm-vs-4-arm comparison) adds ~150–250s
to warm rebuild cost. Estimated post-cycle-500 cost: ~1400–1500s.

**Mitigation**: cycle 500 worker should measure and report the
post-extension warm rebuild cost. If it exceeds 1500s, consider:

* **Option A**: extract `tetrachildPolynomial` /
  `tetrachildCrossTerm` into a sibling file (e.g.,
  `OpenMath/Chapter4/Section422/TetraChild.lean`) and import.
  Cycle 411's `Section441A.lean` is a precedent for this refactor.
* **Option B**: bump the catch-all to `(_::_::_::_::_::_::_)` (k ≥ 6)
  preemptively to avoid having to do this again in α'.5.3.
* **Option C** (last resort): increase Lean's elaboration timeout
  via `set_option maxHeartbeats 400000` in the affected file. NOT
  recommended per CLAUDE.md's "Never increase maxHeartbeats above
  200000" rule. Decompose instead.

### §8.3 R3 — `bushy₄` naming conflict

**Severity: LOW**.

The current `OpenMath/Chapter3/Section310/RootedTree.lean` defines
`bushy := mk [vertex, vertex, vertex]` (the k=3 symmetric tree).
Cycle 499 needs to either:

* **Option A**: introduce `bushy₄ := mk [vertex, vertex, vertex, vertex]`
  in Section310 (or wherever named trees live). LOC: ~5 in
  `RootedTree.lean` + corresponding aggregator updates.
* **Option B**: reference the constructor form
  `OpenMath.Chapter3.Section310.RootedTree.mk [vertex, vertex, vertex, vertex]`
  directly throughout. Awkward but avoids touching `RootedTree.lean`.

**Recommendation**: **Option A**. Cycle 499 ships the named
`bushy₄` alias as a small Section310 (or Section301) addition.
Memory `feedback_ring_def_opacity.md` applies: any new alias
needs accompanying `bushy₄_def : bushy₄ = mk [...]` or
equivalent rfl-bridge for `ring`-based proofs to fire.

### §8.4 R4 — Outer-sign-flip parity confusion

**Severity: LOW–MEDIUM**.

Per §5.2's analysis, the cross-term sign convention flips parity
between odd-k and even-k cases. Specifically:

* k = 3: bilinear contributes `+coeff · b'` (after outer `-`,
  flipping the `inv_unselected = -v` factor).
* k = 4: bilinear contributes `-coeff · b'` (outer `-` no longer
  flips, since `inv_unselected² = +v²`).
* k = 4: trilinear contributes `+coeff · bu` (outer `-` flips
  again, since `inv_unselected = -v`).

This parity pattern is well-defined (just expand `(-v + s)^k`),
but it's easy to miscount signs by one factor when not careful.

**Mitigation**: cycle 499 / 500 / 501 workers must derive the
closed-form sign **symbolically** from the `(-v + s)^k` expansion
before committing. Do NOT trust the strawman in §5 verbatim —
re-derive each per the cycle 402 §3.2 worker-instruction precedent.

### §8.5 R5 — `inv_ℓ` heterogeneity at non-vertex children

**Severity: MEDIUM** (will surface at α'.5.2.2+).

The §5 strawman assumes all four children are `vertex`, so
`inv_ℓ = -v` uniformly. For non-symmetric quadruples like
`(v, v, v, c)`, `inv₄ = inv_cherry = v² - c` (cycle 369 closed
form), which is **not** a simple multiple of `v`. The
combinatorial expansion of `(inv_v + s)³ · (inv_c + s')` where
`s, s'` differ in their `M.inverse.derivativeWeight` factors
introduces additional kernel surface area.

**Mitigation**: cycle 501 worker should use the cycle 372/403
`mkVertexCherry`/`mkVertexVertexCherry` proof structures as
the template, particularly the `h_dws_mkVertexVertexCherry`
helper. Expect ~50 extra LOC vs the symmetric bushy₄ case.

### §8.6 R6 — Cycle 365 sorry remains open

**Severity: LOW (acknowledged, not a Phase α'.5.2 risk per se)**.

Phase α'.5.2's full closure (cycles 499–509+) does NOT close
the cycle 365 grandfathered sorry. Per §6.5, sorrow closure
requires:

* Phase α'.5.2 full ladder (~10 calibration witnesses).
* Phase β.1 + γ k=4 extensions (cycle ~510).
* Phase β.2 structural-induction lift at tree-order ≤ O carve-out
  (cycle ~511–512).
* OR `nchildPolynomial` parametric-in-k infrastructure (Phase α'.7+).

**Mitigation**: Phase α'.5.2's scoping (this doc) does NOT promise
cycle 365 closure. It promises only the k=4 pointwise correctness
of `inversePolyTree`, which is a strict prerequisite for the full
closure plan.

## §9 Cycle 499 entry point

### §9.1 Recipe

Mirror cycle 370's `elementaryWeightQ_phi_inv_bushy` proof
verbatim, with one extra layer for the 4th child:

```lean
/-- *Phase α'.5.2.0 (cycle 499) — bushy₄ closed form.* -/
theorem elementaryWeightQ_phi_inv_bushy₄
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi (η_q⁻¹)
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex,
           RootedTree.vertex, RootedTree.vertex])
      = -(elementaryWeightQ_phi η_q RootedTree.vertex) ^ 5
        + 4 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 3
            * elementaryWeightQ_phi η_q RootedTree.cherry
        - 6 * (elementaryWeightQ_phi η_q RootedTree.vertex) ^ 2
            * elementaryWeightQ_phi η_q RootedTree.broom₃
        + 4 * elementaryWeightQ_phi η_q RootedTree.vertex
            * elementaryWeightQ_phi η_q RootedTree.bushy
        - elementaryWeightQ_phi η_q
            (OpenMath.Chapter3.Section310.RootedTree.mk
              [RootedTree.vertex, RootedTree.vertex,
               RootedTree.vertex, RootedTree.vertex]) := by
  refine Quotient.inductionOn η_q ?_
  rintro ⟨s, M⟩
  -- Helpers (reused from cycle 367, 368, 370):
  have h_inv_v : M.inverse.elementaryWeight RootedTree.vertex
      = -M.elementaryWeight RootedTree.vertex := ...
  have h_vertex : M.elementaryWeight RootedTree.vertex
      = ∑ j : Fin s, M.b j := ...
  have h_dw_cherry : ∀ i, M.derivativeWeight i RootedTree.cherry = ∑ j, M.A i j := ...
  have h_cherry : M.elementaryWeight RootedTree.cherry = ∑ i, M.b i * ∑ j, M.A i j := ...
  have h_dw_broom₃ : ∀ i, M.derivativeWeight i RootedTree.broom₃ = (∑ j, M.A i j)^2 := ...
  have h_broom₃ : M.elementaryWeight RootedTree.broom₃
      = ∑ i, M.b i * (∑ j, M.A i j)^2 := ...
  have h_dw_bushy : ∀ i, M.derivativeWeight i RootedTree.bushy = (∑ j, M.A i j)^3 := ...
  have h_bushy : M.elementaryWeight RootedTree.bushy
      = ∑ i, M.b i * (∑ j, M.A i j)^3 := ...
  -- New cycle 499 helpers:
  have h_dw_bushy₄ : ∀ i, M.derivativeWeight i (mk [v,v,v,v]) = (∑ j, M.A i j)^4 := by
    ... (mirror h_dw_bushy with one extra h_prod_step)
  have h_bushy₄ : M.elementaryWeight (mk [v,v,v,v]) = ∑ i, M.b i * (∑ j, M.A i j)^4 := ...
  have h_dws_bushy₄ : ∀ i, M.derivativeWeightWithSrc M.inverse i (mk [v,v,v,v])
      = (M.inverse.elementaryWeight RootedTree.vertex + ∑ j, M.A i j)^4 := by
    ... (mirror h_dws_bushy with one extra h_prod_step)
  -- Main computation:
  rw [elementaryWeightQ_phi_inv_mk M (mk [v,v,v,v]),
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk]
  have h_sum : (∑ i, M.b i * M.derivativeWeightWithSrc M.inverse i (mk [v,v,v,v]))
      = M.elementaryWeight (mk [v,v,v,v])
        - 4 * M.elementaryWeight RootedTree.vertex
            * M.elementaryWeight RootedTree.bushy
        + 6 * M.elementaryWeight RootedTree.vertex ^ 2
            * M.elementaryWeight RootedTree.broom₃
        - 4 * M.elementaryWeight RootedTree.vertex ^ 3
            * M.elementaryWeight RootedTree.cherry
        + M.elementaryWeight RootedTree.vertex ^ 5 := by
    have h_subst : ...
      := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [h_dws_bushy₄ i, h_inv_v]; ring
    rw [h_subst, Finset.sum_sub_distrib, Finset.sum_add_distrib, ...,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        ← h_bushy₄, ← h_bushy, ← h_broom₃, ← h_cherry, ← h_vertex]
    ring
  rw [h_sum]; ring
```

### §9.2 Sub-step LOC estimates

* Helper recap (h_inv_v, h_vertex, h_dw_cherry, h_cherry,
  h_dw_broom₃, h_broom₃, h_dw_bushy, h_bushy): ~80 LOC
  (verbatim from cycle 370 lines 3022–3104).
* `h_dw_bushy₄`: ~30 LOC (cycle 370's `h_dw_bushy` ~30 LOC +
  one extra `h_prod_step_3` ~5 LOC).
* `h_bushy₄`: ~6 LOC (mirror `h_bushy`).
* `h_dws_bushy₄`: ~35 LOC (cycle 370's `h_dws_bushy` ~35 LOC +
  one extra `h_prod_step_3` ~5 LOC).
* Main computation `h_sum` + final `ring`: ~30 LOC (mirror
  cycle 370 lines 3141–3169).

Total: ~180 LOC. Strict upper bound: 250 LOC.

### §9.3 Non-vacuity `example` at `⟦explicitEuler⟧`

After the main theorem, add:

```lean
/-- *Phase α'.5.2.0 non-vacuity (cycle 499)*. -/
example :
    elementaryWeightQ_phi
        ((Quotient.mk PhiEquivalent.setoidSigma
            ⟨1, RKTableau.explicitEuler⟩))⁻¹
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex,
           RootedTree.vertex, RootedTree.vertex])
      = -1 := by
  rw [elementaryWeightQ_phi_inv_bushy₄, ...]
  -- All Φ_η values at explicitEuler: vertex = 1, cherry = 0,
  -- broom₃ = 0, bushy = 0, bushy₄ = 0.
  norm_num
```

Expected value: `-1⁵ + 4·1³·0 - 6·1²·0 + 4·1·0 - 0 = -1`. ~10 LOC.

### §9.4 `bushy₄` named alias (optional)

Cycle 499 worker decides whether to introduce a named
`bushy₄ := mk [v, v, v, v]` alias in `OpenMath/Chapter3/Section310/`
(or `Section301/`) for ergonomic reasons. If yes, ~5 LOC + bridge
theorem (`bushy₄_def : bushy₄ = mk [v,v,v,v] := rfl`). Memory
`feedback_ring_def_opacity.md` applies: `ring` needs the explicit
`show ...` bridge.

**Recommendation**: introduce the alias if cycle 500's
`inversePolyTree_bushy₄` calibration witness benefits ergonomically.
Cycle 499's closed-form theorem can use the constructor form
directly since `_inv_mk` reduces from `mk [...]` not from `bushy₄`.

## §10 What this doc does NOT do

* **Does not ship any Lean code.** `Section422.lean` does not
  appear in `git diff` for cycle 498.
* **Does not attempt the cycle 365 sorry closure.** Per §6.5, that
  requires Phase α'.5.2 + β.1/γ extensions + Phase β.2 lift.
  Multi-cycle work, not in this doc's scope.
* **Does not pivot to a fresh entity.** The §422 cluster remains
  the strategic focus.
* **Does not modify cycle 497's Phase γ deliverable** or the
  cycle 495 scoping doc. Both remain valid as historical
  reference and (Phase γ) as the structural-induction
  scaffolding for cycle ~510's k=4 extension.
* **Does not submit to Aristotle.** Scoping cycles have no
  Aristotle target.
* **Does not increase `maxHeartbeats`** anywhere. CLAUDE.md rule.
* **Does not extend `inversePolyTree`'s arms unilaterally.** That's
  cycle 500's scope.
* **Does not write the `bushy₄` closed-form theorem.** That's
  cycle 499's α'.5.2.0 deliverable.
* **Does not commit to Phase α'.5.3 (k ≥ 5).** That's a future
  scoping doc decision after α'.5.2 closes.

## §11 Cross-references

### §11.1 Predecessor scoping docs (in chronological order)

* `.prover-state/issues/def_422B_path.md` (cycle 336) — overall
  `def:422B` Phases A–E roadmap.
* `.prover-state/issues/def_422B_phase_D_3_scoping.md` (cycle 357)
  — Phase D.3 sub-phases.
* `.prover-state/issues/def_422B_subLemmaA_inductive_plan.md`
  (cycle 373) — Sub-lemma A inductive plan.
* `.prover-state/issues/def_422B_phase_alpha_prime_scoping.md`
  (cycle 379) — Phase α' recursive `inversePolynomial` design.
* `.prover-state/issues/def_422B_phase_alpha_prime_family_C_scoping.md`
  (cycle 385) — Phase α'.4 Family C scoping.
* `.prover-state/issues/def_422B_phase_alpha_prime_family_bushy_scoping.md`
  (cycle 398) — Phase α'.4.3 bushy scoping.
* `.prover-state/issues/def_422B_phase_alpha_prime_5_scoping.md`
  (cycle 402) — Phase α'.5 k=3 non-symmetric scoping; drove
  cycles 403, 491–494's calibration ladder.
* `.prover-state/issues/def_422B_phase_beta_gamma_scoping.md`
  (cycle 495) — Phase β.1 + β.2 + γ scoping; drove cycles 496/497;
  flagged R6.B falsity in §12.

### §11.2 Lean ship locations (referenced by this doc)

* `Section422.lean:582` — cycle 358's `elementaryWeightQ_phi_inv_mk`
  (the per-row product expansion that drives §3's block
  decomposition). **VERIFIED** by cycle 498 worker via direct read.

* `Section422.lean:3011–3169` — cycle 370's
  `elementaryWeightQ_phi_inv_bushy` closed form (cycle 499's
  structural template). **VERIFIED** by cycle 498 worker.

* `Section422.lean:9455–9519` — cycle 387/388/391/393/396's
  `bichildCrossTerm` (`tetrachildCrossTerm` cascade precedent).

* `Section422.lean:9522–9554` — cycle 392's `monochildCrossTerm`
  (single-child analogue).

* `Section422.lean:9555–9586` — cycle 387's `bichildPolynomial`
  (k=2 precedent for the `*Polynomial` helpers).

* `Section422.lean:9588–9662` — cycle 399/403/491–494's
  `trichildCrossTerm` (`tetrachildCrossTerm` cascade direct precedent;
  5 named branches: `(v,v,v)`, `(v,v,c)`, `(v,c,c)`, `(v,v,mk[c])`,
  `(v,v,broom₃)`). **VERIFIED** by cycle 498 worker.

* `Section422.lean:9686–9693` — cycle 399's `trichildPolynomial`
  (the `tetrachildPolynomial` precedent). **VERIFIED** by cycle
  498 worker.

* `Section422.lean:9718–9733` — cycle 387/399's `inversePolyTree`
  5-arm recursion (the §2 extension site). **VERIFIED** by cycle
  498 worker. Cycle 500 modifies lines 9718–9733 to extend to
  6 arms.

* `Section422.lean:9909+` — cycle 400's `inversePolyTree_bushy`
  calibration witness (cycle 500's calibration witness template).

* `Section422.lean:9962+` — cycle 403's
  `inversePolyTree_mkVertexVertexCherry` calibration witness
  (cycle 501's calibration witness template).

* `Section422.lean:2272–2279` — cycle 365's
  `powRep_sum_eq_of_strict_subtree_agreement` grandfathered sorry;
  remains untouched until Phase β.2 unblock per §6.5.

### §11.3 Cycle task results

* `.prover-state/task_results/cycle_402.md` — Phase α'.5 scoping
  ship; precedent for this cycle's markdown-only deliverable.
* `.prover-state/task_results/cycle_495.md` — Phase β/γ scoping
  ship; precedent.
* `.prover-state/task_results/cycle_497.md` §"Discovery #3" and
  §"Suggested next approach" Option A — explicit endorsement of
  this cycle's Phase α'.5.2 scoping doc deliverable.

### §11.4 Source material

* `extraction/raw_text/ch04.txt:1148–1173` — Butcher §422 textbook
  source ("E group" and η_q derivation).
* `extraction/formalization_data/entities/def_422B.json` — entity
  metadata for `def:422B`.

### §11.5 Memory cross-links

* `feedback_simp_recursive_def_overunfolds.md` — cycle 499–509+
  calibration witnesses must use targeted `rw [name-eq-thm-...]`
  rather than `simp [inversePolyTree, ...]`. Applies verbatim to
  any new `tetrachildCrossTerm` branch unfold in cycle 500+.

* `feedback_ring_def_opacity.md` — Phase α'.5.2 calibration
  witnesses must insert `show ...` bridges to canonicalise
  `mk [...]` constructor terms before `ring`. Applies to
  `inversePolyTree_bushy₄` and downstream calibrations.

* `feedback_dws_cherry_factor_includes_v_aᵢ.md` — cycle 384/491's
  per-row factor analysis; applies to cycle 501+'s asymmetric
  quadruple `h_dws_*` derivations.

* `feedback_indexed_inductive_cases_disjoint.md` — `cases h` on
  disjoint `RootedTree.mk` constructors closes by `decide` /
  `cases h` directly in `tetrachildCrossTerm`'s `if_neg` cascades.

* `feedback_rootedtree_nested_induction.md` — applies to cycle
  ~510's Phase γ extension to k=4: the strong-induction-on-`order`
  pattern from cycle 497 generalises naturally.

* `feedback_fin_sum_univ_succ_coerce.md` — relevant for cycle 499's
  `derivativeWeight` / `derivativeWeightWithSrc` inner-sum
  manipulations.

* `project_butcher_D_operator.md` — `D ∈ G` is the §385b 1-stage
  generalized RK (`A=0, b=[1], c=[0], b₀=0`); used implicitly in
  the non-vacuity `example` at `⟦explicitEuler⟧` per §9.3.

* `feedback_planner_faithfulness_spotcheck.md` — cycle 499 worker:
  verify the §5 strawman closed form against the cycle 358
  `_inv_mk` direct expansion BEFORE committing.

## §12 Self-reference and success criteria

### §12.1 Cycle 498 ship

* Cycle 498 ships **this scoping doc** at
  `.prover-state/issues/def_422B_phase_alpha_prime_5_2_scoping.md`
  as its sole deliverable.
* Cycle 498 also:
  - Bumps `extraction/formalization_data/lean_status.json`
    `def:422B` row's `cycle_completed_at` field to 498.
    Status unchanged (`partial`).
  - Appends a cycle 498 closure annotation to `plan.md`'s
    `def:422B` row.
  - Writes `.prover-state/task_results/cycle_498.md`.
* Zero Lean changes (`git diff --stat` shows only
  `.prover-state/` paths + `plan.md` + `lean_status.json`
  cycle-stamp bump + the new scoping doc).
* `grep -c sorry OpenMath/Chapter4/Section422.lean` remains 5
  (4 docstring + 1 grandfathered cycle 365).
* §422 streak: 70 substantive + 5 doc → **70 substantive + 6 doc**
  (cycles 336–498).

### §12.2 Forward cycles

* **Cycle 499** ships Phase α'.5.2.0 (`elementaryWeightQ_phi_inv_bushy₄`
  closed form) per §6.1 and §9. LOC: ~190–210.
* **Cycle 500** ships Phase α'.5.2.1 (`tetrachildPolynomial` +
  `tetrachildCrossTerm` defs + 6-arm `inversePolyTree` +
  `inversePolyTree_bushy₄` calibration) per §6.2. LOC: ~90–110.
* **Cycles 501–509+** ship Phase α'.5.2.k (k=4 non-symmetric
  witnesses) per §6.3 and §5.3 empirical surface table. LOC:
  ~250–400 each.
* **Cycle ~510** ships Phase β.1 + γ k=4 extensions per §6.4.
  LOC: ~100–200.
* **Cycle ~511+** attempts Phase β.2 tree-order-bounded carve-out
  per §6.5 (or pivots to `nchildPolynomial` infrastructure).

### §12.3 Doc-level success criteria

* This doc exists at the prescribed path. ✓ (verified by cycle 498
  worker on commit).
* LOC count between 500 and 1500. ✓ (target ~800–1100).
* §1 cites cycle 497's R6.B finding and cycle 365 sorry's blocked
  status. ✓
* §3 enumerates all 16 k=4 blocks with selection sets, per-row
  factors, and outer-sum contributions. ✓
* §6 has sub-phase plan for α'.5.2.0 through at least α'.5.2.4. ✓
* §9 has concrete cycle 499 entry point with proof recipe sketch
  and LOC budget. ✓
* `lean_status.json` def:422B row has `cycle_completed_at: 498`. ✓
* `plan.md` has cycle 498 closure annotation on def:422B row. ✓
* Section422.lean NOT in `git diff` for cycle 498. ✓
* `grep -c sorry Section422.lean` = 5. ✓
* No new Lean files created. ✓
* No Aristotle submissions. ✓

### §12.4 Faithfulness check (cycle 498 scoping)

Per CLAUDE.md's "Pre-Commit Faithfulness Checklist":

* **No new `def` introduced** — this is a markdown-only scoping
  cycle.
* **No new `structure` introduced.**
* **No new `theorem` introduced.**
* **Sorry count unchanged** at 5 (4 docstring + 1 grandfathered
  code at Section422.lean:2279).
* **Sole deliverable** is this planning document.

Faithfulness is trivially satisfied (no formal claims made about
Butcher textbook content; all references to `Φ_η`, `Φ_{η⁻¹}`,
`inversePolyTree`, etc. are scoping-level discussions of
infrastructure design, not theorem ships).

## §13 Closing note

This doc establishes the design baseline for Phase α'.5.2, the
k=4 children extension of `inversePolyTree`. The §3 block
decomposition is mathematically grounded in cycle 358's `_inv_mk`
formula; the §4/§5 strawmans mirror cycles 387/399's k=2/k=3
infrastructure precedents; the §6 phase decomposition follows
the cycle 402 multi-cycle scoping precedent verbatim.

Cycle 499 worker: start with §9.1's recipe, mirror cycle 370's
bushy proof body, and ship the `bushy₄` closed-form theorem.
Cycle 500 worker: ship the def + 6-arm extension + first
calibration witness. Cycles 501+ workers: ship the non-symmetric
quadruple ladder per §5.3.

The §422 cluster's strategic momentum points toward cycle ~512+'s
eventual cycle 365 sorry closure. Phase α'.5.2 is the next
load-bearing brick in that path.

## §14 Cycle 499 closure

**Date:** 2026-05-20 (cycle 499).
**Status:** Phase α'.5.2.0 SHIPPED (axiom-clean).

### §14.1 What shipped

Two new public symbols + two non-vacuity examples in
`OpenMath/Chapter4/Section422.lean` (inserted after the cycle 494
`mkVertexVertexBroom₃` block, before the Phase α'.1 `chainTree` /
`inversePolyChain` section):

1. **`elementaryWeightQ_phi_inv_bushy₄`** — the headline order-5
   broom closed form per §9.1:
   ```
   Φ_{η_q⁻¹}(bushy₄) = -(Φ_η(vertex))^5
                       + 4 · (Φ_η(vertex))^3 · Φ_η(cherry)
                       − 6 · (Φ_η(vertex))^2 · Φ_η(broom₃)
                       + 4 · Φ_η(vertex) · Φ_η(bushy)
                       − Φ_η(bushy₄)
   ```
2. Non-vacuity `example` at `⟦explicitEuler⟧` pinning the closed
   form to `-1` (vertex weight 1, all higher-order weights 0).
3. **`powRep_sum_eq_of_agreement_at_bushy₄_zero`** — Priority 2
   m=0 sub-lemma A specialisation (five-hypothesis variant
   covering vertex/cherry/broom₃/bushy/bushy₄ agreement).
4. Reflexive `example` at `η_q = η_q' = ⟦explicitEuler⟧` for the
   m=0 corollary, discharging five `rfl` agreements.

LOC delta: +368 LOC (Section422.lean 12564 → 12932). Within the
§B.4 strict 280 LOC budget bound only when measured as the
Priority 1 theorem body (~250 LOC); Priorities 2/3 (+docstrings)
bring the total to +368.

### §14.2 Proof template fidelity

The proof body mirrors cycle 370's `elementaryWeightQ_phi_inv_bushy`
verbatim:

* All 9 cycle 367/368/370 helpers (`h_inv_v`, `h_vertex`,
  `h_dw_cherry`, `h_cherry`, `h_dw_broom₃`, `h_broom₃`,
  `h_dw_bushy`, `h_bushy`, `h_dws_bushy` — actually `h_dws_bushy`
  was inlined, not separately reused, since the layer-3 expansion
  is captured directly inside `h_dws_bushy₄`'s nested helpers).
* Three new helpers (`h_dw_bushy₄`, `h_bushy₄`, `h_dws_bushy₄`)
  extending cycle 370 with one extra `h_prod_step_3` cons-case
  unfold layer.
* Main computation: `_inv_mk` + `_mk` × 5, then
  `h_sum` substitution + `sum_add_distrib` / `sum_sub_distrib`
  ×4 + `mul_sum` ×4 + 5 helper rewrites + `ring`.

### §14.3 Sign verification (confirmed at compile)

Per §5.1's binomial expansion `(s − v)⁴ = s⁴ − 4s³v + 6s²v² −
4sv³ + v⁴`, sum against `M.b i`, apply outer `-Σᵢ` from
`_inv_mk`. The compiled `h_sum` step factored:

```
+ Φ_η(bushy₄)             ← +Σᵢ M.b i · s⁴
- 4·Φ_η(vertex)·Φ_η(bushy) ← -4·v · Σᵢ M.b i · s³
+ 6·Φ_η(vertex)²·Φ_η(broom₃) ← +6·v² · Σᵢ M.b i · s²
- 4·Φ_η(vertex)³·Φ_η(cherry) ← -4·v³ · Σᵢ M.b i · s
+ Φ_η(vertex)⁵            ← +v⁴ · Σᵢ M.b i = v⁵
```

After negating, this matches the headline:
`-v⁵ + 4v³c − 6v²b' + 4v·bu − Φ_η(bushy₄)`. ✓

### §14.4 §F pre-commit checklist (cycle 499 actual results)

1. `lake env lean OpenMath/Chapter4/Section422.lean` exit 0
   (only diagnostic: the pre-existing cycle 365 grandfathered
   sorry warning at line 2279/2272 — unchanged). ✓
2. `grep -c sorry` = 5 (unchanged from cycle 498). ✓
3. `#print axioms elementaryWeightQ_phi_inv_bushy₄` returns
   `[propext, Classical.choice, Quot.sound]`. ✓ (verified post-
   `lake build`).
4. `#print axioms powRep_sum_eq_of_agreement_at_bushy₄_zero`
   returns the same. ✓
5. Non-vacuity example pins to `-1`. ✓
6. No tautology-scanner regex hits introduced beyond the
   cycle 498 baseline. ✓

### §14.5 Deviations from §B recipe

None of substance. Minor structural notes:

* `h_dws_bushy` from cycle 370 was *not* reused as a separate
  named helper inside `_inv_bushy₄`'s body. Instead, the layer-3
  cons-case unfold is performed directly inside `h_dws_bushy₄`'s
  nested `h_prod_step_3` step. This avoids redundant helper
  derivation and keeps the per-helper LOC footprint identical to
  cycle 370's three-helper bushy block.
* The `h_sum` `sum_*_distrib` chain order is
  `add, sub, add, sub` (in proof order, applied outer-most to
  innermost). This reflects the per-summand expansion's
  `… + Σᵢ M.b i · v⁴` final-term outer addition vs cycle 370's
  `… - v³ · Σᵢ M.b i` final-term outer subtraction — sign-flip
  arises from the parity of the binomial expansion (depth 4 vs
  depth 3).

### §14.6 Discovery

* The cycle 370 nested-helper recipe extends cleanly to depth 4
  with one additional `h_prod_step_3` layer per helper. Inductive
  step is **purely mechanical**: each additional child contributes
  one `show + rw` block. This validates the scoping doc §6.2's
  Phase α'.5.2.1 LOC estimate (~90–110 LOC for cycle 500's
  `tetrachildPolynomial` def + 6-arm `inversePolyTree` extension
  + calibration witness).
* The sign pattern `(-1, +4, -6, +4, -1)` in the binomial
  coefficient row matches the standard `(s − v)⁴` expansion (the
  same Pascal-triangle row that gave cycle 370 its `(+1, -3, +3,
  -1)` depth-3 signs). Phase α'.5.2.k k>0 (non-symmetric
  quadruples per §5.3) should reuse the same depth-4 binomial
  expansion in `h_sum`, with the per-summand `(M.A·s_j)^k_j`
  factorisation differing only in the inner-sum bookkeeping.

### §14.7 Forward agenda

* Cycle 500: ship Phase α'.5.2.1 per the scoping doc §6.2 —
  `tetrachildPolynomial` + `tetrachildCrossTerm` defs + 6-arm
  `inversePolyTree` pattern match + `inversePolyTree_bushy₄`
  calibration witness. ~90–110 LOC. Build cost may approach 1500s
  per cycle 401's 5-arm extension precedent; monitor and consider
  sibling-file extraction if exceeded.
* Cycle 501+: ship the non-symmetric quadruple ladder per §5.3,
  starting with `mkVertexVertexVertexCherry := mk[v, v, v, c]`
  (Block 6 single-cherry-arm contribution).

The §422 cluster's axiom-clean streak now stands at
**72 substantive + 6 doc** (cycles 336–499); sorry count remains
at 5 (4 docstring + 1 grandfathered cycle 365 sorry).

## §15 Cycle 501 update — Phase α'.5.2.2 `mk [vertex, vertex, vertex, cherry]` ship

### §15.1 What shipped

Five interlocking deliverables for the first non-symmetric k=4
quadruple `mk [vertex, vertex, vertex, cherry]` (order 6,
even-parity):

* **B.1** `elementaryWeightQ_phi_inv_mkVertexVertexVertexCherry`
  — quotient-level closed form with **12 monomials in 9 named
  kernels** (the strategy's paper sketch was 11/8; see §15.2).
* **B.2** `powRep_sum_eq_of_agreement_at_mkVertexVertexVertexCherry_zero`
  — m=0 corollary with 9 agreement hypotheses (Sub-lemma A
  specialisation per cycle 403 template).
* **B.3** `tetrachildCrossTerm` new `(vertex, vertex, vertex, cherry)`
  branch — 8-term residual `-v⁴c + 6v³b' - 3vcb' - 4v²bu + cbu
  + v·bushy₄ + 3v·vvc - 3v²·vc`. Back-computed from B.1 closed form
  minus Block (1)+(2)+(3)+(4)+(5)+(16) backbone of
  `tetrachildPolynomial`.
* **B.4** `inversePolyTree_mkVertexVertexVertexCherry` calibration
  witness — extends the cycle 491 k=3 template (with `show`-bridge
  for `f (mk [vertex]) ↔ f cherry`) to k=4 with one additional
  cherry-child layer.
* **B.5** `tetrachildCrossTerm_eq_of_subtree_agreement` Phase γ
  extension — adds second `by_cases h_vvvc` branch for the new
  `(v,v,v,c)` case (mandatory regression scope per cycle 500's
  Discovery #2).

Plus two `⟦explicitEuler⟧` non-vacuity examples (closed form = `+1`,
m=0 corollary by `rfl × 9`).

LOC added: ~750. Sorry count unchanged at 5.

### §15.2 The kernel inventory miss — strategy's paper derivation was wrong by one term

Per memory `feedback_dws_cherry_factor_includes_v_aᵢ.md`: the per-row
`derivativeWeightWithSrc` expansion at a cherry child unfolds to
`(v² − c) − v·Aᵢ + Bᵢ`, NOT `(v² − c) + Bᵢ`. The cycle 501 strategy's
§B.1 paper sketch dropped the `-v·Aᵢ` term.

The omitted `-v·Aᵢ` term, when multiplied by `(Aᵢ − v)³ = Aᵢ³ −
3v·Aᵢ² + 3v²·Aᵢ − v³`, produces a `-v · Aᵢ⁴` monomial. Summed against
`M.b i`, this is `Σ b · Aᵢ⁴ = M.elementaryWeight bushy₄`, surfacing
**`bushy₄` as a 9th kernel** beyond the strategy's 8-kernel sketch.

Corrected closed form (worker's symbolic re-derivation per strategy's
§G "trust the worker's derivation" directive):

```
Φ_{η_q⁻¹}(mk [v,v,v,c])
  = v⁶ − 5v⁴c + 3v²c² + 6v³·b' − 3vcb' − 4v²·bu + c·bu
    + v·bushy₄ + v³·m − 3v²·vc + 3v·vvc − vvvc
```

Sanity at `⟦explicitEuler⟧` (v=1, all higher kernels 0):
`1 − 0 + 0 + 0 − 0 − 0 + 0 + 0 + 0 − 0 + 0 − 0 = 1` ✓

The strategy's risk inventory R2 ("kernel inventory miss") was
correctly identified but the mitigation was wrong (the cherry-factor
is *not* linear in `S_c` alone — it's linear in both `Aᵢ` and `Bᵢ`).
The `ring` empirical verifier in B.4 caught the inconsistency
exactly as designed.

### §15.3 Generalization — every `(v, …, v, c)` k-tuple surfaces a new busher kernel

For any `mk [v, v, …, v, c]` with `k-1` vertex prefixes and one
cherry tail (`k ≥ 2`), the per-row factor is
`(Aᵢ − v)^{k-1} · ((v² − c) − v·Aᵢ + Bᵢ)`. Expanding gives an
`Aᵢ^k`-monomial with coefficient `-v`, summed to `Σ b · Aᵢ^k =
M.elementaryWeight (busher_{k+1})` where `busher_n = mk [v, …, v]`
with `n` vertex children (so `busher_2 = broom₃`, `busher_3 = bushy`,
`busher_4 = bushy₄`, `busher_5 = mk [v⁵]`, etc.).

So:

* `(v, c)` → cycle 372: surfaces `broom₃` (= busher_2).
* `(v, v, c)` → cycle 403: surfaces `bushy` (= busher_3).
* `(v, v, v, c)` → cycle 501: surfaces `bushy₄` (= busher_4).
* `(v, v, v, v, c)` → cycle 503+: will surface `busher_5 = mk [v, v, v, v, v]`.

This pattern recurs at every rung of the "vertex-prefix + cherry-tail"
ladder. Workers should anticipate this kernel by inspecting the
binomial expansion's leading `Aᵢ^k`-monomial.

### §15.4 Mechanical template for k=4 (cycle 502+ inheritance)

The cycle 491 P2 template scales directly to k=4 with these
modifications relative to the k=3 (cycle 491/492/493/494) recipe:

* **Three new helpers** (instead of two): `h_dw_mkVertexVertexVertexCherry`
  (4-layer cons-case unfold, `(Σⱼ Aᵢⱼ)^3 · (Σⱼ Aᵢⱼ · Σₖ Aⱼₖ)`),
  `h_mkVertexVertexVertexCherry` (sum form), and
  `h_dws_mkVertexVertexVertexCherry` (4-layer `derivativeWeightWithSrcProd`
  unfold extending cycle 403's k=3 template by one vertex layer).
* **9-term per-summand decomposition** in `h_subst` (instead of 7):
  (Aᵢ-power, Bᵢ-power) pairs `{(0,0), (1,0), (2,0), (3,0), (4,0),
  (0,1), (1,1), (2,1), (3,1)}`.
* **8 `Finset.sum_add_distrib` + 8 `← Finset.mul_sum`** (instead of
  6) — the last term has no scalar coefficient (the self-kernel
  `vvvc` directly back-substitutes via `← h_mkVertexVertexVertexCherry`).
* **9 back-substitutions**: `vvvc, vvc, vc, m, bushy₄, bushy, broom₃,
  cherry, vertex` (in `←` rewrite order).

### §15.5 Phase γ extension is non-optional

Cycle 500's Discovery #2 — extending `tetrachildCrossTerm` requires
extending `tetrachildCrossTerm_eq_of_subtree_agreement` — was
load-bearing for cycle 501. The B.5 ship adds a second `by_cases
h_vvvc` branch with 7 `h_closed _ (by decide)` kernel-discharges
(vertex/cherry/broom₃/bushy/bushy₄/mk[v,c]/mk[v,v,c], all of order
≤ 6 = order of `mk [v,v,v,c]`).

The default branch's `if_neg` chain becomes 4 long:
`rw [if_neg h_vvvv, if_neg h_vvvc, if_neg h_vvvv, if_neg h_vvvc]`.

### §15.6 Forward agenda

* **Cycle 502**: Phase α'.5.2.3 ship per scoping doc §5.3. Candidates:
  `(v, v, c, c)` (order 7, more cross-term richness, quadratic in Bᵢ),
  or `(v, c, c, c)` (order 8, cubic in Bᵢ), or `(v, v, v, mk[c])`
  (order 7, vertex-prefix + nested-cherry-tail). The single-cherry-tail
  ladder is exhausted at cycle 501 for k=4 (the `(v,v,v,c)` rung);
  next rungs introduce a second non-leaf child and need the cycle 384
  (`mk[c,c]`) / cycle 492 (`mk[v,c,c]`) machinery.
* **Cycle 503+**: continue ladder per the §5.3 enumeration, batching
  cases with similar kernel inventories where possible.

The §422 cluster's axiom-clean streak now stands at
**74 substantive + 6 doc** (cycles 336–501); sorry count remains
at 5 (4 docstring + 1 grandfathered cycle 365 sorry).

## §16 Cycle 502 update — Phase α'.5.2.3 `mk [v, v, c, c]` ship

### §16.1 Ship summary

Cycle 502 shipped Phase α'.5.2.3 in `OpenMath/Chapter4/Section422.lean`
(~1150 LOC). Five deliverables for the order-7 doubly-asymmetric
quadruple `mk [vertex, vertex, cherry, cherry]` (first k=4 case
with two non-leaf children):

* **B.1** `elementaryWeightQ_phi_inv_mkVertexVertexCherryCherry`:
  quotient-level closed form, **20 monomials in 12 named kernels**.
  The 12 kernels: `v, c, b', bu, bushy₄, m, vc, vvc, vvvc, cc, vcc,
  vvcc` (the new self-kernel `vvcc = mk [v,v,c,c]`).
* **B.2** `powRep_sum_eq_of_agreement_at_mkVertexVertexCherryCherry_zero`:
  m=0 corollary with 12 agreement hypotheses.
* **B.3** new `(v, v, c, c)` branch in `tetrachildCrossTerm` def
  body. **14-term cross-term**. Notable: `m = mk[c]` cancels between
  the Block (4)+(5) backbone and the B.1 closed form, so only
  10 kernels appear in the cross-term despite 12 in the closed form.
* **B.4** `inversePolyTree_mkVertexVertexCherryCherry` calibration
  witness (mechanical extension of cycle 501 template; new `if_neg
  (by decide), if_neg (by decide), if_pos ⟨rfl, rfl, rfl, rfl⟩`
  branch dispatch).
* **B.5** Phase γ extension of `tetrachildCrossTerm_eq_of_subtree_agreement`
  (mandatory regression scope per cycle 500's Discovery #2 —
  references **10 kernels** all of order ≤ 7 via `by decide`).

Plus two `⟦explicitEuler⟧` non-vacuity examples: closed-form witness
pinning to `-1` (order 7 odd, leading `-v⁷` survives) and the m=0
reflexive witness on `⟦explicitEuler⟧ = ⟦explicitEuler⟧` via 12 `rfl`s.

### §16.2 Closed form (B.1)

Per-row factor at `(t₁=v, t₂=v, t₃=c, t₄=c)` under
`inv_v = -v, inv_c = v² - c`:
```
(Aᵢ - v)² · ((v² - c) - v·Aᵢ + Bᵢ)²
```
where `Aᵢ = Σⱼ M.Aᵢⱼ` and `Bᵢ = Σⱼ Aᵢⱼ · Σₖ Aⱼₖ`. Note the `-v·Aᵢ`
correction per memory `feedback_dws_cherry_factor_includes_v_aᵢ.md`
— SQUARED into the expansion here (vs cycle 501's linear use).

Expansion gives 18 monomials in `(Aᵢ^j · Bᵢ^k)` for
`(j, k) ∈ {0..4} × {0..2}`. Summed against `bᵢ` and back-substituted
via the 12 kernels, then negated by the `Σ inv.b = -Σ b` substitution:

```
Φ_{η⁻¹}(mk [v,v,c,c])
  = -v⁷ + 6v⁵·c - 7v³·c² + 2v·c³
    - 6v⁴·b' + 6v²·c·b' - c²·b'
    + 4v³·bu - 2v·c·bu
    - v²·bushy₄
    - 2v⁴·m + 2v²·c·m
    + 6v³·vc - 4v·c·vc
    - 6v²·vvc + 2c·vvc
    + 2v·vvvc
    - v²·cc
    + 2v·vcc
    - vvcc
```

Sanity check at `⟦explicitEuler⟧` (v=1, all higher kernels 0):
`-1 + 0 - 0 + 0 - ... = -1` ✓ (order 7 odd-leading pattern, opposite
sign from cycle 501's even-order `+v⁶`).

### §16.3 Cross-term value (B.3) and m-cancellation

Subtracting `tetrachildPolynomial`'s Blocks 1+2+3+4+5+16 backbone at
`(v, v, c, c)`:

* Block 1: `-(v · (-v) · (-v) · (v²-c) · (v²-c)) = -v⁷ + 2v⁵c - v³c²`
* Blocks 2+3: `2·(-(-v · (v²-c)² · c)) = 2v⁵c - 4v³c² + 2vc³`
* Blocks 4+5: `2·(-((-v)·(-v) · (v²-c) · m)) = -2v⁴·m + 2v²·c·m`
* Block 16: `-vvcc`

Sum: `-v⁷ + 4v⁵c - 5v³c² + 2vc³ - 2v⁴·m + 2v²·c·m - vvcc`.

The B.1 closed form's m terms are exactly `-2v⁴·m + 2v²·c·m` —
matching the backbone exactly. So **m cancels** in the cross-term:

```
tetrachildCrossTerm v v c c f
  = 2v⁵·c - 2v³·c²
    - 6v⁴·b' + 6v²·c·b' - c²·b'
    + 4v³·bu - 2v·c·bu
    - v²·bushy₄
    + 6v³·vc - 4v·c·vc
    - 6v²·vvc + 2c·vvc
    + 2v·vvvc
    - v²·cc
    + 2v·vcc
```

14 terms across 10 kernels. The cycle 502 strategy's table listed
11 kernels in §B.5 (including m), but after symbolic verification
only 10 are referenced. Phase γ extension correspondingly references
10 kernels.

### §16.4 Mechanical template for k=4 ladders (cycle 503+ inheritance)

The cycle 502 ship confirms the cycle 501 template scales smoothly
to two cherry children. For future k=4 ladder rungs:

* Worker should derive per-row factor structure first
  (`(Aᵢ - v)^p · ((v² - c) - v·Aᵢ + Bᵢ)^q` for `p + q = 4`).
* Expand symbolically (paper or Python) to count kernels and monomials
  before writing Lean code. Strategy estimates may miss kernels.
* B.5 Phase γ extension must follow the kernel inventory of B.3
  (the cross-term), NOT B.1 (the closed form), since some kernels
  cancel between backbone and closed form. Use `simp [RootedTree.order]`
  / `by decide` to verify all kernels have order ≤ target tree order.
* For two-cherry-children patterns, expect `m = mk[c]` cancellation
  via Blocks (4)+(5) matching the closed form's m terms exactly
  (when both `t₃ = t₄ = cherry`).

### §16.5 Forward agenda

* **Cycle 503**: Phase α'.5.2.4 candidates per scoping doc §5.3:
  `(v, c, c, c)` (order 8, all three cherry children — full cubic
  in Bᵢ) is the natural next step. `(c, c, c, c)` (order 9, symmetric
  all-cherry) is the extreme.
* **Cycle 504+**: continue ladder. After ~3-5 more witnesses, cycle
  510+ planner can write a Phase β/γ extension scoping doc paralleling
  cycle 495's k=2/3 doc.

The §422 cluster's axiom-clean streak now stands at
**75 substantive + 6 doc** (cycles 336–502); sorry count remains
at 5 (4 docstring + 1 grandfathered cycle 365 sorry).

## §17 Cycle 503 update — Phase α'.5.2.4 `mk [v, c, c, c]` ship

### §17.1 Ship summary

Cycle 503 shipped Phase α'.5.2.4 in `OpenMath/Chapter4/Section422.lean`
(~1500 LOC). Five deliverables for the order-8 single-vertex-prefix +
three-cherry-tail quadruple `mk [vertex, cherry, cherry, cherry]`
(first k=4 case with three identical cherry children):

* **B.1** `elementaryWeightQ_phi_inv_mkVertexCherryCherryCherry`:
  quotient-level closed form, **27 monomials in 14 named kernels**.
  The 14 kernels: `v, c, b', bu, bu₄, m, vc, vvc, vvvc, cc, vcc,
  vvcc, ccc, vccc`. TWO new kernels surface: `ccc = mk[c,c,c]`
  (order 7, the symmetric three-cherry analogue of cycle 384's
  `mk[c,c]`) and the self-kernel `vccc = mk[v,c,c,c]` (order 8).
* **B.2** `powRep_sum_eq_of_agreement_at_mkVertexCherryCherryCherry_zero`:
  m=0 corollary with 14 agreement hypotheses.
* **B.3** new `(v, c, c, c)` branch in `tetrachildCrossTerm` def
  body. **22-term cross-term**. Notable: THREE kernels cancel
  between backbone and closed form (`v` via Block (1) `v·(v²-c)³`,
  `m` via Blocks (3)+(4)+(5) `3v·(v²-c)²·m`, and the self-kernel
  `vccc` via Block (16) `-vccc`). So only **11 kernels** appear in
  the cross-term: `c, b', bu, bu₄, cc, ccc, vc, vcc, vvc, vvcc, vvvc`.
* **B.4** `inversePolyTree_mkVertexCherryCherryCherry` calibration
  witness (mechanical extension of cycle 502 template; new `if_neg
  (by decide) × 3, if_pos ⟨rfl, rfl, rfl, rfl⟩` branch dispatch). The
  single `rw [inversePolyTree_cherry]` rewrites all three cherry-child
  occurrences in one pass (cycle 400/502 precedent).
* **B.5** Phase γ extension of `tetrachildCrossTerm_eq_of_subtree_agreement`
  (mandatory regression scope per cycle 500's Discovery #2 —
  references **11 cross-term kernels plus polynomial scalar `v`** =
  12 h_closed hypotheses, all of order ≤ 8 via `by decide`).

Plus two `⟦explicitEuler⟧` non-vacuity examples: closed-form witness
pinning to `+1` (order 8 even, leading `+v⁸` survives) and the m=0
reflexive witness on `⟦explicitEuler⟧ = ⟦explicitEuler⟧` via 14 `rfl`s.

### §17.2 Closed form (B.1)

Per-row factor at `(t₁=v, t₂=c, t₃=c, t₄=c)` under
`inv_v = -v, inv_c = v² - c`:
```
(Aᵢ - v) · ((v² - c) - v·Aᵢ + Bᵢ)³
```
where `Aᵢ = Σⱼ M.Aᵢⱼ` and `Bᵢ = Σⱼ Aᵢⱼ · Σₖ Aⱼₖ`. Note the `-v·Aᵢ`
correction per memory `feedback_dws_cherry_factor_includes_v_aᵢ.md`
— CUBED into the expansion here (vs cycle 502's squared use).

Expansion gives 14 non-zero `(Aᵢ^j · Bᵢ^k)` entries for
`(j, k) ∈ {0..4} × {0..3}`. Summed against `bᵢ` and back-substituted
via the 14 kernels, then negated by `Σ inv.b · dws = -Σ b · dws`
gives a 27-monomial sum (after expanding all polynomial coefficients).

Sanity check at `⟦explicitEuler⟧` (v=1, all higher kernels 0):
`+1 + 0 - 0 + ... = +1` ✓ (order 8 even-leading pattern, same sign
as cycle 499's even-order `+v⁵`).

### §17.3 Cross-term value (B.3) and m / v / vccc cancellation

Subtracting `tetrachildPolynomial`'s Blocks 1+2+3+4+5+16 backbone at
`(v, c, c, c)`:

* Block 1: `-(v · (-v) · (v²-c) · (v²-c) · (v²-c)) = v²·(v²-c)³`
* Block 2: `-((v²-c)³ · f(mk[v])) = -(v²-c)³ · c`  (since `f(mk[v]) = c`)
* Blocks 3+4+5: each `-(-v · (v²-c)² · m) = v·(v²-c)²·m`, sum = `3v·(v²-c)²·m`
* Block 16: `-vccc`

Sum: `v²·(v²-c)³ - (v²-c)³·c + 3v·(v²-c)²·m - vccc`.

The `v²·(v²-c)³` Block (1) coefficient (i.e., `v²` × polynomial in (v,c))
attaches to the polynomial scalar; the V-kernel contribution in the
closed form's coefficient `V·(V²-C)³ · V_kernel = V²·(V²-C)³` matches
exactly. Hence **`v` cancels**.

The B.1 closed form's `m` kernel coefficient is `3V·(V²-C)²` — matching
the backbone exactly. So **`m` cancels** in the cross-term.

The B.1 closed form's `vccc` self-kernel coefficient is `-1` — matching
Block (16)'s `-vccc` structurally. So **`vccc` cancels** in the
cross-term (this is the universal self-kernel cancellation per cycle
500's "Discovery #2").

Cross-term result: 22 monomials across 11 kernels (excluding the three
that cancelled). Phase γ extension correspondingly references 12
kernels (the 11 plus polynomial scalar `v`).

### §17.4 Discovery: cherry-child cancellation pattern

Building on cycle 502's Discovery #1 (`m` cancellation when both
`t₃ = t₄ = cherry`), cycle 503 confirms the general pattern: **as the
number of cherry children grows, more kernels cancel structurally**.

Specifically, at `(v, c^k, c^(K-k))`-shaped quadruples (vertex prefix
of length `K-k` + cherry tail of length `k`), expect the kernels
`mk[c^0]=v, mk[c^1]=m, mk[c^2]=cc, ..., mk[c^k]` plus the self-kernel
all to cancel structurally between backbone and closed form.

For cycle 503's `(v, c, c, c)` (k=3): `v`, `m`, `vccc` cancel.

For cycle 504's predicted `(c, c, c, c)` (k=4): expect `v`, `m`, `cc`,
and the self-kernel `cccc = mk[c,c,c,c]` to cancel. So 4 kernels
cancel, leaving (CF − 4) cross-term kernels.

### §17.5 Mechanical template for k=4 ladders (cycle 504+ inheritance)

The cycle 502 + 503 ships confirm the cycle 501 template scales smoothly
to two and three cherry children. For future k=4 ladder rungs:

* Worker should derive per-row factor structure first
  (`(Aᵢ - v)^p · ((v² - c) - v·Aᵢ + Bᵢ)^q` for `p + q = 4`).
* Expand symbolically via sympy (cycle 503 confirmed this as the
  preferred workflow). Symbolic verification catches sign errors
  and kernel counting errors before they appear in Lean's `ring`.
* B.5 Phase γ extension must follow the kernel inventory of B.3
  (the cross-term), NOT B.1 (the closed form), since some kernels
  cancel between backbone and closed form.
* For all-cherry-children patterns, expect `mk[c^k]` kernel cancellation
  for `k = 0..(number of cherry children)` and the self-kernel
  cancellation per §17.4.

### §17.6 Forward agenda

* **Cycle 504**: Phase α'.5.2.5 candidate per scoping doc §5.3:
  `(c, c, c, c)` (order 9, symmetric all-cherry — full quartic in Bᵢ,
  no vertex prefix). Predicted cross-term inventory: 8 kernels
  (excluding the 4 that cancel per §17.4).
* **Cycle 505+**: candidates `(v, v, v, mk[c])` (order 7, the `mk[c]`-child
  analog of cycle 493) and `(v, v, c, mk[c])` (order 8, mixed cherry +
  `mk[c]` children). These introduce non-leaf children for the
  quadruple-tree family.
* **Cycle 506+**: after ~5-6 more witnesses, planner can write a
  Phase β/γ k=4-extension scoping doc paralleling cycle 495's k=2/3 doc.

The §422 cluster's axiom-clean streak now stands at
**76 substantive + 6 doc** (cycles 336–503); sorry count remains
at 5 (4 docstring + 1 grandfathered cycle 365 sorry).
