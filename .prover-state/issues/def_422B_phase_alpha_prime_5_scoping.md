# Issue: `def:422B` Phase α'.5 scoping — non-symmetric `k ≥ 3` heterogeneous-children migration to `inversePolyTree`

## §1 Status & blocker

**Scoping doc, cycle 402.** No Lean code shipped this cycle — this is a
markdown-only research doc distilling cycle 399's `trichildPolynomial`
infrastructure into a concrete multi-cycle plan for extending
`inversePolyTree`'s `[c₁, c₂, c₃]` dispatch from its current
hard-coded `(vertex, vertex, vertex)`-only branch into a general
non-symmetric `k = 3` cross-term dispatch (and, eventually, a
`k = 4` extension).

This doc is the direct continuation of the markdown-only scoping
precedent established by cycles 373, 379, 385, and 398:

* `.prover-state/issues/def_422B_subLemmaA_inductive_plan.md` (cycle
  373 — 1399 lines, 11 sections; drove cycles 374–378's 8-tree
  ladder build-out).
* `.prover-state/issues/def_422B_phase_alpha_prime_scoping.md` (cycle
  379 — 1373 lines, 11 sections; drove cycles 380–383's Family A/B
  recursive helper ships).
* `.prover-state/issues/def_422B_phase_alpha_prime_family_C_scoping.md`
  (cycle 385 — 894 lines, 11 sections incl. §10/§11 appends; drove
  cycles 386–397's Phase α'.4.0 → α'.4.2 ladder of 11 substantive
  migrations).
* `.prover-state/issues/def_422B_phase_alpha_prime_family_bushy_scoping.md`
  (cycle 398 — 938 lines, 12 sections incl. §11/§12 appends; drove
  cycles 399–401's Phase α'.4.3 bushy migration in 3 substantive
  cycles).

**§422 axiom-clean streak: 63 substantive + 3 doc (cycles 336–401)**,
advancing to **63 substantive + 4 doc (336–402)** after this ship.
Single grandfathered sorry at `OpenMath/Chapter4/Section422.lean:2279`
(cycle 365's `powRep_sum_eq_of_strict_subtree_agreement` general
body); deferred to Phase β/γ extension scoping per cycle 401 §"Suggested
next approach" Option 2. Section422.lean: 8178 LOC. `grep -c sorry`
returns 5 (4 docstring references + 1 actual code sorry).

### §1.1 What's missing — the precise blocker

Cycle 399's `inversePolyTree` extension introduced a 5-arm match:

```lean
noncomputable def inversePolyTree : RT → (RT → ℝ) → ℝ
  | mk [],            f => -f vertex
  | mk [c],           f => -(v · inversePolyTree c f)
                            + monochildCrossTerm c f
                            - f (mk [c])
  | mk [c₁, c₂],      f => bichildPolynomial c₁ c₂
                            (inversePolyTree c₁ f) (inversePolyTree c₂ f) f
  | mk [c₁, c₂, c₃],  f => trichildPolynomial c₁ c₂ c₃
                            (inversePolyTree c₁ f) (inversePolyTree c₂ f)
                            (inversePolyTree c₃ f) f
  | mk (_::_::_::_::_), _ => 0
```

The `[c₁, c₂, c₃]` arm delegates to `trichildPolynomial` (cycle 399,
`Section422.lean:6439–6446`), whose `trichildCrossTerm` cross-term
(cycle 399, `Section422.lean:6410–6415`) currently dispatches **only**
`(vertex, vertex, vertex) → 3 · f vertex · f broom₃` and falls
through to `0` for every other triple. The structural consequence:

* All non-`(vertex, vertex, vertex)` `k = 3` trees route to a polynomial
  that is **mathematically incorrect**: the leading
  `-(v · inv₁ · inv₂ · inv₃)` block and the three
  `-(inv_{j} · inv_{k} · f (mk [t_ℓ]))` Block (2/3/4) contributions
  are correct (per the cycle 398 §3 block decomposition), but the
  Blocks (5)/(6)/(7) bilinear cross-terms and the Block (8) trilinear
  cross-term that surface for non-symmetric triples are dropped to
  `0` by the cross-term dispatch default.
* All `k ≥ 4` trees route to the catch-all `(_::_::_::_::_) → 0`,
  which is even more drastic: the entire polynomial is dropped to
  zero with no block contributions surfaced.

Empirically, the only `k = 3` closed form currently in Lean is cycle
370's `elementaryWeightQ_phi_inv_bushy` at
`Section422.lean:3011–3168` for the symmetric all-vertex triple
`bushy = mk [vertex, vertex, vertex]`. No non-symmetric `k = 3` tree
has been characterised in Lean yet. (Cycle 372's
`elementaryWeightQ_phi_inv_mkVertexCherry` at
`Section422.lean:3798–4061` covers `mk [vertex, cherry]` —
a `k = 2` heterogeneous binary tree — which is *not* the same
combinatorial regime, since `k = 2`'s Block decomposition has only 4
blocks, not 8.)

### §1.2 Why this matters

Phase α'.4 closure (cycle 401) achieves *uniform* `inversePolyTree`
routing for the 9-tree migration ladder, which is necessary for the
eventual collapse of `inversePolynomial_eq_of_subtree_agreement`'s
per-tree case analysis into a uniform structural recursion proof
(see cycle 401 §"Discovery" #3). However, the recursion is only
*pointwise correct* on the dispatched ladder trees; for any tree
outside the migration ladder (which includes ALL non-symmetric
`k = 3` trees and ALL `k = 4` trees), `inversePolyTree` returns a
"best-effort" polynomial that does not match the true
`Φ_{η_q⁻¹}` value.

This is acceptable as long as `inversePolynomial`'s if-then-else
dispatch chain only references trees that have been pointwise
calibrated. But Phase β/γ closure work (Option 2 in cycle 401
§"Suggested next approach") will eventually need a structural
induction over `RootedTree` that quantifies over arbitrary trees,
not just the 9-tree ladder. At that point, `inversePolyTree`'s
incorrectness on uncalibrated trees becomes a load-bearing
obstruction — every block decomposition step in the induction
either must be guarded by a "we are on the ladder" hypothesis (which
breaks the induction's quantifier structure) or must invoke a
correct-by-construction `inversePolyTree` (which is the Phase α'.5
deliverable).

Phase α'.5's role is to **incrementally widen the set of
`k = 3` and `k = 4` trees on which `inversePolyTree` is pointwise
correct**, with each cycle shipping (a) a new closed-form
`elementaryWeightQ_phi_inv_*` witness for one specific tree, (b) the
calibration witness `inversePolyTree_* = closed_form`, and (c) the
dispatch extension in `trichildCrossTerm` (or its `k = 4` analogue)
that realises the calibration. Eventually, by cycle 410+, the
dispatch matrix has enough entries that the Phase β/γ structural
induction can proceed for all "small" trees (Butcher §312's
order ≤ 5 set, which is the §422 group's order-of-accuracy
threshold).

## §2 Block decomposition for k ≥ 3 children (review and extension)

Cycle 398 §3 catalogued the 8 blocks for `k = 3`. This section
reviews them and extends to `k = 4` (16 blocks) for forward
reference.

### §2.1 `k = 3` block recap (from cycle 398 §3)

For `t = mk [t₁, t₂, t₃]`, cycle 358's `_inv_mk` unfolds:

```
M.inverse.derivativeWeightWithSrc i (mk [t₁, t₂, t₃])
  = Π_{ℓ∈{1,2,3}} ( M.inverse.elementaryWeight tℓ
                  + Σⱼ M.A i j · M.inverse.derivativeWeight j tℓ )
  = Π_ℓ ( inv_ℓ + S_ℓ(i) )
```

Expanding gives 8 blocks indexed by `{const, A-sum}³`:

| Block | Selection at (t₁, t₂, t₃) | Algebraic shape | Outer-sum contribution |
|---|---|---|---|
| (1) | c · c · c | `inv₁ · inv₂ · inv₃` | `-v · inv₁ · inv₂ · inv₃` |
| (2) | A · c · c | `S₁(i) · inv₂ · inv₃` | `-inv₂ · inv₃ · f (mk [t₁])` |
| (3) | c · A · c | `inv₁ · S₂(i) · inv₃` | `-inv₁ · inv₃ · f (mk [t₂])` |
| (4) | c · c · A | `inv₁ · inv₂ · S₃(i)` | `-inv₁ · inv₂ · f (mk [t₃])` |
| (5) | A · A · c | `S₁(i) · S₂(i) · inv₃` | bilinear cross-kernel `(t₁, t₂)` |
| (6) | A · c · A | `S₁(i) · inv₂ · S₃(i)` | bilinear cross-kernel `(t₁, t₃)` |
| (7) | c · A · A | `inv₁ · S₂(i) · S₃(i)` | bilinear cross-kernel `(t₂, t₃)` |
| (8) | A · A · A | `S₁(i) · S₂(i) · S₃(i)` | trilinear self-kernel surfacing `-f (mk [t₁, t₂, t₃])` |

**`trichildPolynomial` (cycle 399 ship) absorbs Blocks (1)–(4)
explicitly**, leaves `+trichildCrossTerm t₁ t₂ t₃ f` for the
Blocks (5)+(6)+(7) bilinear sum, and absorbs Block (8) into the
explicit `- f (mk [t₁, t₂, t₃])` self-term.

The cross-term `trichildCrossTerm t₁ t₂ t₃ f` is the only term
whose closed-form value depends on the specific triple. Phase α'.5's
work is to expand `trichildCrossTerm`'s `if-then-else` dispatch
into a per-triple cross-term cascade analogous to cycle 387/388's
`bichildCrossTerm` (which currently dispatches 3 binary pairs:
`(cherry, cherry)`, `(broom₃, cherry)`, `(vertex, cherry)`).

### §2.2 `k = 4` block extension (forward reference)

For `t = mk [t₁, t₂, t₃, t₄]`, cycle 358's `_inv_mk` unfolds into
`Π_{ℓ∈{1,2,3,4}} (inv_ℓ + S_ℓ(i))`, expanding to 16 blocks indexed
by `{const, A-sum}⁴`:

| Block range | Count | Description |
|---|---|---|
| (1) | 1 | All-const → `inv₁ · inv₂ · inv₃ · inv₄` |
| (2)–(5) | 4 | Single-A (one of four positions) → linear `f (mk [t_pos])` kernels |
| (6)–(11) | 6 | Two-A (one of six 2-subsets) → bilinear cross-kernels |
| (12)–(15) | 4 | Three-A (one of four 3-subsets) → trilinear cross-kernels |
| (16) | 1 | All-A → quadrilinear self-kernel surfacing `-f (mk [t₁, t₂, t₃, t₄])` |

The pattern generalises: for arity-`k`, the polynomial expansion has
`2^k` blocks indexed by `{const, A-sum}^k`, with binomial coefficient
`C(k, j)` blocks at each "A-count" `j ∈ {0, 1, ..., k}`. Cross-kernel
complexity scales combinatorially with `k`:
* `k = 3`: 1 + 3 + 3 + 1 = 8 blocks (cycle 399 ship).
* `k = 4`: 1 + 4 + 6 + 4 + 1 = 16 blocks (deferred to α'.5.3+).
* `k = 5`: 1 + 5 + 10 + 10 + 5 + 1 = 32 blocks (no current target).

**A natural `tetrachildPolynomial` / `tetrachildCrossTerm`
decomposition** for `k = 4` would mirror `trichildPolynomial`:

```lean
noncomputable def tetrachildPolynomial
    (t₁ t₂ t₃ t₄ : RT) (inv₁ inv₂ inv₃ inv₄ : ℝ) (f : RT → ℝ) : ℝ :=
  -(f RootedTree.vertex * inv₁ * inv₂ * inv₃ * inv₄)        -- Block (1)
    - inv₂ * inv₃ * inv₄ * f (mk [t₁])                       -- Block (2)
    - inv₁ * inv₃ * inv₄ * f (mk [t₂])                       -- Block (3)
    - inv₁ * inv₂ * inv₄ * f (mk [t₃])                       -- Block (4)
    - inv₁ * inv₂ * inv₃ * f (mk [t₄])                       -- Block (5)
    + tetrachildBilinear t₁ t₂ t₃ t₄ inv₁ inv₂ inv₃ inv₄ f   -- Blocks (6)–(11), 6 contributions
    + tetrachildTrilinear t₁ t₂ t₃ t₄ inv₁ inv₂ inv₃ inv₄ f  -- Blocks (12)–(15), 4 contributions
    - f (mk [t₁, t₂, t₃, t₄])                                -- Block (16) self-term
```

Each cross-term helper itself decomposes by triple/quadruple position.
This is a non-trivial design surface; deferred to α'.5.3+. See §6.

### §2.3 Pattern lock: `nchildPolynomial`?

Looking three or four steps ahead, the right abstraction may be a
single parametric-in-`k` recursive helper `nchildPolynomial`:

```lean
noncomputable def nchildPolynomial
    (children : List RT) (invs : List ℝ) (f : RT → ℝ) : ℝ :=
  -- Block expansion over 2^k subsets of `children.length`
  ∑ S in Finset.powerset (Finset.range children.length),
    sign(S) · Π_{ℓ ∉ S} inv_ℓ · crossKernel S children f
```

where `sign(S) = -1` if `|S| ∈ {0, 1}`-or-`children.length` (the
"absorbed" blocks per cycle 387/388 sign convention) and `+1`
otherwise (the cross-kernel blocks). This is *substantially* more
sophisticated than the current cycle 399 ship and is **NOT** a
Phase α'.5 target — it would be a Phase α'.7 or Phase α'.8
infrastructure ship, after the explicit `k = 3` and `k = 4`
witnesses have provided enough empirical anchor data to lock the
general pattern.

**Conclusion**: Phase α'.5 proceeds with explicit `trichildCrossTerm`
extension (sub-phases α'.5.0 / α'.5.1 / α'.5.2) and defers
`tetrachildPolynomial` / `nchildPolynomial` design to α'.5.3+
without committing to a timeline. See §6 for full sub-phase
decomposition.

## §3 Empirical data points and Phase α'.5.0 calibration target

### §3.1 Existing `k = 3` empirical data

**Only one**. Cycle 370's `elementaryWeightQ_phi_inv_bushy` at
`Section422.lean:3011–3168`:

```
Φ_{η_q⁻¹}(mk [vertex, vertex, vertex])
   = v⁴ − 3v²c + 3v·b' − Φ_η(bushy)
```

where `v = Φ_η(vertex), c = Φ_η(cherry), b' = Φ_η(broom₃)`. The
non-symmetric Block (5)+(6)+(7) cross-kernels at the all-vertex
triple collapse to `3v · b'` because each bilinear `(vertex, vertex)`
sub-kernel evaluates to `Σᵢ bᵢ · (Σⱼ Aᵢⱼ)² = Φ_η(broom₃) = b'`.

This is the **symmetric** case — all three children identical. It
does not exercise the `trichildCrossTerm` dispatch outside the
existing `(vertex, vertex, vertex)` branch.

### §3.2 Phase α'.5.0 entry target — `mk [vertex, vertex, cherry]`

The natural first non-symmetric `k = 3` tree is
`mk [vertex, vertex, cherry]`, which has Butcher-order **5** (sum
of `2 + 1 + 1 + 1 = 5`: root + 3 children, one of which is `cherry`
contributing one extra leaf). It is the smallest non-symmetric
`k = 3` tree by node count.

Its expected closed form (paper derivation; not yet shipped to Lean):

By the §2.1 block decomposition at `(t₁, t₂, t₃) = (vertex, vertex, cherry)`:

* `inv_vertex = M.inverse.elementaryWeight vertex = -v` (cycle 367 lift).
* `inv_cherry = M.inverse.elementaryWeight cherry = v² - c` (cycle 367).
* Block (1): `-v · (-v) · (-v) · (v² - c) = -v · v² · (v² - c) = -v⁴ + v²c`.
  Sign: with leading `-v`, evaluated at the outer `-Σ_i bᵢ · (...)`
  prefactor of `_inv_mk`, contributes `+v⁴ - v²c` to the closed form.
  Wait — let me re-check the sign. Cycle 398 §3 Block (1) at bushy
  gives `+v⁴`; at `mk [vertex, vertex, cherry]` it should give the
  analogous `-(-v) · (-v) · (v² - c) = -(v² · (v² - c)) = -v⁴ + v²c`.
  Then outer `-Σ_i bᵢ · (-v⁴ + v²c) = v · (v⁴ - v²c) = v⁵ - v³c`.
  But `trichildPolynomial`'s leading `-(f vertex · inv₁ · inv₂ · inv₃)
  = -(v · (-v)(−v)(v²-c)) = -(v · v²(v²-c)) = -(v⁴ - v²c) · v / v
  = -v⁴ + v²c` … this is wrong sign. **Lock-up at scoping time**:
  cycle 403's worker must symbolically verify the Block-(1) sign at
  `(vertex, vertex, cherry)` BEFORE committing to a closed form. The
  cycle 398 §7 R3 precedent applies — `bushy`'s symmetry happens to
  make the sign analysis cleaner; non-symmetric triples may surface
  cross-term sign subtleties not seen at `(vertex, vertex, vertex)`.

* Blocks (2)+(3)+(4): each is `-(inv_{j} · inv_{k} · f (mk [t_ℓ]))`.
  At `(vertex, vertex, cherry)`:
  - Block (2): `-(inv₂ · inv₃ · f (mk [t₁])) = -((-v) · (v² - c) · f cherry)
    = v(v²-c) · c = v³c - vc²`.
  - Block (3): symmetric. `-(inv₁ · inv₃ · f (mk [t₂])) = v³c - vc²`.
  - Block (4): `-(inv₁ · inv₂ · f (mk [t₃])) = -((-v)(-v) · f (mk [cherry]))
    = -v² · m` where `m := f (mk [cherry])`.

* Blocks (5)/(6): bilinear cross-kernels involving `(vertex, vertex)`
  pairs (Block 5) and `(vertex, cherry)` pair (Block 6). Block (5) at
  `(t₁, t₂) = (vertex, vertex)` surfaces `Σᵢ bᵢ · (Σⱼ Aᵢⱼ)² = b'`
  weighted by `inv₃ = (v² - c)`, contributing
  `-(v² - c) · b' = -v²b' + cb'` to the closed form. Block (6) at
  `(t₁, t₃) = (vertex, cherry)` surfaces the cycle 387's
  `bichildCrossTerm vertex cherry f = -v²c + v · b'` weighted by
  `inv₂ = -v`, contributing `-(-v) · (-v²c + vb') = v · (-v²c + vb')
  = -v³c + v²b'`. Block (7) at `(t₂, t₃) = (vertex, cherry)` is
  symmetric to Block (6) — contributes another `-v³c + v²b'`.

* Block (8): trilinear `(vertex, vertex, cherry)` cross-kernel surfaces
  `Σᵢ bᵢ · (Σⱼ Aᵢⱼ)² · (Σⱼ Aᵢⱼ · Σₖ Aⱼₖ) = ?` — this is a new
  cross-kernel not previously characterised. It is **plausibly**
  `f (mk [vertex, vertex, cherry])` itself (the self-kernel), which
  would absorb into the explicit `- f (mk [t])` self-term in
  `trichildPolynomial`. Cycle 403's worker should verify by direct
  computation against the cycle 358 `_inv_mk` unfold.

**Bottom line for §3.2**: the expected closed form for
`mk [vertex, vertex, cherry]` will surface **multiple** new cross-kernels
in `trichildCrossTerm`, including bilinear kernels reused from cycle
387's `bichildCrossTerm` (specifically `(vertex, vertex)` and
`(vertex, cherry)`). The cycle 403 worker should NOT attempt to
compute the closed form from scratch from `_inv_mk` — instead they
should:

1. Mirror cycle 372's `elementaryWeightQ_phi_inv_mkVertexCherry`
   proof structure (`Section422.lean:3798–4061`), substituting the
   third child `cherry → vertex` (i.e., handling the third child as
   a vertex instead of as part of the cherry pair).
2. Use the §2.1 block-by-block paper derivation as the *expected*
   closed form, then verify it matches the symbolic computation.

### §3.3 Other Phase α'.5 candidate trees

After `mk [vertex, vertex, cherry]` (α'.5.0 entry), the natural
continuation is — in increasing combinatorial complexity:

| Tree | Order | k | Notes |
|---|---|---|---|
| `mk [vertex, vertex, cherry]` | 5 | 3 | α'.5.0 entry (§3.2) |
| `mk [vertex, cherry, cherry]` | 6 | 3 | Two cherry leaves |
| `mk [cherry, cherry, cherry]` | 7 | 3 | All-cherry triple, symmetric |
| `mk [vertex, vertex, broom₃]` | 6 | 3 | Reuses cycle 388's `(vertex, broom₃)` knowledge |
| `mk [vertex, vertex, vertex, vertex]` | 5 | 4 | k=4 minimum; symmetric (analogue of bushy) |

The order column is the Butcher tree order (number of nodes). Note
that `mk [vertex, vertex, vertex, vertex]` at order 5 is the SAME
order as `mk [vertex, vertex, cherry]`, since both have 4 nodes total
under the root (the order-5 set has 9 elements per Butcher §312
Table 312(II)).

Phase α'.5 scope (cycles 403–408+, conservative estimate) covers
the first 3 of these (all `k = 3` cases). The 4th (`k = 4` symmetric)
is deferred to α'.5.3+. See §6.

## §4 Conjectured `trichildPolynomial` extension and dispatch

Cycle 399's `trichildPolynomial` body (`Section422.lean:6439–6446`)
is **already correct** for all `k = 3` triples — the block (1) through
block (4) structure is universal. The only thing that varies is the
`trichildCrossTerm` cross-term packaging.

Cycle 399's `trichildCrossTerm` (`Section422.lean:6410–6415`) is
currently:

```lean
noncomputable def trichildCrossTerm
    (t₁ t₂ t₃ : RT) (f : RT → ℝ) : ℝ :=
  if t₁ = RootedTree.vertex ∧ t₂ = RootedTree.vertex
      ∧ t₃ = RootedTree.vertex then
    3 * f RootedTree.vertex * f RootedTree.broom₃
  else 0
```

The Phase α'.5 dispatch extension is a per-triple cascade
analogous to cycle 387/388's `bichildCrossTerm`. Sketch:

```lean
noncomputable def trichildCrossTerm
    (t₁ t₂ t₃ : RT) (f : RT → ℝ) : ℝ :=
  if t₁ = RootedTree.vertex ∧ t₂ = RootedTree.vertex
      ∧ t₃ = RootedTree.vertex then
    3 * f RootedTree.vertex * f RootedTree.broom₃
  else if t₁ = RootedTree.vertex ∧ t₂ = RootedTree.vertex
       ∧ t₃ = RootedTree.cherry then
    -- closed form for `mk [vertex, vertex, cherry]` cross-term
    -- = sum of Block (5)/(6)/(7) bilinear contributions
    -- empirically: `-v²b' + cb' + 2(-v³c + v²b')`  (paper §3.2)
    -- consolidate: `(2v² - v²)b' + cb' - 2v³c = v²b' + cb' - 2v³c`
    -- TO BE CONFIRMED BY CYCLE 403 SYMBOLIC DERIVATION
    f RootedTree.vertex ^ 2 * f RootedTree.broom₃
      + f RootedTree.cherry * f RootedTree.broom₃
      - 2 * f RootedTree.vertex ^ 3 * f RootedTree.cherry
  else if t₁ = ... ∧ t₂ = ... ∧ t₃ = ... then
    ... (next triple)
  else 0
```

The dispatch grows with each empirical witness shipped. Cycle 403
ships the `(vertex, vertex, cherry)` branch; cycle 404+ ships
`(vertex, cherry, cherry)`; cycle 405+ ships `(cherry, cherry, cherry)`;
etc. **Each new branch is a separate substantive ship cycle**, with
recipe:

1. Symbolic derivation of the closed form from `_inv_mk` (paper +
   manual Lean verification scratch).
2. Ship a new `elementaryWeightQ_phi_inv_*` theorem mirroring cycle
   370's bushy / cycle 372's `mkVertexCherry` structure (∼250 LOC
   typical).
3. Ship a new `inversePolyTree_*` calibration witness theorem
   (∼30–50 LOC, mechanical).
4. Extend `trichildCrossTerm`'s `if-then-else` cascade with the
   new branch.
5. Update `inversePolynomial` if (and only if) the new tree is on
   the §422 dispatch ladder (which it might not be — see §3.3 caveat).

**Caveat for §4**: the paper closed form in §3.2 was sketched in
this scoping doc but **not** verified against cycle 358's `_inv_mk`.
Cycle 403's worker MUST do a clean symbolic derivation before
committing. The cycle 398 §7 R3 lesson (planner's strawman value was
correct after a sign re-check) applies — assume the strawman is
plausible but always verify.

## §5 Conjectured `tetrachildPolynomial` for `k = 4` (deferred)

For the eventual `k = 4` extension, sketch:

```lean
noncomputable def tetrachildPolynomial
    (t₁ t₂ t₃ t₄ : RT) (inv₁ inv₂ inv₃ inv₄ : ℝ) (f : RT → ℝ) : ℝ :=
  -(f RootedTree.vertex * inv₁ * inv₂ * inv₃ * inv₄)            -- Block (1)
    - inv₂ * inv₃ * inv₄ * f (mk [t₁])                            -- Block (2)
    - inv₁ * inv₃ * inv₄ * f (mk [t₂])                            -- Block (3)
    - inv₁ * inv₂ * inv₄ * f (mk [t₃])                            -- Block (4)
    - inv₁ * inv₂ * inv₃ * f (mk [t₄])                            -- Block (5)
    + tetrachildBilinear t₁ t₂ t₃ t₄ inv₁ inv₂ inv₃ inv₄ f        -- Blocks (6)–(11)
    + tetrachildTrilinear t₁ t₂ t₃ t₄ inv₁ inv₂ inv₃ inv₄ f       -- Blocks (12)–(15)
    - f (mk [t₁, t₂, t₃, t₄])                                     -- Block (16)
```

The `tetrachildBilinear` helper enumerates 6 position-pairs
`{(1,2), (1,3), (1,4), (2,3), (2,4), (3,4)}` and for each surfaces
a bilinear cross-kernel weighted by the product of the two
*non-selected* `inv_k` values. The `tetrachildTrilinear` helper
enumerates 4 position-triples and surfaces a trilinear cross-kernel
weighted by the single non-selected `inv_k`.

**Flagged risks for k = 4**:

* **Combinatorial explosion**: `tetrachildBilinear` alone has 6
  `if-then-else` branches per pair, each parametric in 3 tree
  identifiers (the two paired children + the third unpaired one).
  The dispatch matrix grows combinatorially.
* **Equation compiler unfolding-lemma cost**: cycle 399's
  Discovery and cycle 401's 1165s warm rebuild flagged that
  `inversePolyTree`'s 5-arm match generates many unfolding lemmas;
  adding a 6th arm for `[c₁, c₂, c₃, c₄]` will compound this. Cycle
  403+ workers should monitor build cost and consider abstracting
  `tetrachildPolynomial` into its own file if Section422 elaboration
  exceeds 1500s.
* **Catch-all bump**: extending to `k = 4` requires bumping the
  catch-all from `(_ :: _ :: _ :: _ :: _)` to
  `(_ :: _ :: _ :: _ :: _ :: _)`, mirroring cycle 399's pattern bump.

**`k = 4` is NOT a Phase α'.5.0/.1/.2 deliverable.** It's α'.5.3 at
the earliest. See §6 for the phase plan.

## §6 Phase decomposition

Phase α'.5 decomposes into 4 sub-phases analogous to Phase α'.4's
α'.4.0 / α'.4.1 / α'.4.2 / α'.4.3 structure.

### §6.1 Phase α'.5.0 — first non-symmetric `k = 3` empirical witness

**Single cycle**, estimated ~250–300 LOC.

* **Cycle 403 deliverable**: `elementaryWeightQ_phi_inv_mkVertexVertexCherry`
  — the closed-form theorem for `Φ_{η_q⁻¹}(mk [vertex, vertex, cherry])`.
* **Proof template**: mirror cycle 372's
  `elementaryWeightQ_phi_inv_mkVertexCherry`
  (`Section422.lean:3798–4061`), substituting the third child
  `cherry → vertex` (sic — third child is `cherry`, not vertex; but
  the proof structure mirrors the binary `mk [vertex, cherry]` ship
  scaled to three children with the additional bushy-style
  third-vertex handling).
* **Sub-steps**:
  1. Derive `M.derivativeWeight i (mk [vertex, vertex, cherry])`
     closed form (analogous to cycle 370's `h_dw_bushy` at
     `Section422.lean:3075–3104` but for the asymmetric triple).
  2. Derive `M.derivativeWeightWithSrc M.inverse i (mk [vertex, vertex, cherry])`
     closed form (analogous to cycle 370's `h_dws_bushy` at
     `Section422.lean:3105–3140`).
  3. Assemble the main computation via `_inv_mk` unfold + `_mk × 4`
     + sum algebra (analogous to cycle 370's lines 3141–3169).
* **LOC budget**: ~250–300 LOC (cycle 370's `bushy` ship was 159
  LOC; cycle 372's `mkVertexCherry` ship was 263 LOC; the
  `mkVertexVertexCherry` ship combines both regimes and should land
  in the 280–300 LOC range).
* **Aristotle integration**: try submitting the closed-form theorem
  to Aristotle for direct full-proof attempts. Cycle 370/372 did
  NOT use Aristotle (the manual `Finset.sum_congr; ring`-heavy
  template predates the cycle 388+ Aristotle workflow). Cycle 403's
  worker should try Aristotle on the full theorem AND on the major
  sub-helpers (`h_dw_*`, `h_dws_*`, `h_sum`); 30-min sleep
  per Aristotle policy.

### §6.2 Phase α'.5.1 — `trichildCrossTerm` dispatch extension

**Multi-cycle**, 1 cycle per new triple, estimated ~30 LOC per
addition.

Per cycle 401's Discovery #1 ("Phase α'.4.2 recipe fully stabilised"),
the recipe is mechanical:

* **Cycle 404** (or first available after α'.5.0): ship
  `inversePolyTree_mkVertexVertexCherry` calibration witness.
  Recipe: cycle 400's `inversePolyTree_bushy` template scaled
  to the asymmetric triple. ~30 LOC.
* **Cycle 405+ (multi-cycle)**: extend `trichildCrossTerm`'s
  `if-then-else` cascade with new triple branches as new closed
  forms are shipped.

### §6.3 Phase α'.5.2 — optional `inversePolynomial` body migration

**Conditional**, possibly 0 cycles.

For each new `k = 3` tree witness shipped in α'.5.0 / α'.5.1, check
whether it is on `inversePolynomial`'s if-then-else dispatch ladder
(per `Section422.lean:6900+` body). If yes, ship the 6-step migration
recipe (cycle 401 §12.1 template). If no, skip — the calibration
witness alone is sufficient for downstream Phase β/γ structural
induction work.

**Current observation**: NONE of the listed Phase α'.5 candidate
trees (§3.3 table) are on the current `inversePolynomial` dispatch
ladder. The 9 ladder trees were finalised at cycle 401; new ladder
entries would be a separate scoping decision belonging to a future
planner. **Default**: α'.5.2 ships 0 migrations and exists only as
a placeholder for the conditional.

### §6.4 Phase α'.5.3 — `k = 4` infrastructure (DEFERRED)

**Multi-cycle, no immediate target**. Estimated 3–5 cycles total.

* **Cycle X+1 (deferred)**: ship `tetrachildCrossTerm` placeholder
  helper (cycle 387's `bichildCrossTerm` template scaled to 4
  children; empty dispatch).
* **Cycle X+2 (deferred)**: ship `tetrachildBilinear` and
  `tetrachildTrilinear` placeholder helpers (empty dispatches).
* **Cycle X+3 (deferred)**: ship `tetrachildPolynomial` body
  combining the helpers per §5.
* **Cycle X+4 (deferred)**: extend `inversePolyTree`'s recursion
  with a new `[c₁, c₂, c₃, c₄]` arm and bump the catch-all to
  `(_ :: _ :: _ :: _ :: _ :: _)`.
* **Cycle X+5 (deferred)**: ship the first `k = 4` calibration
  witness, likely `inversePolyTree_mkVertexVertexVertexVertex` (the
  `k = 4` analogue of bushy — `Φ_{η_q⁻¹}(mk [v,v,v,v]) = ?` closed
  form to be derived).

Phase α'.5.3 only starts once Phase α'.5.0/.1 has accumulated enough
`k = 3` empirical data to lock the cross-term sign conventions for
arbitrary heterogeneous children. **Estimated start: cycle 408+**
(after 5+ α'.5.0/.1 cycles).

### §6.5 Total budget

| Sub-phase | Deliverable | Cycles | LOC |
|---|---|---|---|
| α'.5.0 | First `k = 3` non-symmetric closed form (cycle 403) | 1 | ~280 |
| α'.5.1 | `trichildCrossTerm` dispatch + calibrations | 3–5 | ~30 per |
| α'.5.2 | (Conditional) `inversePolynomial` migrations | 0–2 | ~50 per |
| α'.5.3 | `k = 4` infrastructure (DEFERRED) | 3–5 | ~80–200 per |
| **Total** | **Phase α'.5 full closure** | **7–13** | **~600–1500** |

Section422.lean projection: 8178 (current) → 8800–9700 (post-α'.5).
Warm rebuild cost projection: 1200s (current) → 1500–2000s (post-α'.5.3).

## §7 Risk inventory

**R1 — Cross-term sign discrepancy at non-symmetric triples**
(severity: MEDIUM). Phase α'.5.0's first non-symmetric witness may
surface a Block-(1) sign flip relative to bushy (the symmetric
case). The cycle 398 §7 R3 resolution was clean for bushy because
all three children were identical; non-symmetric triples mix
different `inv_ℓ` sign conventions and the leading
`-(v · inv₁ · inv₂ · inv₃)` term may need adjustment.

**Mitigation**: cycle 403 worker MUST derive Block (1) at
`(vertex, vertex, cherry)` symbolically from `_inv_mk` before
finalising the closed form. The §3.2 paper derivation above is
preliminary and contains a flagged sign-check pending. If the
derivation reveals a sign issue, update `trichildPolynomial`'s
Block (1) convention to handle the heterogeneous case (possibly
via a `mul_neg` rearrangement).

**R2 — Build cost escalation** (severity: MEDIUM). Cycle 401
measured a 1165s warm rebuild; cycle 399 Discovery flagged the 5-arm
`inversePolyTree` match as the load-bearing cause. Phase α'.5
adds:

* α'.5.1 cycles: ~30 LOC each, no new `inversePolyTree` arms.
  Build cost should remain ~1200s.
* α'.5.3 cycles: bump from 5 arms to 6 arms in `inversePolyTree`.
  Worst-case projection: 1500–2000s.

**Mitigation**: Phase α'.5.3 workers should monitor build times; if
warm rebuilds exceed 1500s, consider extracting the `tetrachild*`
helpers into a new file (e.g., `OpenMath/Chapter4/Section422/TetraChild.lean`)
to limit equation-compiler scope.

**R3 — Cross-term explosion for `k = 4`** (severity: LOW–MEDIUM,
not immediate). The 6 bilinear + 4 trilinear cross-kernel cases for
`k = 4` mean `tetrachildBilinear` + `tetrachildTrilinear` will have
combinatorially many `if-then-else` branches once empirical data
arrives. The cycle 387's 3-branch `bichildCrossTerm` and cycle
399's 1-branch `trichildCrossTerm` patterns do NOT scale linearly;
each tree-shape branch may require a multi-term polynomial
expression (e.g., §3.2's expected
`v²b' + cb' - 2v³c` for `(v, v, c)`).

**Mitigation**: when Phase α'.5.3 starts (cycle 408+), the planner
should evaluate whether a `nchildPolynomial` parametric-in-`k`
helper is justified per §2.3. Defer the decision to the cycle that
opens α'.5.3 scoping.

**R4 — `inversePolynomial` ladder churn** (severity: LOW). If a
future planner decides to add `mk [vertex, vertex, cherry]`,
`mk [cherry, cherry, cherry]`, etc. to `inversePolynomial`'s
dispatch ladder, the Phase α.2 calibration `example`s, Phase β
bridges, and Phase γ branches all need extension. This is the cycle
391/393/396/397/401 mechanical migration recipe, ~50 LOC per tree.

**Mitigation**: Phase α'.5 default per §6.3 is to NOT extend
`inversePolynomial`'s ladder — the calibration witnesses alone
suffice for downstream Phase β/γ structural induction. If a future
planner reverses this default, budget +50 LOC per new ladder entry.

**R5 — Grandfathered cycle 365 sorry stays open** (severity: LOW,
but worth noting). Phase α'.5's work makes the cycle 365 sorry at
`Section422.lean:2279` structurally more attackable (more uniform
`inversePolyTree` routing), but does NOT itself close it. The
cycle 365 closure requires a separate per-tree subtree-agreement →
`linearResidualAt`-agreement bridge that has not yet been built;
this is Phase β/γ extension work (cycle 401 §"Suggested next
approach" Option 2).

**Mitigation**: Phase α'.5 explicitly does NOT touch
`Section422.lean:2279`. Phase β/γ extension is a separate
scoping ship (deferred).

**R6 — Faithfulness of `trichildPolynomial` at non-vacuous triples**
(severity: LOW). Cycle 399's `trichildPolynomial` was non-vacuous
ONLY at the `(vertex, vertex, vertex)` triple (via cycle 400's
calibration); non-symmetric triples currently route to the
`(else → 0)` branch of `trichildCrossTerm`. Phase α'.5.0's first
non-symmetric witness will be the FIRST exercise of `trichildPolynomial`
at a heterogeneous triple. If the §2.1 block decomposition has been
mis-specified, the discrepancy will surface at this cycle.

**Mitigation**: cycle 403 worker should run a scratch
non-vacuity `example` at `f = elementaryWeightQ_phi ⟦explicitEuler⟧`,
both before and after the calibration witness ship, to confirm
numerical consistency. The cycle 370 non-vacuity reference at
`Section422.lean:3176–3220` is the template.

## §8 Cycle 403 entry point

**Recommendation**: ship `elementaryWeightQ_phi_inv_mkVertexVertexCherry`
as the 10th data point in the cycle 366 §G Route B hypothesis
ladder (currently 9 trees catalogued through cycle 388/401's
calibration matrix).

### §8.1 Pre-flight tasks for cycle 403's worker

1. **Read cycle 370's `bushy` closed-form proof body** at
   `Section422.lean:3011–3168` (159 LOC; the symmetric `k = 3`
   ship). Note the structure:
   - Lines 3022–3074: helper lemmas for `M.elementaryWeight vertex`,
     `M.derivativeWeight i cherry`, `M.elementaryWeight cherry`,
     `M.derivativeWeight i broom₃`, `M.elementaryWeight broom₃`.
   - Lines 3075–3104: `h_dw_bushy` — `M.derivativeWeight i bushy =
     (Σⱼ M.A i j)^3`.
   - Lines 3105–3140: `h_dws_bushy` — `M.derivativeWeightWithSrc
     M.inverse i bushy = (M.inverse.elementaryWeight vertex +
     Σⱼ M.A i j)^3`.
   - Lines 3141–3169: main computation — `_inv_mk` unfold + sum
     algebra + `ring`.

2. **Read cycle 372's `mkVertexCherry` closed-form proof body** at
   `Section422.lean:3798–4061` (263 LOC; the asymmetric `k = 2`
   ship). Note the additional cross-helper layer:
   - The asymmetric ship's `h_dws_*` computation must track how
     `vertex` and `cherry` differ in their `derivativeWeight`
     scaling (cherry adds an inner `Σ_k A_{jk}` factor).
   - The final `h_sum` step combines cross-terms via explicit
     `Finset.sum_sub_distrib` / `Finset.sum_add_distrib` algebra
     before `ring`-closing.

3. **Mentally derive the closed form** for
   `mk [vertex, vertex, cherry]` from §2.1's block decomposition.
   Verify the §3.2 paper sketch's structure (do NOT trust the
   coefficient values; cross-check by direct expansion).

4. **Submit Aristotle batch** with ~5 sub-lemmas:
   - `h_dw_mkVertexVertexCherry` (the bare-`derivativeWeight`
     closed form).
   - `h_dws_mkVertexVertexCherry` (the inverse `derivativeWeightWithSrc`
     closed form).
   - The full `elementaryWeightQ_phi_inv_mkVertexVertexCherry`
     theorem at the top level.
   - 1–2 intermediate `h_sum`-style helpers.
   Sleep 30 min, check results.

5. **Write the theorem** at `Section422.lean:~4100` (immediately
   after cycle 372's `elementaryWeightQ_phi_inv_mkVertexCherry`).
   Mirror cycle 370/372's structure.

6. **Ship calibration witness** `inversePolyTree_mkVertexVertexCherry`
   immediately after (separate cycle if α'.5.1 is split, or same
   cycle if compact). Use cycle 400's `inversePolyTree_bushy` template
   scaled to the heterogeneous case.

7. **Update `trichildCrossTerm`** with the new
   `(vertex, vertex, cherry)` branch, dispatching to the closed-form
   value derived from the calibration. Use cycle 388's
   `(broom₃, cherry)` extension pattern as the template.

### §8.2 Proof recipe pattern

Mirror cycle 358 `_inv_mk` unfold → per-child product expansion →
cycle 387/388 helper reuse → `ring` close. Specifically:

```lean
theorem elementaryWeightQ_phi_inv_mkVertexVertexCherry
    (η_q : Quotient PhiEquivalent.setoidSigma) :
    elementaryWeightQ_phi (η_q⁻¹)
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry])
      = <closed-form RHS, to be derived; preliminarily ~6 terms
         per §3.2's expansion> := by
  refine Quotient.inductionOn η_q ?_
  rintro ⟨s, M⟩
  -- Helpers: reuse cycle 367's h_inv_v, h_vertex; cycle 367's
  -- h_dw_cherry, h_cherry; cycle 368's h_dw_broom₃, h_broom₃;
  -- cycle 369's h_inv_cherry; cycle 372's h_dws_cherry.
  -- New helper: h_dws_mkVertexVertexCherry — the asymmetric
  -- inverse triple-child derivative-with-src closed form.
  ...
  -- Main computation: _inv_mk + _mk × 4 + algebra + ring.
  rw [elementaryWeightQ_phi_inv_mk M ...,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk,
      elementaryWeightQ_phi_mk, elementaryWeightQ_phi_mk]
  have h_sum : ... := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_dws_mkVertexVertexCherry i, h_inv_v]
    ring
  rw [h_sum]; ring
```

Estimated 250–280 LOC (cycle 372's 263 LOC + ~20 LOC for the
extra third-child handling).

### §8.3 Calibration witness recipe (Phase α'.5.1, follow-up cycle)

Mirror cycle 400's `inversePolyTree_bushy` template
(`Section422.lean:6662+`). Sketch:

```lean
theorem inversePolyTree_mkVertexVertexCherry (f : RT → ℝ) :
    inversePolyTree
        (OpenMath.Chapter3.Section310.RootedTree.mk
          [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]) f
      = <closed-form RHS from §8.2> := by
  show inversePolyTree
      (OpenMath.Chapter3.Section310.RootedTree.mk
        [RootedTree.vertex, RootedTree.vertex, RootedTree.cherry]) f
      = _
  rw [inversePolyTree, inversePolyTree_vertex, inversePolyTree_cherry]
  unfold trichildPolynomial
  rw [show trichildCrossTerm RootedTree.vertex RootedTree.vertex
          RootedTree.cherry f = <closed-form cross-term> by
        unfold trichildCrossTerm
        rw [if_neg ..., if_pos ⟨rfl, rfl, rfl⟩]]
  -- Bridge: mk [vertex] = cherry, mk [cherry] = mk [cherry]
  show ... = ...
  ring
```

Estimated ~40–50 LOC. Memory `feedback_simp_recursive_def_overunfolds.md`
applies: use targeted `rw [name-eq-thm-...]` rather than `simp
[inversePolyTree, ...]`. Memory `feedback_ring_def_opacity.md` applies:
insert `show ...` bridges before `ring`.

## §9 Cross-references

### Predecessor scoping docs (in chronological order)

* `.prover-state/issues/def_422B_path.md` (cycle 336) — overall
  `def:422B` Phases A–E roadmap (~600 LOC, 9 sections).
* `.prover-state/issues/def_422B_phase_D_3_scoping.md` (cycle 357) —
  Phase D.3 sub-phases.
* `.prover-state/issues/def_422B_subLemmaA_inductive_plan.md` (cycle
  373 — 1399 lines) — Sub-lemma A inductive plan; first markdown-only
  scoping cycle.
* `.prover-state/issues/def_422B_phase_alpha_prime_scoping.md` (cycle
  379 — 1373 lines) — Phase α' recursive `inversePolynomial` design.
* `.prover-state/issues/def_422B_phase_alpha_prime_family_C_scoping.md`
  (cycle 385 — 894 lines) — Phase α'.4 Family C scoping; drove
  cycles 386–397.
* `.prover-state/issues/def_422B_phase_alpha_prime_family_bushy_scoping.md`
  (cycle 398 — 938 lines) — Phase α'.4.3 bushy scoping; drove
  cycles 399–401.

### Lean ship locations (cycles 370 / 372 / 387 / 399 / 400 / 401)

* `Section422.lean:582` — cycle 358's `_inv_mk` (the per-row product
  expansion that drives the §2 block decomposition).
* `Section422.lean:3011–3169` — cycle 370's
  `elementaryWeightQ_phi_inv_bushy` closed form (the §3.1 reference;
  cycle 403's structural template).
* `Section422.lean:3176–3220` — cycle 370's non-vacuity `example` at
  `⟦explicitEuler⟧` (value `1`; the §7 R6 reference).
* `Section422.lean:3798–4061` — cycle 372's
  `elementaryWeightQ_phi_inv_mkVertexCherry` (the §8 binary template;
  cycle 403's primary template scaling to three children).
* `Section422.lean:6283–6348` — cycle 387/388's `bichildCrossTerm`
  (template for `trichildCrossTerm` cascade extension).
* `Section422.lean:6350–6381` — cycle 392's `monochildCrossTerm` (the
  single-child analogue).
* `Section422.lean:6383–6389` — cycle 387's `bichildPolynomial`
  (the `k = 2` precedent for the `k = 3` and `k = 4` `*Polynomial`
  helpers).
* `Section422.lean:6410–6415` — cycle 399's `trichildCrossTerm` (the
  §4 cascade extension site for Phase α'.5.1).
* `Section422.lean:6439–6446` — cycle 399's `trichildPolynomial` (the
  Block (1)–(4) body; already correct, no Phase α'.5 changes needed).
* `Section422.lean:6471–6486` — cycle 387/399's `inversePolyTree`
  5-arm recursion (the §6.4 extension site for Phase α'.5.3).
* `Section422.lean:6662+` — cycle 400's `inversePolyTree_bushy`
  calibration witness (the §8.3 template).

### Cycle 401 task results (entry-point reference)

* `.prover-state/task_results/cycle_401.md` §"Suggested next
  approach" — explicit endorsement of Phase α'.5 (Option 1) as the
  cycle 402 deliverable.
* `.prover-state/task_results/cycle_401.md` §"Discovery" #1 — the
  Phase α'.4.2 6-step migration recipe, applicable to Phase α'.5.2
  (if it materialises).
* `.prover-state/task_results/cycle_401.md` §"Discovery" #2 — the
  1165s warm-rebuild cost flag, applicable to §7 R2 budgeting.
* `.prover-state/task_results/cycle_401.md` §"Discovery" #3 — Phase
  α'.4 closure milestone; the structural precondition that makes
  Phase α'.5 work productive.

### Source material

* `extraction/raw_text/ch04.txt:1148–1173` — Butcher §422 textbook
  source ("E group" and η_q derivation).
* `extraction/formalization_data/entities/def_422B.json` — entity
  metadata for `def:422B`.

### Memory cross-links

* `feedback_simp_recursive_def_overunfolds.md` — cycle 403/404's
  calibration theorems must use targeted `rw [name-eq-thm-...]`
  rather than `simp [inversePolyTree, ...]`; applies verbatim to
  any new `trichildCrossTerm` branch unfold.
* `feedback_ring_def_opacity.md` — Phase α'.5's calibration witnesses
  must insert `show ...` bridges to canonicalise `mk [vertex] = cherry`,
  `mk [cherry] = mk [cherry]`, `mk [vertex, vertex, cherry] = <non-named>`
  (the asymmetric triple has no named alias — no `show` bridge needed
  for the self-term, but the `cherry` and `mk [cherry]` sub-terms
  still need explicit `show`s).
* `feedback_indexed_inductive_cases_disjoint.md` — `cases h` on
  disjoint `RootedTree.mk` constructors closes by `decide` / `cases h`
  directly in the `trichildCrossTerm` `if_neg` cascades.
* `feedback_fin_sum_univ_succ_coerce.md` — relevant for the
  `derivativeWeight` / `derivativeWeightWithSrc` inner-sum
  manipulations in Phase α'.5.0's closed-form proof.

## §10 Self-reference and success criteria

### §10.1 Cycle 402 ship

* Cycle 402 ships **this scoping doc** at
  `.prover-state/issues/def_422B_phase_alpha_prime_5_scoping.md`
  as its sole deliverable.
* Cycle 402 also bumps `extraction/formalization_data/lean_status.json`
  `def:422B` row's `cycle_completed_at` field to 402; bumps
  `plan.md` `def:422B` row to reference cycle 402; writes
  `.prover-state/task_results/cycle_402.md`.
* Zero Lean changes (`git diff --stat` shows only `.prover-state/`
  paths + `plan.md` + `lean_status.json` cycle-stamp bumps).
* `grep -c sorry OpenMath/Chapter4/Section422.lean` remains 5.

### §10.2 Forward cycles

* Cycle 403 ships Phase α'.5.0 (`elementaryWeightQ_phi_inv_mkVertexVertexCherry`)
  per §8.
* Cycle 404+ ships Phase α'.5.1 (`inversePolyTree_mkVertexVertexCherry`
  calibration + `trichildCrossTerm` dispatch extension) per §6.2.
* Cycle 405+ ships further `k = 3` non-symmetric witnesses per
  §3.3 candidate list.
* Cycle 408+ (deferred): Phase α'.5.3 `k = 4` infrastructure per
  §6.4.
* Throughout: cycle 365 grandfathered sorry remains open; closure
  is a separate Phase β/γ extension scoping ship belonging to a
  future planner.

### §10.3 Cycle 402 success criteria

* New file at `.prover-state/issues/def_422B_phase_alpha_prime_5_scoping.md`
  (this file) with ~600 lines spanning §1–§10.
* §3 catalogues the existing cycle 370 bushy data point and
  identifies the cycle 403 target (`mk [vertex, vertex, cherry]`).
* §4 explicitly references cycle 399's hard-coded
  `(vertex, vertex, vertex)` branch in `trichildCrossTerm` and pins
  the generalisation target (per-triple `if-then-else` cascade).
* §6 phase decomposition has 4 sub-phases (α'.5.0 / α'.5.1 / α'.5.2 /
  α'.5.3) with LOC estimates and cycle-count estimates.
* §8 cycle 403 entry point is concrete: names the target tree
  (`mk [vertex, vertex, cherry]`), the estimated LOC (~250–280),
  and the proof template to mirror (cycle 372's binary
  `mkVertexCherry` ship plus cycle 370's symmetric three-child
  `bushy` ship).
* Zero Lean changes.
* `lean_status.json` `def:422B` row's `cycle_completed_at` bumped
  from 401 to 402.
* `plan.md` `def:422B` row bumped to reference cycle 402.
* §422 axiom-clean streak advances: 63 substantive + 3 doc → **63
  substantive + 4 doc** (cycles 336–402).

### §10.4 What this doc deliberately does NOT do

* Does NOT ship any new Lean definitions (`trichildCrossTerm`
  extensions, `tetrachildPolynomial`, etc.). Phase α'.5.0/.1/.2/.3
  work, deferred to cycles 403+.
* Does NOT ship calibration witnesses (`inversePolyTree_*`). Phase
  α'.5.1 work, deferred to cycle 404+.
* Does NOT touch `inversePolynomial`'s if-then-else dispatch ladder.
  Phase α'.5.2 work, deferred and conditional per §6.3.
* Does NOT touch the cycle 365 grandfathered sorry at
  `Section422.lean:2279`. Phase β/γ extension scoping ship,
  separate from Phase α'.5.
* Does NOT lock the `k = 4` infrastructure design. §5 sketches
  `tetrachildPolynomial` but flags the design as deferred to α'.5.3+,
  with a possible pivot to `nchildPolynomial` parametric-in-`k`
  abstraction per §2.3.
* Does NOT pivot to a fresh entity. The §422 streak is productive;
  cycle 401 §"Suggested next approach" Option 1 was the cycle 402
  planner's choice, and Phase α'.5 work continues that track.

---

**End of scoping doc.** Cycle 402 ships this markdown file; cycle
403 ships Phase α'.5.0 per §8; cycles 404+ ship Phase α'.5.1 per
§6.2 incrementally as new `k = 3` empirical witnesses surface.
Phase α'.5.3 (`k = 4` infrastructure) deferred to cycle 408+ as the
multi-cycle infrastructure ship that follows once enough `k = 3`
empirical anchor data has accumulated.

---

## §11 Cycle 491 closure — Phase α'.5.1 P1+P2 ship

**Status: SHIPPED.** Phase α'.5.1 P1+P2 closed at cycle 491.

### §11.1 What shipped

1. **`trichildCrossTerm` extension** (`Section422.lean:7020–7046`).
   The cycle 399 single-branch body
   `if (t₁, t₂, t₃) = (vertex, vertex, vertex) then 3·v·b' else 0`
   extended to a cascade with the second branch
   `else if (t₁, t₂, t₃) = (vertex, vertex, cherry) then v³c − 3v²·b'
   + c·b' + v·bushy + 2v·vc else 0`. Back-computed by subtracting
   `trichildPolynomial` Blocks (1)+(2)+(3)+(4) at
   `(inv_v, inv_v, inv_c) = (-v, -v, v² − c)` from cycle 403's
   9-kernel closed form per §B.1 of the cycle 491 strategy doc.

2. **`inversePolyTree_mkVertexVertexCherry`** calibration witness
   (`Section422.lean:7308–7387`, ~75 LOC inclusive of docstring).
   The 11th Family C inverse-polynomial calibration witness;
   confirms that the recursive `inversePolyTree` definition (cycles
   387/399) evaluates correctly on `mk [vertex, vertex, cherry]`
   against the cycle 403 quotient-level closed form. Proof recipe
   per §B.3 of the strategy doc: `rw [inversePolyTree,
   inversePolyTree_vertex, inversePolyTree_cherry]` (the
   `_vertex` rewrite fires globally on both `t₁ = t₂ = vertex`
   occurrences), `unfold trichildPolynomial`, then
   `rw [show trichildCrossTerm vertex vertex cherry f = … by
   unfold trichildCrossTerm; rw [if_neg (by decide),
   if_pos ⟨rfl, rfl, rfl⟩]]`, then a `show … = …` bridge for
   `f (mk [vertex]) ↔ f cherry` (per memory
   `feedback_ring_def_opacity.md`), then `ring`.

### §11.2 Regression checks

* `inversePolyTree_bushy` (cycle 400) re-verified axiom-clean:
  the new `else if (vertex, vertex, cherry)` branch only matches at
  the second-pattern conjunction `vertex = vertex ∧ vertex = vertex
  ∧ ?₃ = cherry`; at `?₃ = vertex` the FIRST `if`-branch fires
  (since `vertex = vertex` for all three components). So
  `rw [if_pos ⟨rfl, rfl, rfl⟩]` in cycle 400's proof still
  discharges to the original `3·v·b'` value unchanged.
* `elementaryWeightQ_phi_inv_mkVertexVertexCherry` (cycle 403)
  re-verified axiom-clean (no dependency on the cycle 399
  `trichildCrossTerm` body — it lives in the quotient layer
  directly, not the polynomial layer).
* Sorry count unchanged at 5 (4 docstring + 1 grandfathered cycle 365
  code at `Section422.lean:2279`).

### §11.3 Streak advance

§422 axiom-clean streak: 64 substantive + 4 doc (cycles 336–403)
→ **65 substantive + 4 doc** (cycles 336–491).

### §11.4 Cycle 492+ outlook

Per §6.2 + §3.3 candidate list, the next Phase α'.5.1 cycle ships
one more non-symmetric `k = 3` witness — natural candidates:

* `mk [vertex, cherry, cherry]` (order 6, asymmetric two-cherry
  cluster).
* `mk [vertex, vertex, broom₃]` (order 6, two-vertex + broom₃
  cluster).
* `mk [vertex, vertex, mk [cherry]]` (order 6, two-vertex + `[cherry]`
  cluster).

Each cycle adds one `else if` branch to `trichildCrossTerm` + one
`inversePolyTree_*` calibration. Cycle 492's planner picks per
mathematical interest and proof-complexity estimate; the strategy
doc §F outlook bullet is the entry point.

## §12 Cycle 492 closure — Phase α'.5.1 P3 ship

### §12.1 What shipped

* **Quotient-level closed form**
  `elementaryWeightQ_phi_inv_mkVertexCherryCherry` (cycle 492) for
  the order-6 asymmetric three-children tree
  `mk [vertex, cherry, cherry]`. The closed form has 14 monomials
  across 9 named sum-kernels:
  ```
  Φ_{η_q⁻¹}(mk [vertex, cherry, cherry])
     = v⁶ − 5v⁴c + 5v²c² − c³ + 3v³b' − 2vcb' − v²·bushy
       + 2v³m − 2vcm − 4v²·vc + 2c·vc + 2v·vvc + v·cc − M_vcc
  ```
  where `v, c, b', bushy, m, vc, vvc, cc, M_vcc` abbreviate `Φ_η`
  at vertex, cherry, broom₃, bushy, mk[cherry], mk[vertex,cherry],
  mk[vertex,vertex,cherry], mk[cherry,cherry], and the self-kernel
  mk[vertex,cherry,cherry] respectively.
  Paper derivation cross-checked numerically at `⟦explicitEuler⟧`
  (yields `1`, matching the leading `v⁶` term).
  21 helpers (cycles 367/368/369/370/372/384/403) reused verbatim
  + 3 new helpers (`h_dw_mkVertexCherryCherry`,
  `h_mkVertexCherryCherry`, `h_dws_mkVertexCherryCherry`).

* **m=0 corollary**
  `powRep_sum_eq_of_agreement_at_mkVertexCherryCherry_zero`
  (cycle 492) — specialisation of Sub-lemma A at `t = mk
  [vertex, cherry, cherry], m = 0`; nine agreement hypotheses
  (vertex, cherry, broom₃, bushy, mk[cherry], mk[vertex,cherry],
  mk[vertex,vertex,cherry], mk[cherry,cherry],
  mk[vertex,cherry,cherry]).

* **`trichildCrossTerm` extension** — third `else if` branch for
  `(vertex, cherry, cherry)` with the back-computed Blocks (5)+(6)+(7)
  trilinear cross-term value:
  ```
  −2v⁴c + 2v²c² + 3v³b' − 2vcb' − v²·bushy − 4v²·vc + 2c·vc
   + 2v·vvc + v·cc
  ```

* **Recursive calibration witness**
  `inversePolyTree_mkVertexCherryCherry` (cycle 492) matching the
  cycle 492 closed form verbatim under `f = elementaryWeightQ_phi η_q`.

* **Two non-vacuity `example`s** on `⟦explicitEuler⟧`:
  - closed-form witness pinning to `1` (the order-6 even-parity
    leading-`v⁶` value);
  - m=0 reflexive witness via 9 `rfl`s.

### §12.2 Regression checks

* Cycle 491's `inversePolyTree_mkVertexVertexCherry` re-verified
  axiom-clean after the `trichildCrossTerm` extension (the new
  `(vertex, cherry, cherry)` `if_neg` branch does not affect cycle
  491's `if_pos ⟨rfl, rfl, rfl⟩` discharge at `(vertex, vertex,
  cherry)`).
* Cycle 400's `inversePolyTree_bushy` re-verified axiom-clean (the
  first `(vertex, vertex, vertex)` branch still fires).
* Cycle 403's `elementaryWeightQ_phi_inv_mkVertexVertexCherry`
  re-verified axiom-clean (independent of `trichildCrossTerm`).
* All prior `inversePolyTree_*` calibration witnesses re-verified
  axiom-clean (the new branch only matches at
  `(vertex, cherry, cherry)`).
* `Section422.lean` compiles cleanly with only the cycle 365
  grandfathered sorry warning at line 2279.

### §12.3 Streak advance

§422 axiom-clean streak: 65 substantive + 4 doc (cycles 336–491)
→ **66 substantive + 4 doc** (cycles 336–492).

### §12.4 Cycle 493+ outlook

Two more non-symmetric `k = 3` candidates remain per §6.2 + §3.3:
* `mk [vertex, vertex, broom₃]` (order 6).
* `mk [vertex, vertex, mk [cherry]]` (order 6).

Each cycle adds one `else if` branch to `trichildCrossTerm` + one
`inversePolyTree_*` calibration. Cycle 493+ planners may also
consider transitioning to Phase α'.5.2 (k ≥ 4 trees) once the
`k = 3` ladder is sufficiently populated for downstream
machine-checked corollaries.

## §13 Cycle 493 closure — Phase α'.5.1 P4 ship

### §13.1 What shipped

* **Quotient-level closed form**
  `elementaryWeightQ_phi_inv_mkVertexVertexMkCherry` — `Φ_{η_q⁻¹}`
  at the order-6 tree `mk [vertex, vertex, mk [cherry]]`. 15
  monomials across 10 named sum-kernels: `vertex, cherry, broom₃,
  bushy, mk[cherry], mk[v,c], mk[v,v,c], mk[mk[cherry]],
  mk[v,mk[cherry]]`, plus the self-kernel `mk[v,v,mk[cherry]]`.
* **`trichildCrossTerm` extension** — fourth `else if` branch
  `(vertex, vertex, mk [cherry])`:
  ```
  -v⁴c + v³m + v²c² + 3v³b' - 4vcb' + mb'
    - v²·bu + c·bu - 2v²·vc + v·vvc + 2v·vmc
  ```
  Back-computed by subtracting Blocks (1)+(2)+(3)+(4)+(8) of
  `trichildPolynomial` at `(inv_v, inv_v, inv_mc) = (-v, -v,
  -v³ + 2vc - m)` from the closed-form RHS.
* **Calibration witness** `inversePolyTree_mkVertexVertexMkCherry`
  — 13th Family C witness; proof recipe identical to cycle
  491/492's: `rw [inversePolyTree, inversePolyTree_vertex,
  inversePolyTree_mkCherry]; unfold trichildPolynomial; rw [show
  trichildCrossTerm vertex vertex (mk [cherry]) f = ... by unfold;
  rw [if_neg × 3, if_pos]]; show <bridge>; ring`.
* **m=0 corollary**
  `powRep_sum_eq_of_agreement_at_mkVertexVertexMkCherry_zero` (10
  agreement hypotheses; specialisation of Sub-lemma A).
* **Two `example` non-vacuity checks** at `⟦explicitEuler⟧`:
  closed-form pins to `1` via leading `v⁶` (the only non-vanishing
  term when `c = b' = bu = m = vc = vvc = Mmc = vmc = vvmc = 0`);
  m=0 reflexive via 10 `rfl`s.

All four named theorems axiom-clean:
`[propext, Classical.choice, Quot.sound]`.

### §13.2 Regression checks

* `inversePolyTree_bushy`, `inversePolyTree_mkVertexVertexCherry`,
  and `inversePolyTree_mkVertexCherryCherry` remain axiom-clean
  after the `trichildCrossTerm` extension. Their `if_neg`/`if_pos`
  cascades hit at the 1st/2nd/3rd branches (respectively), all
  before the new 4th branch — so the cycle 493 extension is
  invisible to them.
* `Section422.lean` compiles cleanly with only the cycle 365
  grandfathered sorry warning at line 2279.
* Sorry count: 5 (unchanged).

### §13.3 Streak advance

§422 axiom-clean streak: 66 substantive + 4 doc (cycles 336–492)
→ **67 substantive + 4 doc** (cycles 336–493).

### §13.4 Cycle 494+ outlook

One remaining non-symmetric `k = 3` candidate per §6.2 + §3.3:
* `mk [vertex, vertex, broom₃]` (order 6).

Paper-derivation guidance: third-child factor for `broom₃` is
`dws M.inverse i broom₃ = (inv_v + Aᵢ)²` (depth-2 binary, but
both children are vertices so only `Aᵢ` appears, not `Bᵢ`). So
the per-row factor for `mk [v, v, broom₃]` is
`(inv_v + Aᵢ)² · (inv_b' + Σⱼ Aᵢⱼ · (inv_v + Aⱼ)²)`. Expanding
the inner `(inv_v + Aⱼ)² = inv_v² + 2·inv_v·Aⱼ + Aⱼ²` produces
new `Σⱼ Aᵢⱼ · Aⱼ²` and `Σⱼ Aᵢⱼ · Aⱼ` terms; multiplied through
gives a 9-kernel decomposition (estimated):
* Existing: `v, c, b', bu, vc, vvc` (6 from cycle 403).
* New: `Mb' = Φ_η(mk [broom₃])` (cycle 371's kernel), `vMb' =
  Φ_η(mk [vertex, broom₃])` (new), and the self-kernel
  `Φ_η(mk [vertex, vertex, broom₃])`.

That's the same approx LOC budget as cycle 493 (~700 LOC). After
this final `k = 3` ladder ship, Phase α'.5.1 P5 closes and
options open to Phase α'.5.2 (k ≥ 4 children, with `tetrachild*`
infrastructure per §5).

Alternative downstream targets:
* **Phase β**: Sub-lemma A body closure at line 2279
  (grandfathered cycle 365 sorry). Multi-cycle work; needs the
  induction machinery for subtree-agreement → kernel-equality
  lifted from the m=0 corollaries.
* **Phase α'.5.2**: Extend `inversePolyTree` to k=4 children via
  `tetrachildPolynomial`/`tetrachildCrossTerm`. Restructures
  the recursion; estimated ~3–5 cycles for the infrastructure +
  one calibration witness.

## §14 — Cycle 494 update (Phase α'.5.1 P5 ship, ladder closure)

### §14.1 Deliverables shipped

* **Quotient-level closed form** `elementaryWeightQ_phi_inv_mkVertexVertexBroom₃`
  for `Φ_{η_q⁻¹}(mk [vertex, vertex, broom₃])`. Closed form:
  `v⁶ - 5v⁴c + 4v³b' + 4v²c² - 4vcb' + b'² - v²·bushy + 2v³·mc
   - 4v²·mvc + 2v·mvvc - v²·mb + 2v·mvb - mvvb` (13 monomials
  across 10 named sum-kernels — v, c, b', bu, mc, mvc, mvvc, mb,
  mvb, mvvb).
* **`trichildCrossTerm` extension** — fifth `else if` branch
  `(vertex, vertex, broom₃)`, value back-computed from the closed
  form minus Blocks (1)+(2)+(3)+(4)+(8):
  `-v⁴c + 3v³b' - 2vcb' + b'² - v²·bushy + 2v³·mc - 4v²·mvc
   + 2v·mvvc + 2v·mvb`.
* **Recursive calibration witness** `inversePolyTree_mkVertexVertexBroom₃`
  matching the closed form verbatim.
* **m=0 corollary** `powRep_sum_eq_of_agreement_at_mkVertexVertexBroom₃_zero`
  (10 agreement hypotheses).
* **Two non-vacuity `example`s** at `⟦explicitEuler⟧`.

### §14.2 Kernel enumeration (cycle 494 paper derivation)

Per cycle 493's `feedback_dws_cherry_factor_includes_v_aᵢ.md` discipline,
worker enumerated kernels via symbolic expansion BEFORE drafting Lean.

For `t = mk [vertex, vertex, broom₃]`, the per-row factor is:
```
dws_i = (inv_v + Aᵢ)² · (inv_b' + ∑ⱼ Aᵢⱼ · (inv_v + Aⱼ)²)
```
where `Aᵢ = ∑ⱼ M.A i j`, `Aⱼ = ∑ₖ M.A j k`, `inv_v = -v`,
`inv_b' = -v³ + 2vc - b'`.

Expanding `(-v + Aⱼ)² = v² - 2v·Aⱼ + Aⱼ²` and distributing:
```
∑ⱼ Aᵢⱼ · (-v + Aⱼ)² = v²·Aᵢ - 2v·∑ⱼ Aᵢⱼ·Aⱼ + ∑ⱼ Aᵢⱼ·Aⱼ²
```

Per-row decomposition has 10 distinct (Aᵢ^p, β_j-aggregate)
monomials, mapping after `Σᵢ bᵢ · ...` to 10 named kernels:
* `1, Aᵢ, Aᵢ², Aᵢ³` → `v, c, b', bu` (cycle 367/368/370 standard kernels)
* `∑ⱼ Aᵢⱼ·Aⱼ` → `mc = Φ_η(mk [cherry])`
* `Aᵢ · ∑ⱼ Aᵢⱼ·Aⱼ` → `mvc = Φ_η(mk [v, cherry])` (cycle 372 kernel)
* `Aᵢ² · ∑ⱼ Aᵢⱼ·Aⱼ` → `mvvc = Φ_η(mk [v, v, cherry])` (cycle 403 kernel)
* `∑ⱼ Aᵢⱼ·Aⱼ²` → `mb = Φ_η(mk [broom₃])` (cycle 371 kernel)
* `Aᵢ · ∑ⱼ Aᵢⱼ·Aⱼ²` → `mvb = Φ_η(mk [v, broom₃])` (cycle 386 kernel)
* `Aᵢ² · ∑ⱼ Aᵢⱼ·Aⱼ²` → `mvvb = Φ_η(mk [v, v, broom₃])` (self-kernel, NEW)

Strategy estimate was 8–10 kernels; actual is 10 (matched
upper bound). Sanity check at `⟦explicitEuler⟧` (v=1, all
others=0) gives `1⁶ = 1` ✓.

### §14.3 Regression checks

* `inversePolyTree_bushy`, `inversePolyTree_mkVertexVertexCherry`,
  `inversePolyTree_mkVertexCherryCherry`, and
  `inversePolyTree_mkVertexVertexMkCherry` remain axiom-clean after
  the `trichildCrossTerm` extension. Their `if_neg`/`if_pos` cascades
  hit at the 1st/2nd/3rd/4th branches respectively, all before the
  new 5th branch — so the cycle 494 extension is invisible to them.
* `Section422.lean` compiles cleanly with only the cycle 365
  grandfathered sorry warning at line 2279.
* Sorry count: 5 (unchanged).

### §14.4 Streak advance and Phase α'.5.1 ladder closure

§422 axiom-clean streak: 67 substantive + 4 doc (cycles 336–493)
→ **68 substantive + 4 doc** (cycles 336–494).

Phase α'.5.1 closes the `k = 3` order-6 candidate list per §6.2.
Five witnesses shipped over cycles 400 / 403 / 491 / 492 / 493 / 494:
* `bushy = mk [v, v, v]` (cycle 400, symmetric)
* `mk [v, v, cherry]` (cycle 403 / 491 cal witness)
* `mk [v, cherry, cherry]` (cycle 492)
* `mk [v, v, mk [cherry]]` (cycle 493)
* `mk [v, v, broom₃]` (cycle 494, this ship)

### §14.5 Cycle 495+ outlook

Three principal paths for cycle 495's planner:

1. **Phase β/γ scoping doc** — markdown-only scoping doc for the
   cycle 365 sorry at line 2279
   (`powRep_sum_eq_of_strict_subtree_agreement` general body).
   The unified `inversePolyTree` recursion + uniform kernel
   characterisation across cycles 491/492/493/494 + the 14 Family C
   calibration witnesses give the empirical surface needed to
   design the structural induction.

2. **Phase α'.5.2 scoping doc** — `k = 4` heterogeneous-children
   witnesses (e.g. `mk [v, v, v, c]`). Requires
   `tetrachildPolynomial` + `tetrachildCrossTerm` infrastructure
   analogous to cycle 387's `bichildPolynomial` and cycle 399's
   `trichildPolynomial`. Multi-cycle infrastructure.

3. **Pivot to fresh entity** — natural inflection point after the
   `k = 3` ladder closes. Cycle 495's planner reads
   `cycle_336_pivot_options.md` and picks `def:451A`, `def:442A`,
   `thm:535A`, or `thm:541A`.

The pivot decision belongs to cycle 495's planner.
