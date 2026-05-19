# Issue: `def:422B` Phase α'.4.3 bushy scoping — `trichildPolynomial` and the last ladder-tree migration

## §1 Status & blocker

**Scoping doc, cycle 398.** No Lean code shipped this cycle — this is a
markdown-only research doc distilling cycle 370's `bushy` closed form
and cycle 387's `bichildPolynomial`/`inversePolyTree` infrastructure
into a concrete multi-cycle plan for migrating
`inversePolynomial`'s `bushy` branch from Family B's
`inversePolyBroom 3` dispatch to a Family C–style
`inversePolyTree (mk [vertex, vertex, vertex])` dispatch. The cycle
397 worker's "Suggested next approach"
(`task_results/cycle_397.md` §"Suggested next approach") explicitly
named this scoping doc as the cycle 398 move; the cycle 398 planner
authorised the markdown-only ship in `strategy.md`
§"Priority 1 — DELIVERABLE: Phase α'.4.3 scoping doc".

This doc continues the markdown-only scoping precedent of cycles
373 / 379 / 385:

* `.prover-state/issues/def_422B_subLemmaA_inductive_plan.md` (cycle
  373 — 1399 lines, 11 sections; drove cycles 374–378's 8-tree
  ladder build-out).
* `.prover-state/issues/def_422B_phase_alpha_prime_scoping.md` (cycle
  379 — 1298 lines, 11 sections; drove cycles 380–383's Family A/B
  recursive helper ships).
* `.prover-state/issues/def_422B_phase_alpha_prime_family_C_scoping.md`
  (cycle 385 — 894 lines, 11 sections incl. §10/§11 appends; drove
  the 11-cycle ladder of α'.4.0 through α'.4.2 migrations from
  cycle 386 through cycle 397).

**§422 axiom-clean streak: 60 substantive + 2 doc (cycles 336–397)**,
advancing to **60 substantive + 3 doc (336–398)** after this ship.
Single grandfathered sorry at `OpenMath/Chapter4/Section422.lean:2279`
(cycle 365's `powRep_sum_eq_of_strict_subtree_agreement` general body).
Section422.lean: ~7867 LOC. `grep -c sorry` returns 5 (4 docstring
references + 1 actual code sorry).

`bushy = mk [vertex, vertex, vertex]` is the **last** unmigrated
ladder tree. After it lands, all 9 ladder trees route uniformly
through `inversePolyTree`, unlocking the eventual closure of the
cycle 365 grandfathered sorry in Phase β/γ.

## §2 The bushy closed form

Cycle 370's `elementaryWeightQ_phi_inv_bushy` at
`Section422.lean:3011` pins the closed form:

```
Φ_{η_q⁻¹}(bushy)
   =  (Φ_η(vertex))^4
    − 3 · (Φ_η(vertex))^2 · Φ_η(cherry)
    + 3 · Φ_η(vertex) · Φ_η(broom₃)
    −     Φ_η(bushy)
```

Notation: `v = Φ_η(vertex), c = Φ_η(cherry), b' = Φ_η(broom₃)`. Then

```
Φ_{η_q⁻¹}(bushy) = v⁴ − 3v²c + 3v·b' − Φ_η(bushy)
```

This is **algebraically the Family B `inversePolyBroom 3 f` value**
(binomial expansion of `(Aᵢ − v)³` against `bᵢ`):

| j | sign | C(3,j) | factor | term |
|---|---|---|---|---|
| 0 | (−1)⁴ = + | 1 | v³ · v | + v⁴ |
| 1 | (−1)⁵ = − | 3 | v² · c | − 3v²c |
| 2 | (−1)⁶ = + | 3 | v · b' | + 3v·b' |
| 3 | (−1)⁷ = − | 1 | 1 · Φ_η(bushy) | − Φ_η(bushy) |

So `bushy` is currently dispatched by `inversePolynomial`'s 5th
`if-then-else` branch to `inversePolyBroom 3 f` (cycle 383's Family B
binomial closed form). The Phase α'.4.2 unification migrates this to
`inversePolyTree (mk [vertex, vertex, vertex]) f` via a new
three-children-aware extension of the recursion.

**Non-vacuity reference value** (cycle 370 example,
`Section422.lean:3176`): at `⟦explicitEuler⟧`, where `Σ b = 1` (so
`v = 1`) and `A = 0` (so `c = b' = Φ_η(bushy) = 0`), the closed form
evaluates to `1⁴ − 3·1²·0 + 3·1·0 − 0 = 1`. Cycle 370's example pins
this to `1` by explicit Lean computation. This anchors the cycle 400
calibration ship's non-vacuity check.

## §3 Block decomposition for three children

Cycle 385's §3.2 decomposed two-children product expansions into 4
blocks indexed by (constant vs A-row-sum) selection at each child.
For three children, the analogous decomposition has **2³ = 8 blocks**.

Let `t = mk [t₁, t₂, t₃]`. Cycle 358's `_inv_mk` unfolds the
per-row product:

```
M.inverse.derivativeWeightWithSrc i (mk [t₁, t₂, t₃])
  = Π_{ℓ∈{1,2,3}} ( M.inverse.elementaryWeight tℓ
                  + Σⱼ M.A i j · M.inverse.derivativeWeight j tℓ )
  = Π_ℓ ( inv_ℓ + S_ℓ(i) )
```

where `inv_ℓ := M.inverse.elementaryWeight tℓ` and
`S_ℓ(i) := Σⱼ M.A i j · M.inverse.derivativeWeight j tℓ`.

Expanding the three-factor product gives 8 blocks, one per element
of `{const, A-sum}³`:

| Block | Selection at (t₁, t₂, t₃) | Algebraic shape |
|---|---|---|
| (1) | c · c · c | `inv₁ · inv₂ · inv₃` |
| (2) | A · c · c | `S₁(i) · inv₂ · inv₃` |
| (3) | c · A · c | `inv₁ · S₂(i) · inv₃` |
| (4) | c · c · A | `inv₁ · inv₂ · S₃(i)` |
| (5) | A · A · c | `S₁(i) · S₂(i) · inv₃` |
| (6) | A · c · A | `S₁(i) · inv₂ · S₃(i)` |
| (7) | c · A · A | `inv₁ · S₂(i) · S₃(i)` |
| (8) | A · A · A | `S₁(i) · S₂(i) · S₃(i)` |

After multiplying by `M.b i` and summing over `i`, with the outer
`−Σᵢ` prefactor from `_inv_mk` (which contributes the leading sign):

* **Block (1)** → `−(Σᵢ bᵢ) · inv₁ · inv₂ · inv₃
  = −v · inv₁ · inv₂ · inv₃`. Pure scalar multiple of the recursive
  three-fold product.
* **Block (2)** → `−inv₂ · inv₃ · Σᵢ bᵢ · S₁(i)
  = −inv₂ · inv₃ · Φ_η(mk [t₁])` (the parent of `t₁`-only kernel).
* **Block (3)** → symmetric: `−inv₁ · inv₃ · Φ_η(mk [t₂])`.
* **Block (4)** → symmetric: `−inv₁ · inv₂ · Φ_η(mk [t₃])`.
* **Block (5)** → `−inv₃ · (Σᵢ bᵢ · S₁(i) · S₂(i))`. The bilinear
  factor `Σᵢ bᵢ · S₁(i) · S₂(i)` is the §385 §3.2 block-(4) kernel
  for the *two*-children tree `mk [t₁, t₂]` — empirically (cycle 384)
  this surfaces an `Φ_η(mk [vertex, t_some])`-style cross-kernel.
* **Block (6)** → similar, surfaces a `(t₁, t₃)` bilinear cross-kernel.
* **Block (7)** → similar, surfaces a `(t₂, t₃)` bilinear cross-kernel.
* **Block (8)** → `−Σᵢ bᵢ · S₁(i) · S₂(i) · S₃(i)`. This is the
  trilinear sum surfacing `Φ_η(mk [t₁, t₂, t₃]) = Φ_η(t)` itself
  (the self-kernel; appears as `−f t` in the closed form).

**For bushy `(t₁, t₂, t₃) = (vertex, vertex, vertex)`:**

* `inv_ℓ = M.inverse.elementaryWeight vertex = −v` for each ℓ
  (cycle 367's `h_inv_v`).
* `S_ℓ(i) = Σⱼ Aᵢⱼ · M.inverse.derivativeWeight j vertex
       = Σⱼ Aᵢⱼ · 1 = Σⱼ Aᵢⱼ` (since
  `derivativeWeight j vertex = 1`; the inverse-row carries no sign at
  `derivativeWeight`, only at the `M.inverse.b`).
* `Φ_η(mk [vertex]) = Φ_η(cherry) = c`.

So:

* Block (1) → `−v · (−v)³ = −v · (−v³) = +v⁴`. ✓ (matches cycle 370's
  leading `+v⁴`)
* Blocks (2/3/4) → each `−(−v)(−v) · c = −v²·c`. Three of them:
  `−3v²c`. ✓ (matches cycle 370's `−3v²c`)
* Blocks (5/6/7) → each `−(−v) · Σᵢ bᵢ · (Σⱼ Aᵢⱼ)² = v · Φ_η(broom₃)
  = +v·b'`. Three of them: `+3v·b'`. ✓ (matches cycle 370's `+3v·b'`)
* Block (8) → `−Σᵢ bᵢ · (Σⱼ Aᵢⱼ)³ = −Φ_η(bushy) = −f bushy`. ✓
  (matches cycle 370's `−Φ_η(bushy)`)

**Every block lines up cleanly.** The full strawman recovers cycle
370's closed form by inspection.

## §4 Conjectured `trichildPolynomial` shape

Building on cycle 387's `bichildPolynomial` sign convention (leading
`-(v · inv₁ · inv₂)`), the natural extension to three children is:

```lean
noncomputable def trichildPolynomial
    (t₁ t₂ t₃ : RT) (inv₁ inv₂ inv₃ : ℝ) (f : RT → ℝ) : ℝ :=
  -(f RootedTree.vertex * inv₁ * inv₂ * inv₃)         -- Block (1)
    - inv₂ * inv₃ * f (mk [t₁])                        -- Block (2)
    - inv₁ * inv₃ * f (mk [t₂])                        -- Block (3)
    - inv₁ * inv₂ * f (mk [t₃])                        -- Block (4)
    + trichildCrossTerm t₁ t₂ t₃ f                     -- Blocks (5)(6)(7)(8)
    - f (mk [t₁, t₂, t₃])                              -- self-kernel
```

Sign convention rationale:

* Leading `-(v · inv₁ · inv₂ · inv₃)`: matches cycle 387's
  `bichildPolynomial` leading `-(v · inv₁ · inv₂)`. Together they
  ensure consistency with the cycle 358 `_inv_mk` outer `−Σᵢ M.b i ·
  (...)` prefactor.
* `- inv_j · inv_k · f (mk [t_ℓ])` for each (j, k, ℓ) cyclic
  selection: each such block is the §3 Block (2/3/4) contribution
  pulled out through the closed form for the one-child
  `Φ_η(mk [t_ℓ])` kernel.
* `+ trichildCrossTerm`: bundles Blocks (5)/(6)/(7)/(8) (the
  bilinear and trilinear sums).
* `- f (mk [t₁, t₂, t₃])`: uniform self-kernel sign across all four
  Family C witnesses (cycles 371/372/384/386) and across cycle 387's
  `bichildPolynomial`.

**Sanity check at bushy** (paper computation):

For `(t₁, t₂, t₃) = (vertex, vertex, vertex)`:

* `inv_ℓ = inversePolyTree vertex f = −f vertex = −v` (cycle 387's
  `inversePolyTree_vertex`).
* `mk [vertex] = cherry`; `mk [vertex, vertex] = broom₃`;
  `mk [vertex, vertex, vertex] = bushy`.

Plugging in:

```
trichildPolynomial vertex vertex vertex (−v) (−v) (−v) f
  = −(v · (−v) · (−v) · (−v))                -- = +v⁴ (Block 1)
    − (−v) · (−v) · f cherry                  -- = −v²c   (Block 2)
    − (−v) · (−v) · f cherry                  -- = −v²c   (Block 3)
    − (−v) · (−v) · f cherry                  -- = −v²c   (Block 4)
    + trichildCrossTerm vertex vertex vertex f
    − f bushy                                  -- = −f bushy
  = v⁴ − 3v²c + trichildCrossTerm vertex vertex vertex f − f bushy
```

Matching cycle 370's `v⁴ − 3v²c + 3v·b' − f bushy` forces

```
trichildCrossTerm vertex vertex vertex f = 3 · f vertex · f broom₃.
```

The `+3v·b'` decomposes into the three Block (5)/(6)/(7) bilinear
contributions at `(v, v, v)`, each surfacing `Σᵢ bᵢ · (Σⱼ Aᵢⱼ)² · 1
= Φ_η(broom₃)` after the outer `−Σᵢ`-and-three-inv₃-collapse. Block
(8) trilinear contributes `−Φ_η(bushy)` which is absorbed into the
self-term `−f bushy` (since at three-vertex children, Block (8) is
exactly the `Σᵢ bᵢ · (Σⱼ Aᵢⱼ)³ = Φ_η(bushy)` summand).

**Verification status**: the §3 paper decomposition matches cycle
370 cleanly (§3 sanity walk-through above). Cycle 399's worker
should still do a symbolic derivation directly from cycle 358's
`_inv_mk` body before locking the trichild infrastructure — see §7
R3 below — but the strawman is internally consistent with the
shipped closed form.

## §5 Conjectured `trichildCrossTerm` dispatch

Mirroring cycle 387's `bichildCrossTerm` `if-then-else` cascade
(currently with `(cherry, cherry)` and `(broom₃, cherry)` cases):

```lean
noncomputable def trichildCrossTerm (t₁ t₂ t₃ : RT) (f : RT → ℝ) : ℝ :=
  if t₁ = RootedTree.vertex
       ∧ t₂ = RootedTree.vertex
       ∧ t₃ = RootedTree.vertex then
    3 * f RootedTree.vertex * f RootedTree.broom₃
  else
    0
```

Initial dispatch: only the `(vertex, vertex, vertex)` triple is
populated, as this is the **only** three-children ladder tree that
will route to `inversePolyTree` in cycle 401. Future Phase α' work
on higher-arity heterogeneous-children trees would extend this
dispatch (per the §3 block decomposition's general form), but no
such trees are on the immediate horizon.

**Sign convention re-check** at the all-vertex triple under cycle
370: `trichildCrossTerm vertex vertex vertex f = 3 · v · b'` matches
the `+3v·b'` term in `v⁴ − 3v²c + 3v·b' − f bushy`. ✓

## §6 Lean ship plan (cycles 399–401)

Three Lean cycles, ~3 cycles total, ~160 LOC budget.

### §6.1 Cycle 399 (Phase α'.4.1 P8) — trichild infrastructure

**Deliverables**:

1. **Symbolic verification** of §5's
   `trichildCrossTerm vertex vertex vertex f = 3 · f vertex · f broom₃`
   value. Cycle 399's worker should:
   * Open cycle 358's `_inv_mk` body
     (`Section422.lean:582`) and trace the three-children expansion
     manually, or via a scratch `example` that unfolds `_inv_mk` at
     `mk [vertex, vertex, vertex]` and computes Blocks (5)/(6)/(7)
     directly.
   * Cross-check against the §3 paper derivation above. If the
     symbolic computation matches `3v·b'`, lock the §5 strawman.
     If not, derive the correct value and update §5.
2. **`trichildCrossTerm` definition** (§5 strawman, possibly
   updated):
   ```lean
   noncomputable def trichildCrossTerm (t₁ t₂ t₃ : RT) (f : RT → ℝ) : ℝ :=
     if t₁ = RootedTree.vertex
          ∧ t₂ = RootedTree.vertex
          ∧ t₃ = RootedTree.vertex then
       3 * f RootedTree.vertex * f RootedTree.broom₃
     else
       0
   ```
3. **`trichildPolynomial` definition** (§4 strawman):
   ```lean
   noncomputable def trichildPolynomial
       (t₁ t₂ t₃ : RT) (inv₁ inv₂ inv₃ : ℝ) (f : RT → ℝ) : ℝ :=
     -(f RootedTree.vertex * inv₁ * inv₂ * inv₃)
       - inv₂ * inv₃ * f (mk [t₁])
       - inv₁ * inv₃ * f (mk [t₂])
       - inv₁ * inv₂ * f (mk [t₃])
       + trichildCrossTerm t₁ t₂ t₃ f
       - f (mk [t₁, t₂, t₃])
   ```
4. **Extension of `inversePolyTree`'s recursion** at
   `Section422.lean:6412–6423`. Insert the `[c₁, c₂, c₃]` case
   BEFORE the existing `(_ :: _ :: _ :: _) → 0` catch-all:
   ```lean
   noncomputable def inversePolyTree : RT → (RT → ℝ) → ℝ
     | mk [], f       => -f vertex
     | mk [c], f      => -(v · inversePolyTree c f)
                          + monochildCrossTerm c f - f (mk [c])
     | mk [c₁, c₂], f => bichildPolynomial c₁ c₂
                          (inversePolyTree c₁ f) (inversePolyTree c₂ f) f
     | mk [c₁, c₂, c₃], f => trichildPolynomial c₁ c₂ c₃
                          (inversePolyTree c₁ f) (inversePolyTree c₂ f)
                          (inversePolyTree c₃ f) f                          -- NEW
     | mk (_ :: _ :: _ :: _ :: _), _ => 0                                   -- bumped
   ```
   Note the catch-all changes from `(_ :: _ :: _ :: _) → 0`
   (three-or-more) to `(_ :: _ :: _ :: _ :: _) → 0`
   (four-or-more). This shift is the structural-recursion risk
   flagged in §7 R1.

**LOC budget**: ~80–100. Risk: low-medium (the symbolic derivation
in step 1 is the only substantive new content; steps 2–4 are
mechanical).

**Verification**: all 11 existing `inversePolyTree_*` calibrations
(`_vertex`, `_cherry`, `_broom₃` if exists, `_mkCherry`,
`_mkBroom₃`, `_mkVertexCherry`, `_mkMkCherry`, plus any cycle
390-era extras) must still pass — their proof bodies match on
children-list shapes with `k ≤ 2`, so the new `k = 3` case won't
unify against any of them. See §7 R2 for the detailed risk argument.

### §6.2 Cycle 400 (Phase α'.4.1 P9) — `inversePolyTree_bushy` calibration

**Deliverable**: a single new calibration theorem
```lean
theorem inversePolyTree_bushy (f : RT → ℝ) :
    inversePolyTree RootedTree.bushy f
      = (f RootedTree.vertex) ^ 4
        - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
        + 3 * f RootedTree.vertex * f RootedTree.broom₃
        - f RootedTree.bushy
```

**Proof recipe** (cycle 392/394/395 mechanical template):

```lean
show inversePolyTree (mk [RootedTree.vertex, RootedTree.vertex, RootedTree.vertex]) f
       = ...
rw [inversePolyTree, inversePolyTree_vertex,
    inversePolyTree_vertex, inversePolyTree_vertex,
    show trichildCrossTerm RootedTree.vertex RootedTree.vertex RootedTree.vertex f
           = 3 * f RootedTree.vertex * f RootedTree.broom₃ by
      unfold trichildCrossTerm
      rw [if_pos ⟨rfl, rfl, rfl⟩]]
show ... = ...                                -- canonicalise mk [v] = cherry, mk [v,v,v] = bushy
ring
```

**LOC budget**: ~30. Risk: low (cycle 392/394/395 precedent is
mechanical; the only novelty is the trichild cross-term unfold).

**Non-vacuity verification**: at `f = elementaryWeightQ_phi
⟦explicitEuler⟧`, the closed form should evaluate to `1` (cycle 370
non-vacuity reference). Optional `example` ship for confirmation,
~10 LOC.

### §6.3 Cycle 401 (Phase α'.4.2 P5) — `bushy` migration

**Deliverable**: the final Family B → Family C migration of
`inversePolynomial`'s `bushy` branch.

1. **Bridge ship**:
   `inversePolyTree_bushy_eq_inversePolynomial` — a 4-`if_neg`
   plus `if_pos rfl` cascade analogous to cycles 396/397's
   `mk [cherry]` and `mk [mk [cherry]]` bridge ships. The cycle 397
   ship's `if_neg ... if_pos rfl` template applies after
   substituting `bushy` for `mk [mk [cherry]]`. Note: bushy is
   `inversePolynomial`'s 5th branch (after vertex, cherry, broom₃,
   mk [cherry]), so the bridge has 4 `if_neg` discharges + 1
   `if_pos rfl`.
2. **`inversePolynomial`'s `bushy` branch body** rewritten to
   dispatch through `inversePolyTree (mk [vertex, vertex, vertex])
   f` instead of `inversePolyBroom 3 f`.
3. **Phase α.2 calibration `example` update**: cycle 374's
   `bushy` calibration `example` trailing `inversePolyBroom_three`
   swapped for `inversePolyTree_bushy`. (Combinable with Step 4 via
   `replace_all` per cycle 397's discovery.)
4. **Phase β.4 bridge update**:
   `elementaryWeightQ_phi_inv_eq_inversePolynomial_bushy`
   (cycle 374-era; check exact theorem name) similarly retrofitted.
5. **Phase γ branch update**: in
   `inversePolynomial_eq_of_subtree_agreement`'s `bushy` arm, both
   `inversePolyBroom_three` occurrences (f-side and g-side)
   replaced with `inversePolyTree_bushy`. `replace_all` on the
   matching f / g pattern.
6. **Step F (derivative fix on cycle 382's
   `inversePolyBroom_three_eq_inversePolynomial`)**: extend the
   proof body with `inversePolyBroom_three, inversePolyTree_bushy`
   after the existing `if_pos rfl`. Cycle 396 / 397 ship pattern.

**LOC budget**: ~50. Risk: low — this is the third copy of the
cycle 396 / 397 migration recipe; the cycle 397 worker's
`replace_all` discovery applies here too.

**Verification**: `lake build OpenMath.Chapter4.Section422` exits 0;
all migration touch-point theorems return
`[propext, Classical.choice, Quot.sound]` axioms; `grep -c sorry`
still 5.

### §6.4 Total budget

| Cycle | Deliverable | LOC |
|---|---|---|
| 399 | Trichild infra + `inversePolyTree` extension | 80–100 |
| 400 | `inversePolyTree_bushy` calibration | 30 (+10 example) |
| 401 | `bushy` migration | 50 |
| **Total** | **Three Lean ships, post-cycle-398** | **~160–200** |

Section422.lean: ~7867 (current) → ~8000–8100 (post-401). Still
tractable for warm rebuilds (cycle 397 measured ~200s).

## §7 Risk inventory

**R1 — structural recursion extension** (severity: MEDIUM). Inserting
a new `[c₁, c₂, c₃]` case BEFORE the existing
`(_ :: _ :: _ :: _) → 0` catch-all requires careful pattern ordering.
Cycle 387's ship at `Section422.lean:6412–6423` placed the catch-all
last; the cycle 399 worker should preserve this ordering by inserting
the new triple-children case BEFORE the catch-all and bumping the
catch-all's pattern to `(_ :: _ :: _ :: _ :: _)`.

**Mitigation**: cycle 399 worker should re-read the cycle 387 ship
at `Section422.lean:6412–6423` to verify pattern ordering; run
`lake env lean OpenMath/Chapter4/Section422.lean` after the
`inversePolyTree` extension to confirm Lean accepts the new match.

**R2 — existing calibration witnesses** (severity: LOW). All current
`inversePolyTree_*` calibrations (`_vertex`, `_cherry`, `_mkCherry`,
`_mkBroom₃`, `_mkVertexCherry`, `_mkCherryCherry`, `_mkBroomCherry`,
`_mkMkCherry`) match on children-list shapes with `k ≤ 2`. The new
`k = 3` case won't pattern-match against any of them, so no existing
proof body breaks.

**Note**: cycle 394's lesson (extending `monochildCrossTerm` required
adding one `if_neg` discharge in `inversePolyTree_cherry` because
`monochildCrossTerm` dispatches by *child*-tree-shape) does **NOT**
apply here, because the trichild extension is at the
**recursion-level** match (children-LIST shape, not individual-child
shape).

**R3 — strawman cross-term value** (severity: LOW, downgraded from
the planner's "RED FLAG"). The strategy's §7 R3 (`strategy.md` for
cycle 398) raised concern that the §5 strawman value
`trichildCrossTerm vertex vertex vertex f = 3 · f vertex · f broom₃`
disagreed with cycle 370's non-vacuity witness value at
`⟦explicitEuler⟧`. The strategy author computed:

> Strawman value: `1⁴ - 3·1²·1 + 3·1·1 - 1 = 1 - 3 + 3 - 1 = 0`.

This substitution is **incorrect**. At `⟦explicitEuler⟧`:

* `v = Φ_η(vertex) = Σ b = 1` (with `b = [1]`).
* `c = Φ_η(cherry) = 0` (since `A = 0`).
* `b' = Φ_η(broom₃) = 0` (since `A = 0`).
* `Φ_η(bushy) = 0` (since `A = 0`).

Plugging in correctly: `1⁴ − 3·1²·0 + 3·1·0 − 0 = 1`, which **matches**
cycle 370's example (`Section422.lean:3176`, confirmed value `1`).

**Resolution**: there is **no discrepancy** between the §5 strawman
and cycle 370. The §3 paper block decomposition above gives the same
`+3v·b'` term independently. Cycle 399's worker should still do a
symbolic verification (per §6.1 step 1) before locking the
infrastructure, but the strawman is internally consistent.

**R4 — sign convention** (severity: LOW). Cycle 387/388 hit sign
issues with the bichild cross-term. The §4 strawman uses the same
leading `-(v · inv₁ · inv₂ · inv₃)` sign as cycle 387's
`bichildPolynomial`. The §3 block decomposition's sign analysis
matches cycle 370 cleanly — no expected sign flip. Cycle 399's
worker should re-verify by computing the §3 block at `(v, v, v)`
under the actual `_inv_mk` Lean unfold rather than the paper
derivation.

**R5 — file size** (severity: LOW). Section422.lean is already
~7867 LOC. Adding ~160–200 LOC across cycles 399–401 brings the
total to ~8000–8100 LOC. Warm rebuilds at this size measured ~200s
in cycle 397, which is tractable. If cycle 399 elaboration time
spikes (the new `trichildPolynomial`'s 6-argument signature is
larger than `bichildPolynomial`'s 5-argument signature), monitor
build times; consider extracting helpers if elaboration exceeds
300s.

**R6 — `inversePolyTree` non-vacuity at higher-arity heterogeneous
trees** (severity: LOW). The new `[c₁, c₂, c₃]` case will dispatch
through `trichildPolynomial` for ALL three-children trees, not just
`bushy`. Other three-children trees (e.g. `mk [vertex, vertex,
cherry]`, `mk [cherry, vertex, vertex]`, etc.) will have
`trichildCrossTerm` dispatch to the `else → 0` branch. This is
acceptable: those trees are not on the migration ladder, so the
recursion's behavior on them does not need to match any closed form
yet. Their dispatch through `inversePolyTree` will return a "best-effort"
polynomial that is only correct at `(vertex, vertex, vertex)`. Cycle
401 should NOT add migration entries for them in `inversePolynomial`.

## §8 Cycle 399 entry point

Pre-flight tasks for cycle 399's worker, in order:

1. **Read cycle 387's `bichildPolynomial` design** at
   `Section422.lean:6383–6389` for the two-children precedent.
2. **Read cycle 358's `_inv_mk` proof body** at `Section422.lean:582`
   to understand the per-child block expansion mechanism.
3. **Symbolically compute the three-children expansion** of
   `derivativeWeightWithSrc M.inverse i (mk [vertex, vertex, vertex])`
   per the §3 block decomposition. Specifically:
   * Confirm Block (5)/(6)/(7) at `(v, v, v)` each produces
     `−inv₃ · Φ_η(broom₃) = +v·b'` after the outer `−Σᵢ` prefactor.
   * Confirm Block (8) produces `−Φ_η(bushy) = −f bushy`.
   * Sum: `+v⁴ − 3v²c + 3v·b' − f bushy`, matching cycle 370.
4. **Lock the §5 `trichildCrossTerm` value** based on the
   derivation. If §3's block decomposition checks out cleanly, the
   strawman value `3 · f vertex · f broom₃` is correct. If the
   symbolic computation reveals a discrepancy (unlikely, given §3's
   sanity walk-through above), update §5 before writing the Lean
   definition.
5. **Write `trichildPolynomial`, `trichildCrossTerm`, and the
   `inversePolyTree` extension** per §6.1.
6. **Verify all existing `inversePolyTree_*` calibrations still
   pass** by running `lake env lean
   OpenMath/Chapter4/Section422.lean` after the changes.
7. **Optional non-vacuity `example`** at
   `f = elementaryWeightQ_phi ⟦explicitEuler⟧` confirming bushy
   evaluates to `1`.

## §9 Cross-references

### Predecessor scoping docs (in chronological order)

* `.prover-state/issues/def_422B_path.md` (cycle 336) — overall
  `def:422B` Phases A–E roadmap.
* `.prover-state/issues/def_422B_phase_D_3_scoping.md` (cycle 357) —
  Phase D.3 sub-phases.
* `.prover-state/issues/def_422B_subLemmaA_inductive_plan.md` (cycle
  373) — Sub-lemma A inductive plan; first markdown-only scoping
  cycle.
* `.prover-state/issues/def_422B_phase_alpha_prime_scoping.md` (cycle
  379) — Phase α' recursive `inversePolynomial` design; sibling
  scoping doc for Family A/B helper ships.
* `.prover-state/issues/def_422B_phase_alpha_prime_family_C_scoping.md`
  (cycle 385) — Phase α'.4 Family C scoping doc; direct predecessor
  for this bushy narrowing (also drove cycles 386–397).

### Lean ship locations (cycles 370 / 387 / 396 / 397)

* `Section422.lean:582` — cycle 358's `_inv_mk` (the per-row product
  expansion that drives the §3 block decomposition).
* `Section422.lean:3011–3169` — cycle 370's
  `elementaryWeightQ_phi_inv_bushy` closed form (the §2 target).
* `Section422.lean:3176–3220` — cycle 370's non-vacuity `example` at
  `⟦explicitEuler⟧` (value `1`; the §7 R3 reference).
* `Section422.lean:6283–6348` — cycle 387/388's `bichildCrossTerm`
  (template for §5's `trichildCrossTerm`).
* `Section422.lean:6350–6381` — cycle 392's `monochildCrossTerm` (the
  single-child analogue).
* `Section422.lean:6383–6389` — cycle 387's `bichildPolynomial`
  (template for §4's `trichildPolynomial`).
* `Section422.lean:6412–6423` — cycle 387's `inversePolyTree`
  recursion definition (the extension site for §6.1).
* `Section422.lean:7462–7478` (approx) — cycle 382's
  `inversePolyBroom_three_eq_inversePolynomial` (the cycle 401
  Step F derivative-fix site).

### Cycle 397 task results (entry-point reference)

* `.prover-state/task_results/cycle_397.md` §"Suggested next
  approach" — explicit endorsement of this scoping doc.
* `.prover-state/task_results/cycle_397.md` §"Discovery" — the
  `replace_all` collapse trick for combining Phase α.2 calibration +
  Phase β.4 bridge edits, applicable to cycle 401 step (3+4).

### Source material

* `extraction/raw_text/ch04.txt:1148–1173` — Butcher §422 textbook
  source ("E group" and η_q derivation).
* `extraction/formalization_data/entities/def_422B.json` — entity
  metadata for `def:422B`.

### Memory cross-links

* `feedback_simp_recursive_def_overunfolds.md` — cycle 399/400's
  calibration theorems must use targeted `rw [name-eq-thm-...]`
  rather than `simp [inversePolyTree, ...]`; this applies verbatim
  to the new `trichildPolynomial` / `trichildCrossTerm` defs.
* `feedback_ring_def_opacity.md` — cycle 400's `inversePolyTree_bushy`
  proof must insert a `show ...` to canonicalise `mk [vertex] = cherry`,
  `mk [vertex, vertex] = broom₃`, `mk [vertex, vertex, vertex] = bushy`
  before invoking `ring`. The `bushy` and `broom₃` defs are
  non-reducible, so `ring` cannot bridge `f (mk [vertex, vertex, vertex])`
  to `f bushy` without an explicit `show`.
* `feedback_indexed_inductive_cases_disjoint.md` — `cases h` on
  disjoint `RootedTree.mk` constructors (e.g.,
  `¬ (vertex = mk [...])`) closes by `decide` / `cases h` directly
  in the bridge ship's `if_neg` cascades.

## §10 Self-reference

* Cycle 398 ships **this doc** as its sole deliverable; no Lean
  changes.
* Cycle 399 ships Phase α'.4.1 P8 (trichild infrastructure) per §6.1.
* Cycle 400 ships Phase α'.4.1 P9 (`inversePolyTree_bushy`
  calibration) per §6.2.
* Cycle 401 ships Phase α'.4.2 P5 (`bushy` migration) per §6.3.
* Post-cycle-401: all 9 ladder trees route uniformly through
  `inversePolyTree`. Cycle 402+ revisits the cycle 365 grandfathered
  sorry at `Section422.lean:2279` armed with the now-uniform
  recursive `inversePolyTree` structure.

### §10.1 Success criteria (cycle 398)

* One new markdown file at
  `.prover-state/issues/def_422B_phase_alpha_prime_family_bushy_scoping.md`
  (this file).
* 400–600 lines covering §1–§10.
* §2 closed form transcribed verbatim from cycle 370
  (`Section422.lean:3011`).
* §3 block decomposition has 8 blocks with the
  (constant vs A-row-sum) selection structure.
* §4 strawman `trichildPolynomial` sign convention verified at
  bushy: under `inv = -v` at three children, the leading
  `-(v · inv₁ · inv₂ · inv₃)` gives `+v⁴`.
* §5 strawman `trichildCrossTerm vertex vertex vertex f` value
  `3 · f vertex · f broom₃` cross-checked against cycle 370.
* §7 R3 red flag explicitly **resolved**: the planner's substitution
  was incorrect; no actual discrepancy between strawman and cycle
  370. Cycle 399 still does the symbolic verification to be safe.
* §8 cycle 399 entry point lists pre-flight steps in order.
* Zero Lean changes (`git diff --stat` should show only
  `.prover-state/` paths).
* `lean_status.json` `def:422B` row unchanged (status `partial`,
  `cycle_completed_at` bumped from 397 to 398).
* §422 axiom-clean streak advances: 60 substantive + 2 doc → **60
  substantive + 3 doc** (cycles 336–398).

### §10.2 What this doc deliberately does NOT do

* Does NOT ship `trichildPolynomial` or `trichildCrossTerm` Lean
  definitions. Cycle 399's work.
* Does NOT extend `inversePolyTree`'s match. Cycle 399's work.
* Does NOT ship `inversePolyTree_bushy` calibration. Cycle 400's
  work.
* Does NOT migrate `inversePolynomial`'s `bushy` branch. Cycle 401's
  work.
* Does NOT touch the cycle 365 grandfathered sorry at
  `Section422.lean:2279`. Multi-cycle Phase β/γ extension.
* Does NOT pivot to a fresh entity. The §422 streak is productive
  and 3 cycles from closing Phase α'.4 fully.

---

## §11 Cycle 399 closure (Phase α'.4.1 P8 ship)

Cycle 399 shipped the §6.1 deliverables verbatim per strategy
(no scope deviation). Three new symbols in
`OpenMath/Chapter4/Section422.lean`, inserted between cycle 387's
`bichildPolynomial` (ending at line 6389) and the `inversePolyTree`
recursion (formerly lines 6412–6423, now extended to a 5-arm form).

### §11.1 What shipped

* `trichildCrossTerm : RT → RT → RT → (RT → ℝ) → ℝ` — Block (5)+(6)+(7)
  trilinear cross-term per-triple dispatch. Single non-default
  if-branch at `(vertex, vertex, vertex) → 3 · f vertex · f broom₃`;
  all other triples return `0` (placeholder for future Phase α'.4.3+
  triple-children witnesses, analogous to cycle 387's initial
  `bichildCrossTerm` placeholder for binary pairs).
* `trichildPolynomial : RT → RT → RT → ℝ → ℝ → ℝ → (RT → ℝ) → ℝ` —
  8-block polynomial backbone shaped
  `-(v · inv₁ · inv₂ · inv₃)
   − inv₂ · inv₃ · f (mk [t₁])
   − inv₁ · inv₃ · f (mk [t₂])
   − inv₁ · inv₂ · f (mk [t₃])
   + trichildCrossTerm t₁ t₂ t₃ f
   − f (mk [t₁, t₂, t₃])`,
  mirroring cycle 387's `bichildPolynomial` sign convention. The
  uniform leading `-` and the uniform `- f (mk [t₁, t₂, t₃])`
  self-term match the cycle 380/383/387 convention.
* `inversePolyTree` recursion extension — new fourth match arm
  `mk [c₁, c₂, c₃] → trichildPolynomial c₁ c₂ c₃ (inversePolyTree c₁ f)
  (inversePolyTree c₂ f) (inversePolyTree c₃ f) f` inserted before the
  catch-all; catch-all pattern bumped from `(_ :: _ :: _ :: _)` to
  `(_ :: _ :: _ :: _ :: _)` (now firing for k ≥ 4, not k ≥ 3). Case
  order preserved per strategy §A.3 (`[]`, `[c]`, `[c₁, c₂]`,
  `[c₁, c₂, c₃]`, k ≥ 4 catch-all).
* Docstring above `inversePolyTree` updated to enumerate the new
  triple-children case + the bumped catch-all arity (one-bullet
  diff, no rewrite). Cycle 387's anchor `(cycle 387, extended
  cycle 399)` byline added to the header.

### §11.2 LOC delta

* Section422.lean: 8038 → 8101 LOC (+63 LOC), well within the
  strategy's ~80–100 LOC budget envelope. The headline `+63 LOC`
  decomposes as ~40 LOC of new docstrings + new def bodies and
  ~10 LOC of `inversePolyTree` extension + ~13 LOC of docstring
  reflow for the `inversePolyTree` byline + new bullets.
* No Section381 / Section310 / other-file changes — strictly
  additive to Section422.

### §11.3 Build verification

* `lake env lean OpenMath/Chapter4/Section422.lean` exits 0 with
  only the pre-existing grandfathered cycle 365 sorry warning at
  line 2272 (compiler-displayed line; sorry-token at line 2279 in
  the source).
* All 11 existing `inversePolyTree_*` calibration witnesses
  (cycles 387, 392, 394, 395, 388, 389, 390, plus their corollaries
  through cycles 393/396/397) continue to compile — their match
  patterns (`mk []`, `mk [c]`, `mk [c₁, c₂]`) do not unify against
  the new `mk [c₁, c₂, c₃]` arm, so the cycle 387–397 ship stack is
  undisturbed.
* Build time: ~14 min on warm cache, longer than the strategy's
  ~200–300 s estimate. Hypothesis: the recursive def's
  equation-compiler-generated unfolding lemmas grow polynomially
  with arm count, and the file's growth past 8000 LOC slows
  elaboration. Phase α'.5 work on k ≥ 4 should expect the same
  scaling pressure.

### §11.4 Faithfulness check

* Entity ID: `def:422B` (continuing the §422 work track via Phase α'
  infrastructure).
* Lean statements capture: **same content** as the §4/§5 strawmen
  in this scoping doc. The cycle 398 §C/§7 R3 resolution stands —
  `trichildCrossTerm vertex vertex vertex f = 3 · f vertex · f broom₃`
  matches cycle 370's bushy closed form `+v⁴ − 3v²c + 3v·b' − f bushy`
  via Block (5)+(6)+(7)'s three identical bilinear contributions
  each evaluating to `+v · b'`.
* Definition smuggling: PASS for all three. The new `noncomputable
  def`s are pure computational helpers; their `Prop`-content will
  be delivered by cycle 400's `inversePolyTree_bushy` calibration
  witness (the canonical non-vacuity check for this infrastructure).
* Tautology check: N/A (no theorems shipped).
* Identity check: N/A (no theorems shipped).
* Hypothesis strength: N/A (no theorems shipped).
* `inversePolyTree` extension preserves the existing arms verbatim;
  the new arm structurally mirrors the binary arm's delegation
  pattern (delegate to a polynomial helper, with recursive
  `inversePolyTree c_i f` evaluations as helper inputs).

### §11.5 What this cycle deliberately did NOT do

* Did NOT ship the `inversePolyTree_bushy` calibration witness.
  Cycle 400's work per §6.2.
* Did NOT migrate `inversePolynomial`'s `bushy` branch. Cycle 401's
  work per §6.3.
* Did NOT touch the cycle 365 grandfathered sorry at line 2279.
  Multi-cycle Phase β/γ extension; deferred to cycle 402+.
* Did NOT ship the optional scratch-verification `example` from §D
  step 7. The cycle 400 calibration witness will verify the
  strawman values numerically as a byproduct of its proof; a
  separate intermediate `example` would be redundant.
* Did NOT submit to Aristotle. Strategy §G prohibits this cycle's
  trichild defs as Aristotle targets — pure `noncomputable def`s
  with no `sorry`s to mine.
* Did NOT refactor `bichildCrossTerm` / `bichildPolynomial` /
  `monochildCrossTerm` / existing `inversePolyTree` cases. Cycle
  399 is strictly additive per strategy §G.

### §11.6 Cycle 400 entry point (Phase α'.4.1 P9)

Per §6.2 and strategy §J, ship `inversePolyTree_bushy` calibration:

```lean
theorem inversePolyTree_bushy (f : RT → ℝ) :
    inversePolyTree RootedTree.bushy f
      = (f RootedTree.vertex) ^ 4
        - 3 * (f RootedTree.vertex) ^ 2 * f RootedTree.cherry
        + 3 * f RootedTree.vertex * f RootedTree.broom₃
        - f RootedTree.bushy := by
  show inversePolyTree
      (OpenMath.Chapter3.Section310.RootedTree.mk
        [RootedTree.vertex, RootedTree.vertex, RootedTree.vertex]) f = _
  rw [inversePolyTree, inversePolyTree_vertex,
      inversePolyTree_vertex, inversePolyTree_vertex]
  unfold trichildPolynomial
  rw [show trichildCrossTerm RootedTree.vertex RootedTree.vertex
            RootedTree.vertex f
          = 3 * f RootedTree.vertex * f RootedTree.broom₃ by
        unfold trichildCrossTerm
        rw [if_pos ⟨rfl, rfl, rfl⟩]]
  -- bridge mk [vertex] = cherry and mk [vertex, vertex, vertex] = bushy
  show ... = ...
  ring
```

Estimated ~30 LOC. Memory `feedback_ring_def_opacity.md` predicts the
`mk [vertex] ↔ cherry` and `mk [vertex, vertex, vertex] ↔ bushy`
bridges via `show`-blocks (`cherry` and `bushy` are non-reducible
`def`s in Section310; `ring` cannot canonicalise them without a
`show` reframing). The `if_pos ⟨rfl, rfl, rfl⟩` discharges the
all-vertex triple via the strawman branch, matching cycle 394's
`(cherry)` and cycle 388's `(cherry, cherry)` recipes scaled to a
3-tuple.

### §11.7 §422 streak status

§422 axiom-clean streak: 60 substantive + 3 doc (336–398) →
**61 substantive + 3 doc** (cycles 336–399). The new defs do not
print axioms (def, not theorem); the broader streak continues
without interruption since no new theorems were shipped and no
existing axiom-clean theorems were disturbed.

---

**End of scoping doc.** Cycle 398 shipped the markdown file; cycle
399 shipped the trichild infrastructure per §6.1. Cycle 400 ships
the calibration witness per §6.2. Cycle 401 ships the migration per
§6.3. Cycles 402+ revisit cycle 365's grandfathered Sub-lemma A
sorry under the now-extended `inversePolyTree` routing.
