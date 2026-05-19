# Cycle 398 strategy — Phase α'.4.3 scoping for bushy migration

## TL;DR

Ship a **markdown-only scoping doc** for Phase α'.4.3:
`.prover-state/issues/def_422B_phase_alpha_prime_family_bushy_scoping.md`.
This is the cycle 397 worker's explicit cycle-398 recommendation and
follows the cycle 373 / 379 / 385 precedent of multi-cycle Lean ships
preceded by a focused scoping doc.

The remaining migration target is `bushy = mk [vertex, vertex, vertex]`
— the **last** unmigrated ladder tree. It needs a 3-children-aware
extension to `inversePolyTree`'s recursion. The closed form has a
non-trivial bilinear cross-term contribution (paper math suggests
`+3v·b'`), and the cycle 358 `_inv_mk` block decomposition has 8
blocks for three children (vs 4 for two). One-cycle direct attempts
without a derivation plan risk getting signs / coefficients wrong.

**Do NOT ship Lean infrastructure this cycle.** Specifically: do not
extend `inversePolyTree`'s match, do not define `trichildPolynomial`,
do not ship `inversePolyTree_bushy`. All multi-cycle scope; cycle
399–401 plan deliverable per §6 of the scoping doc below.

§422 axiom-clean streak: 60 substantive + 2 doc (cycles 336–397) →
**60 substantive + 3 doc** (cycles 336–398) after this ship.

## Context (read first)

### What just landed (cycle 397)

Cycle 397 shipped Phase α'.4.2 P4 — 4th ladder migration. The
`mk [mk [cherry]]` branch of `inversePolynomial` now dispatches
through `inversePolyTree (mk [mk [cherry]]) f`. Six edits; all
axiom-clean; sorry count unchanged at 5 (4 docstring + 1
grandfathered cycle 365 code at line 2272).

### Current Phase α'.4.2 migration status

`inversePolynomial`'s 9-way `if-then-else` cascade currently routes:

| Tree | Dispatch | Cycle |
|---|---|---|
| vertex | `inversePolyChain 0` | Family A (cycle 380) |
| cherry | `inversePolyChain 1` | Family A |
| broom₃ | `inversePolyBroom 2` | Family B (cycle 383) |
| mk [cherry] | `inversePolyTree (mk [cherry])` | ✓ cycle 396 |
| **bushy** | **`inversePolyBroom 3`** | **Family B (cycle 383) — TARGET** |
| mk [broom₃] | `inversePolyTree (mk [broom₃])` | ✓ cycle 393 |
| mk [vertex, cherry] | `inversePolyTree (mk [vertex, cherry])` | ✓ cycle 391 |
| mk [mk [cherry]] | `inversePolyTree (mk [mk [cherry]])` | ✓ cycle 397 |

`bushy` is the last non-trivial unmigrated tree. After it lands, all
9 ladder trees route uniformly through `inversePolyTree`, unlocking
the eventual closure of cycle 365's grandfathered sorry
(`powRep_sum_eq_of_strict_subtree_agreement` at line 2272).

### Why bushy needs new infrastructure

`bushy = mk [vertex, vertex, vertex]` has **three** children, but
`inversePolyTree`'s current recursion (Section422.lean:6412–6423)
explicitly defers k ≥ 3:

```lean
noncomputable def inversePolyTree : RT → (RT → ℝ) → ℝ
  | mk [], f       => -f vertex
  | mk [c], f      => -(v · inversePolyTree c f) + monochildCrossTerm c f - f (mk [c])
  | mk [c₁, c₂], f => bichildPolynomial c₁ c₂ (inversePolyTree c₁ f) (inversePolyTree c₂ f) f
  | mk (_ :: _ :: _ :: _), _ => 0   -- ← deferred
```

Bushy migration requires:
1. New helper `trichildPolynomial : RT → RT → RT → ℝ → ℝ → ℝ → (RT → ℝ) → ℝ`
   analogous to cycle 387's `bichildPolynomial`.
2. New helper `trichildCrossTerm : RT → RT → RT → (RT → ℝ) → ℝ`
   with a `(vertex, vertex, vertex)` dispatch.
3. Structural extension of `inversePolyTree`'s match: insert
   `[c₁, c₂, c₃]` BEFORE the existing catch-all.
4. `inversePolyTree_bushy` calibration witness.
5. Migration of `inversePolynomial`'s `bushy` branch.

This is the multi-cycle scope the scoping doc plans.

## Priority 1 — DELIVERABLE: Phase α'.4.3 scoping doc

### File location

Create
`.prover-state/issues/def_422B_phase_alpha_prime_family_bushy_scoping.md`.

### Structural precedent

Read `.prover-state/issues/def_422B_phase_alpha_prime_family_C_scoping.md`
(cycle 385) before drafting. It is the closest structural precedent
(also a Phase α'.4 sub-scoping ahead of Lean ship cycles). Cycle 385
ran 9 sections / 621 lines and drove cycles 386–396's productive
11-cycle ladder. Target: 8–10 sections, 400–600 lines.

### Required sections

**§1 Status & blocker** (~50 lines)

* Acknowledge: markdown-only cycle, no Lean code shipped.
* §422 streak: 60 substantive + 2 doc → 60 substantive + 3 doc.
* Cite cycle 397's task results §"Suggested next approach" as the
  explicit cycle-398 recommendation.
* Cross-reference predecessor scoping docs:
  - `.prover-state/issues/def_422B_subLemmaA_inductive_plan.md` (cycle 373).
  - `.prover-state/issues/def_422B_phase_alpha_prime_scoping.md` (cycle 379).
  - `.prover-state/issues/def_422B_phase_alpha_prime_family_C_scoping.md` (cycle 385).
* Note bushy is the **last** ladder migration; unlocks cycle 365
  sorry closure path.

**§2 The bushy closed form** (~30 lines)

Quote cycle 370's `elementaryWeightQ_phi_inv_bushy` verbatim from
`OpenMath/Chapter4/Section422.lean:3011`:

```
Φ_{η_q⁻¹}(bushy) = v⁴ − 3v²·c + 3v·b' − Φ_η(bushy)
```

where `v = Φ_η(vertex)`, `c = Φ_η(cherry)`, `b' = Φ_η(broom₃)`.

Cross-check against Family B (cycle 382's `inversePolyBroom 3`):
- j=0: `(-1)^4·C(3,0)·v³·v = v⁴` ✓
- j=1: `(-1)^5·C(3,1)·v²·c = -3v²c` ✓
- j=2: `(-1)^6·C(3,2)·v·b' = 3v·b'` ✓
- j=3: `(-1)^7·C(3,3)·1·f(bushy) = -f(bushy)` ✓

So `bushy` is Family B at k=3 algebraically; the Phase α'.4.2
migration unifies dispatch through `inversePolyTree` (currently
through `inversePolyBroom`).

**§3 Block decomposition for three children** (~80 lines)

Cycle 385's §3.2 decomposed two-children product expansions into 4
blocks. For three children, the analogous decomposition has **2³ = 8
blocks** indexed by the (constant vs A-row-sum) choice at each child:

| Block | Selection | Algebraic shape |
|---|---|---|
| (1) | c · c · c | `inv₁ · inv₂ · inv₃` |
| (2) | A · c · c | `(Σⱼ Aᵢⱼ dw(t₁,j)) · inv₂ · inv₃` |
| (3) | c · A · c | symmetric |
| (4) | c · c · A | symmetric |
| (5) | A · A · c | bilinear in `(t₁, t₂)`, const on `t₃` |
| (6) | A · c · A | bilinear in `(t₁, t₃)`, const on `t₂` |
| (7) | c · A · A | bilinear in `(t₂, t₃)`, const on `t₁` |
| (8) | A · A · A | trilinear in `(t₁, t₂, t₃)` |

After multiplying by `M.b i` and summing over `i`:

* Block (1) → `(Σᵢ bᵢ) · inv₁ · inv₂ · inv₃ = v · inv₁ · inv₂ · inv₃`.
* Blocks (2/3/4) → `inv_j · inv_k · Φ_η(mk [t_other])`. The A-row-sum
  collapses to a one-child closed form.
* Blocks (5/6/7) → bilinear cross-terms surfacing a two-children
  kernel `Φ_η(mk [t_i, t_j])` for each pair.
* Block (8) → trilinear cross-term surfacing `Φ_η(mk [t₁, t₂, t₃])`
  itself (the self-kernel).

**§4 Conjectured `trichildPolynomial` shape** (~80 lines)

Strawman analogous to cycle 387's `bichildPolynomial`:

```lean
noncomputable def trichildPolynomial
    (t₁ t₂ t₃ : RT) (inv₁ inv₂ inv₃ : ℝ) (f : RT → ℝ) : ℝ :=
  -(f vertex * inv₁ * inv₂ * inv₃)        -- Block (1), -v prefactor
  - inv₂ * inv₃ * f (mk [t₁])              -- Block (2)
  - inv₁ * inv₃ * f (mk [t₂])              -- Block (3)
  - inv₁ * inv₂ * f (mk [t₃])              -- Block (4)
  + trichildCrossTerm t₁ t₂ t₃ f           -- Blocks (5)–(8)
  - f (mk [t₁, t₂, t₃])                    -- self-term
```

Sign convention: matches cycle 387's bichildPolynomial leading `-`
sign (the cycle 358 `_inv_mk` prefactor `-Σⱼ M.b j · ...`).

**Sanity verification at bushy** (paper, not Lean):

For `(t₁, t₂, t₃) = (vertex, vertex, vertex)`:
- `inv₁ = inv₂ = inv₃ = inversePolyTree vertex f = -v`.
- Block (1): `-(v · (-v) · (-v) · (-v)) = -(v · -v³) = v⁴` ✓
- Blocks (2/3/4): each = `-(-v) · (-v) · f(mk[vertex])
  = -v² · c`. Three of these: `-3v²c` ✓
- Block (?) for `+3v·b'`: comes from `trichildCrossTerm vertex vertex vertex f`.

So the strawman gives `v⁴ - 3v²c + trichildCrossTerm vertex vertex vertex f - f(bushy)`.
Matching cycle 370's `v⁴ - 3v²c + 3v·b' - f(bushy)` forces

```
trichildCrossTerm vertex vertex vertex f = 3 · f vertex · f broom₃.
```

The `3v·b'` comes from the three (5)/(6)/(7) bilinear blocks at
`(v, v, v)`, each surfacing `Φ_η(mk [vertex, vertex]) = Φ_η(broom₃)
= b'` with prefactor `v`. Block (8) trilinear contributes 0 in this
case (or is absorbed into the surface `-f(bushy)` self-term).

**§5 Conjectured `trichildCrossTerm` dispatch** (~40 lines)

```lean
noncomputable def trichildCrossTerm (t₁ t₂ t₃ : RT) (f : RT → ℝ) : ℝ :=
  if t₁ = vertex ∧ t₂ = vertex ∧ t₃ = vertex then
    3 * f vertex * f broom₃
  else
    0
```

Initial dispatch; future Family C trichild work extends per cycle
388/389/390 pattern. The §7 R3 risk note below flags that the
conjectured value `3 · f vertex · f broom₃` should be **verified by
cycle 399's worker before locking** via symbolic derivation from
cycle 358's `_inv_mk`.

**§6 Lean ship plan (cycle 399–401)** (~120 lines)

**Cycle 399 (Phase α'.4.1 P8) — trichild infrastructure**:
1. Symbolically derive `trichildCrossTerm vertex vertex vertex f` from
   cycle 358's `_inv_mk` at three children = vertex. Cross-check the
   strawman §5 value.
2. Define `trichildPolynomial` and `trichildCrossTerm`.
3. Extend `inversePolyTree`'s match: insert
   `[c₁, c₂, c₃] → trichildPolynomial ...` BEFORE the existing
   k-catch-all (now `_ :: _ :: _ :: _ :: _`).
4. Verify all 9 existing calibration witnesses
   (`inversePolyTree_vertex` through `inversePolyTree_mkMkCherry`,
   plus `_mkCherryCherry`, `_mkBroomCherry`, `_mkVertexCherry`)
   still pass; expected: yes, because their proof bodies match on
   children-list shapes with k ≤ 2.
5. Non-vacuity: confirm bushy at `⟦explicitEuler⟧` evaluates correctly.

LOC budget: 80–100.

**Cycle 400 (Phase α'.4.1 P9) — `inversePolyTree_bushy` calibration**:
1. Ship `inversePolyTree_bushy : inversePolyTree (mk [vertex, vertex, vertex]) f = v⁴ − 3v²c + 3v·b' − f bushy`.
2. Proof recipe (cycle 392/394/395 pattern): `rw [inversePolyTree,
   inversePolyTree_vertex, inversePolyTree_vertex, inversePolyTree_vertex]`;
   `show trichildCrossTerm vertex vertex vertex f = 3 · f vertex · f broom₃
   by unfold; rw [if_pos ⟨rfl, rfl, rfl⟩]`; `ring`.

LOC budget: 30.

**Cycle 401 (Phase α'.4.2 P5) — `bushy` migration**:
1. Ship `inversePolyTree_bushy_eq_inversePolynomial` bridge: 7
   `if_neg` discharges + `if_pos rfl`.
2. Migrate `inversePolynomial`'s `bushy` branch from
   `inversePolyBroom 3 f` to `inversePolyTree (mk [vertex, vertex, vertex]) f`.
3. Update Phase α.2 calibration `example` (cycle 374-era).
4. Update Phase β bridge `elementaryWeightQ_phi_inv_eq_inversePolynomial_bushy`.
5. Update Phase γ branch in `inversePolynomial_eq_of_subtree_agreement`.
6. Derivative fix on cycle 382's `inversePolyBroom_three_eq_inversePolynomial`
   proof body (cycle 396 Step F precedent).

LOC budget: 50.

Total cycles 399–401: ~3 cycles, ~160 LOC.

**§7 Risk inventory** (~60 lines)

* **R1 (structural recursion extension)**: Inserting a new
  `[c₁, c₂, c₃]` case BEFORE the existing `(_ :: _ :: _ :: _) → 0`
  catch-all requires careful pattern ordering. Cycle 387 P6 noted
  this risk for the future but it never fired through cycles 388–396
  because no migration needed k ≥ 3. Mitigation: cycle 399 worker
  should re-read the cycle 387 ship at `Section422.lean:6412–6423`
  to understand current pattern order.

* **R2 (existing calibration witnesses)**: All 9 existing
  `inversePolyTree_*` calibrations match on children-list shapes
  with k ≤ 2 (`mk []`, `mk [c]`, `mk [c₁, c₂]`). The new
  `[c₁, c₂, c₃]` case won't pattern-match against any of them, so
  no existing proof body breaks. Cycle 394's lesson (extending
  `monochildCrossTerm` required adding one `if_neg` discharge in
  `inversePolyTree_cherry`) does NOT apply here because the
  extension is at the RECURSION-LEVEL match, not at the
  `monochildCrossTerm`/`bichildCrossTerm` dispatch level.

* **R3 (cross-term value — RED FLAG)**: The §5 strawman gives
  `trichildCrossTerm vertex vertex vertex f = 3 · f vertex · f broom₃`.
  Verify this against cycle 370's actual closed form at `⟦explicitEuler⟧`
  where `v = c = b' = 1, bushy = 1`:

  - Strawman value: `1⁴ - 3·1²·1 + 3·1·1 - 1 = 1 - 3 + 3 - 1 = 0`.
  - Cycle 370's actual value at `⟦explicitEuler⟧`:
    `inversePolyTree_bushy` via Family B `inversePolyBroom 3 f` at
    `f = elementaryWeightQ_phi ⟦explicitEuler⟧` should give the
    cycle 370 non-vacuity witness value. Recall cycle 370 example
    pinned the closed form to `1` at `⟦explicitEuler⟧`.

  **DISCREPANCY**: strawman gives 0, actual gives 1. This means the
  strawman §5 conjecture is **OFF**. Cycle 399's worker must derive
  the actual cross-term value symbolically from cycle 358's `_inv_mk`
  before locking the definition.

  Possible resolutions:
  - The block decomposition §3 may be missing a term (Block (8)
    trilinear might contribute non-trivially).
  - The sign convention in `trichildPolynomial` strawman §4 may be off.
  - The Family B↔C unification might need a different decomposition.

  Cycle 398's scoping doc MUST flag this red flag explicitly and
  defer the actual cross-term value to cycle 399 derivation.

* **R4 (sign convention)**: cycle 388 hit a sign issue with the
  bichild cross-term; verify the §4 trichild sign against the cycle
  358 `_inv_mk` outer `-Σⱼ M.b j · ...` prefactor.

* **R5 (file size)**: Section422.lean is already ~7867 LOC. Adding
  trichild infrastructure (cycle 399) + bushy calibration (cycle 400)
  + bushy migration (cycle 401) adds ~160 LOC. Total post-cycle-401:
  ~8030 LOC. Still tractable for warm rebuilds (cycle 397 measured
  ~200s).

**§8 Cycle 399 entry point** (~50 lines)

Pre-flight tasks for cycle 399's worker:

1. **Read cycle 358's `_inv_mk` proof body** at `Section422.lean:582`
   to understand the per-child block expansion.
2. **Read cycle 387's `bichildPolynomial` derivation** for the
   two-children precedent.
3. **Symbolically compute the three-children expansion** of
   `derivativeWeightWithSrc M.inverse i (mk [vertex, vertex, vertex])`
   per the §3 block decomposition. Specifically, compute:
   - The 8 individual block contributions to
     `Σᵢ M.b i · derivativeWeightWithSrc M.inverse i (mk [v, v, v])`.
   - Collect the `Φ_η(mk [vertex, vertex]) = Φ_η(broom₃)` contributions
     from Blocks (5)/(6)/(7) and the `Φ_η(mk [vertex, vertex, vertex])
     = Φ_η(bushy)` contribution from Block (8).
4. **Cross-check against cycle 370's closed form**. The expansion
   should recover `v⁴ - 3v²c + 3v·b' - f(bushy)` exactly.
5. **Lock the `trichildCrossTerm` value** based on the derivation,
   not the §5 strawman.
6. **THEN write** `trichildPolynomial`, `trichildCrossTerm`, and the
   `inversePolyTree` extension.

The §7 R3 red flag is the substantive technical work cycle 399 must
do. Cycle 398 scopes the problem and flags the gap; cycle 399 solves
it.

**§9 Cross-references** (~30 lines)

Standard cross-references:
* Predecessor scoping docs: cycle 373, 379, 385 issue files.
* Cycle 370 closed form: `Section422.lean:3011`.
* Cycle 358 `_inv_mk`: `Section422.lean:582`.
* Cycle 387 `bichildPolynomial` + `inversePolyTree` recursion:
  `Section422.lean:6367–6423`.
* Cycle 397 migration recipe (mechanical template for cycle 401):
  `Section422.lean` migration of `mk [mk [cherry]]` branch.
* Cycle 396 derivative-fix pattern (Step F): cycle 396 task results.
* Memory: `feedback_simp_recursive_def_overunfolds.md`,
  `feedback_indexed_inductive_cases_disjoint.md`.

**§10 Self-reference** (~20 lines)

* Cycle 398 ships this doc as sole deliverable; no Lean changes.
* Cycle 399 ships Phase α'.4.1 P8 (trichild infrastructure) per §6.
* Cycle 400 ships Phase α'.4.1 P9 (bushy calibration).
* Cycle 401 ships Phase α'.4.2 P5 (bushy migration).
* Post-cycle-401: all 9 ladder trees route uniformly through
  `inversePolyTree`. Cycle 402+ attacks the cycle 365 grandfathered
  sorry.

## Priority 2 — What NOT to ship this cycle

### Do NOT attempt direct Lean ship of trichild infrastructure

The §7 R3 red flag is real: the strawman §5 cross-term value gives
the WRONG closed-form value at `⟦explicitEuler⟧`. A one-cycle attempt
to ship `trichildPolynomial` + `inversePolyTree_bushy` without
resolving R3 will produce an incorrect definition that downstream
cycles 400–401 will need to roll back.

### Do NOT touch existing `inversePolyTree`

The cycle 387 `(_ :: _ :: _ :: _) → 0` catch-all is the current
ship; modifying it without the trichild infrastructure leaves the
file in an inconsistent state.

### Do NOT skip bushy migration via alternate route

Cycle 397 worker recommended unification through `inversePolyTree`.
Don't try to make `inversePolynomial`'s `bushy` branch dispatch
through some other helper; that creates a divergent path that breaks
the cycle 365 sorry closure plan.

### Do NOT pivot to a fresh entity

`def:451A`, `thm:535A`, `thm:541A`, etc. — all available but losing
the 60-cycle §422 streak is a high cost. The bushy migration is one
scoping cycle + three Lean cycles away from completing Phase α'.4.

### Do NOT attempt cycle 365 sorry closure

The cycle 366 heterogeneous-stage obstacle is unresolved until ALL 9
ladder trees route through `inversePolyTree`. Bushy is the gate.

### Do NOT raise `maxHeartbeats`

Per CLAUDE.md.

### Do NOT edit `scripts/autonomous_loop.py`

Loop-maintainer territory.

### Do NOT attempt Section441.lean

43+ cycle GPFS slowness pathology per `cycle_182_gpfs_slowness.md`.

## Priority 3 — Optional stretch (if scoping doc finishes early)

If the scoping doc is complete with substantial cycle budget
remaining (~30 minutes), the only safe Lean ship is:

**Optional cycle 398 P2 stretch**: One axiom-clean
sanity-cross-check `example` (NOT a `theorem`) at the bushy closed
form. E.g.:

```lean
example :
    elementaryWeightQ_phi (⟦⟨1, RKTableau.explicitEuler⟩⟧ : Quotient
      OpenMath.Chapter3.Section312.RKTableau.PhiEquivalent.setoidSigma)⁻¹
      RootedTree.bushy
    = 1 := by
  -- Verify cycle 370's bushy closed form value at ⟦explicitEuler⟧.
  ...
```

This is a one-shot non-vacuity confirmation that the §2 closed form
gives `1` at `⟦explicitEuler⟧` (where `v = c = b' = 1, bushy = 1`,
giving `1 - 3 + 3 - 1 = 0`... wait, that's 0, not 1).

Wait — `elementaryWeightQ_phi` at the INVERSE (η_q⁻¹), and
cycle 370's closed form gives `Φ_{η_q⁻¹}(bushy) = v⁴ - 3v²c + 3v·b' - Φ_η(bushy)`.
Substituting v=c=b'=Φ_η(bushy)=1: `1 - 3 + 3 - 1 = 0`. So at
`⟦explicitEuler⟧`, `Φ_{⟦explicitEuler⟧⁻¹}(bushy) = 0`.

But cycle 370's `elementaryWeightQ_phi_inv_bushy` non-vacuity
example pinned this to `1`. Let me re-read cycle 370 task results...

Actually cycle 370 says:
> non-vacuity examples: closed-form witness gives `1`; reflexive m=0
> closes by `rfl × 4`.

So `1`. But the algebraic check gives `0`. There's a discrepancy
between cycle 370's recorded non-vacuity value and the algebraic
substitution. **This is exactly the §7 R3 red flag** — cycle 398's
scoping doc must flag this discrepancy explicitly. The P2 stretch
above SHOULD ship to verify which value is correct, but doing so
requires actually running the Lean check.

**Recommended P2 stretch**: Yes, ship the verification `example`.
If the value is `0`, cycle 370 task results are wrong; if `1`,
the algebraic substitution above (and §4/§5 strawmen) are wrong.
Either way, this is critical sanity data for cycle 399.

LOC: 5–15. Risk: low. The Lean answer is authoritative.

**If cycle 398 P2 ship reveals cycle 370's value is correct (1):**
the §4/§5 strawmen in the scoping doc are wrong, and cycle 399's
worker must derive the correct closed form symbolically. Document
the resolution in the scoping doc's §7 R3.

**If cycle 398 P2 ship reveals cycle 370's value is wrong (0):**
flag for the loop maintainer; cycle 370's recorded value should be
audited. Cycle 399 proceeds with strawman §4/§5 unchanged.

## Priority 4 — Aristotle status

No pending Aristotle results. No new submissions needed.

## Sanity checklist for cycle 398 worker

Before declaring scoping doc complete:

1. **§2 closed form correctly quoted from cycle 370**:
   `v⁴ − 3v²c + 3v·b' − f bushy`.
2. **§3 block decomposition has 8 blocks** with the (constant vs
   A-row-sum) selection structure.
3. **§4 strawman trichildPolynomial sign convention verified at
   bushy**: under inv = -v at three children, the leading `-(v · inv³)`
   gives `+v⁴`.
4. **§7 R3 red flag explicitly called out**: the strawman §5 cross-term
   value at `(vertex, vertex, vertex)` is NOT verified; cycle 399 must
   derive it from cycle 358's `_inv_mk`.
5. **§6 cycle 399–401 plan is concrete**: named deliverables, LOC
   estimates, proof recipe sketches.
6. **§8 cycle 399 entry point lists pre-flight steps** in order.

## Faithfulness check

This cycle ships only `.prover-state/issues/def_422B_phase_alpha_prime_family_bushy_scoping.md`
(new markdown file). No Lean changes, no new `def`/`theorem`/`structure`,
no axioms, no sorries (unchanged at 5: 4 docstring + 1 grandfathered).

The scoping doc itself does not "smuggle" content: §4/§5 propose
strawmen, §7 R3 flags the open red flag, §8 explicitly defers
verification to cycle 399.

`lean_status.json` `def:422B` row: stays `partial`, `cycle_completed_at`
bumped from 397 to 398.

`plan.md` `def:422B` row: stays `[~]`.

## Expected outcomes

* Sorry count: **5 (unchanged)**.
* §422 axiom-clean streak: 60 substantive + 2 doc → **60 substantive + 3 doc**.
* `lake build OpenMath.Chapter4.Section422` exit 0 (no Lean changes).
* `git diff --stat` shows only `.prover-state/` paths.
* New file:
  `.prover-state/issues/def_422B_phase_alpha_prime_family_bushy_scoping.md`
  (~400–600 lines, 8–10 sections).

## Cycle 399 entry point (for continuity)

Cycle 399 ships Phase α'.4.1 P8 per the scoping doc §6:

1. (FIRST) Symbolically derive `trichildCrossTerm vertex vertex vertex f`
   from cycle 358's `_inv_mk` at three children = vertex. Resolve §7 R3.
2. Define `trichildPolynomial`, `trichildCrossTerm` (with derived value).
3. Extend `inversePolyTree`'s match.
4. Verify all 9 existing calibrations still pass.
5. Confirm bushy at `⟦explicitEuler⟧` matches cycle 370's witness.

LOC budget: ~80–100. Risk: low-medium (the symbolic derivation in
step 1 is the substantive new content; the rest is mechanical).
