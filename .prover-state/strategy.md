# Cycle 385 strategy — §422 Phase α'.4 Family C scoping doc

## TL;DR

Ship a markdown-only Family C scoping document
`.prover-state/issues/def_422B_phase_alpha_prime_family_C_scoping.md`
distilling the three Family C witnesses (cycles 371, 372, 384) into a
concrete multi-cycle plan for a unified `inversePolyTree` recursion
that handles heterogeneous-children trees. No Lean code this cycle.

This follows the cycle 373 (Sub-lemma A inductive plan) and cycle 379
(Phase α' recursive design) precedent: zero-Lean scoping cycles that
directly drove subsequent multi-cycle ladder builds (cycles 374–378,
380–384). The cycle 384 worker's "Suggested next approach" explicitly
endorses this as the next move.

## Status going in

- **§422 axiom-clean streak**: 48 substantive + 1 doc (cycles 336–384).
- **Section422.lean**: ~6520 LOC, 1 grandfathered sorry at line 2272
  (cycle 365 Sub-lemma A general body).
- **Cycle 384 ship**: 9th-tree closed form `Φ_{η_q⁻¹}(mk [cherry,
  cherry]) = −v⁵ + 4v³c − 3vc² − v²b' − 2v²m + 2cm + 2v·vc' − C`
  (8 terms, 6 elementary-weight witnesses) + m=0 corollary, both
  axiom-clean.
- **Witness library**: 9 trees through order ≤ 5 covering Families
  A (chain), B (multi-leaf brooms), and C (heterogeneous children).
- **Cycle 384 worker discovery**: cross-tree-shape dependencies
  surface at order ≥ 5 — `mk [cherry, cherry]`'s closed form depends
  on `Φ_η(mk [vertex, cherry])`. The naive "recurse on each child"
  approach won't capture cross-term contributions.

## Priority 1 — DELIVERABLE: Family C scoping doc

**File**: `.prover-state/issues/def_422B_phase_alpha_prime_family_C_scoping.md`.

**Target length**: 400–600 lines markdown. Cycle 373's
`def_422B_subLemmaA_inductive_plan.md` (1399 lines) is the gold
standard; cycle 379's `def_422B_phase_alpha_prime_scoping.md`
(~1080 lines) is the closer template. This doc can be shorter
because the scope is narrower (Family C only, not the whole Phase α').

**Required sections** (follow cycle 379's structure):

### §1 Status & blocker

- Phase α'.1 (Family A) shipped cycles 380–381 (`inversePolyChain`).
- Phase α'.3 (Family B) shipped cycles 382–383 (`inversePolyBroom`).
- Phase α'.4 (Family C, **this scope**) remains — the unified
  recursion for heterogeneous-children trees.
- Without Phase α'.4, `inversePolynomial` cannot evaluate correctly
  on arbitrary heterogeneous-children trees outside the 9-tree
  ladder, blocking cycle 365's grandfathered sorry closure.

### §2 The three Family C witnesses (full catalog)

Tabulate explicitly with all elementary-weight names spelled out:

| Cycle | Tree | Order | σ(t) | Closed form |
|---|---|---|---|---|
| 371 | `mk [broom₃]` | 4 | 2 | `v⁴ − 3v²c + vb' + 2vm − M` |
| 372 | `mk [vertex, cherry]` | 4 | 1 | `v⁴ − 3v²c + c² + vb' + vm − V` |
| 384 | `mk [cherry, cherry]` | 5 | 2 | `−v⁵ + 4v³c − 3vc² − v²b' − 2v²m + 2cm + 2v·vc' − C` |

For each, list:
- The children list `[t₁, …, tₖ]` and each child's `Φ_η` value name.
- The number of distinct elementary-weight kernels on RHS.
- The leading `(−1)^? · v^(order)` sign (parity-determined).
- The `−Φ_η(t)` self-term sign (uniformly `−1`).
- Cross-term coefficients (the substantive content).

### §3 Structural observations (the analysis)

Three sub-sections:

#### §3.1 The `(Aᵢ − v)^k`-per-child pattern (from cycle 368/370 Discovery)

For each child `c ∈ children`, the cycle 358 `_inv_mk` formula
unrolls to contribute a factor `(M.inverse.elementaryWeight c + Σⱼ
Aᵢⱼ · ?)`. Under `inv_v = −v`, this factor takes the shape
`(−v + Σⱼ Aᵢⱼ · …)` at a leaf-child and `(closed_form_at_c + Σⱼ
Aᵢⱼ · …)` at a non-leaf-child. The product across children, summed
against `M.b i`, distributes into terms collecting elementary-weight
kernels of:
- Each individual child's elementary weights.
- **Cross-products of children's elementary weights** (the
  substantive Family C content).

#### §3.2 Cross-term cataloging

For `mk [t₁, t₂]` (binary case), the expansion of the two-factor
product yields four blocks:

1. Constant block: `inv(t₁) · inv(t₂)` evaluated.
2. Linear-in-A block from `t₁`: `inv(t₁) · Σⱼ Aᵢⱼ · …(t₂)`.
3. Linear-in-A block from `t₂`: `Σⱼ Aᵢⱼ · …(t₁) · inv(t₂)`.
4. Bilinear-in-A block (cross-term): `(Σⱼ Aᵢⱼ · …(t₁)) · (Σⱼ Aᵢⱼ ·
   …(t₂))` — the key new term Family C introduces.

The bilinear block (4) is the one that introduces the
"unexpected" elementary-weight witness in cycle 384's `mk
[cherry, cherry]`: the `Σⱼ Aᵢⱼ · (Σₖ Aⱼₖ)` factor from each
cherry child produces `Φ_η(mk [vertex, cherry])` via the
cons-case unfold of `derivativeWeightWithSrcProd`.

#### §3.3 Why Family A and Family B miss this

- **Family A** (single-child chain): only block (1) and (2)
  contribute (no second child). No cross-term.
- **Family B** (k identical leaves): block (4) collapses by
  binomial expansion because every leaf-factor is `(Aᵢ − v)`,
  giving a clean `(Aᵢ − v)^k` expansion without distinct
  cross-tree-shape contributions.
- **Family C** is the **genuine multi-child heterogeneous case**
  where block (4) produces new elementary-weight kernels not
  matched by either Family A or B.

### §4 Conjectured `inversePolyTree` recursion

Propose Variant V4 (a new variant, extending §5 of cycle 379's
scoping doc):

```lean
noncomputable def inversePolyTree (t : RT) (f : RT → ℝ) : ℝ :=
  match t with
  | RootedTree.mk children =>
      -- Per-child Family A/B/C decomposition: recurse on each child,
      -- track per-child "row-sum signature" σ_c aggregating
      -- cross-product contributions.
      sorry  -- design pending
```

Document **what needs to be added** beyond Family A (cycle 380's
`inversePolyChain`) and Family B (cycle 382's `inversePolyBroom`):
- A **pairwise children-product helper** that captures the
  bilinear-in-A cross-term contributions.
- Conjecturally, the helper takes shape
  `bichildPolynomial : (RT × RT) → (RT → ℝ) → ℝ` returning
  `Φ_η(mk [t₁, t₂]) + (cross-correction)`.

Acknowledge the design is **not pinned** — Phase α'.4 needs more
data points before the recursive shape can be locked. Two specific
data points would close it:

1. `mk [broom₃, cherry]` (order 6): mixed-children with both
   non-leaf children of different orders. Tests the bilinear
   block at non-symmetric inputs.
2. `mk [cherry, broom₃]` (order 6): symmetric to above by
   commutativity — gives a redundancy check.

If both yield the same cross-term coefficient pattern (e.g. the
order-mixing factor is symmetric `(order t₁) · (order t₂)`-style),
the recursive recipe is constrained enough to ship in cycle 386+.

### §5 Phase decomposition

Three sub-phases at 1–2 cycles each:

| Sub-phase | Cycles | Deliverable |
|---|---|---|
| α'.4.0 | 1 (cycle 386) | One more Family C witness: `mk [broom₃, cherry]` or `mk [vertex, broom₃]` (order 6). Pin the cross-term recipe. |
| α'.4.1 | 1–2 (cycle 387+) | Ship recursive `inversePolyTree` (Variant V4) with a `bichildPolynomial` helper. Calibration witnesses against all 11+ ladder trees. |
| α'.4.2 | 1 (cycle 388+) | Migrate `inversePolynomial`'s Family C branches to dispatch to `inversePolyTree`. Phase γ extension. |

### §6 Risk assessment

Tabulate:

| Risk | Severity | Mitigation |
|---|---|---|
| R1: recursion shape under-determined by 3 data points | HIGH | Ship 4th witness in cycle 386 before designing recursion |
| R2: cross-term symmetry under child-permutation | MEDIUM | Ship symmetry-witness pair (`mk [a, b]` and `mk [b, a]`) |
| R3: order-6+ trees have NEW elementary-weight dependencies | MEDIUM | Witness-accumulation discipline + scoping refinement |
| R4: `bichildPolynomial` LOC budget exceeds single cycle | LOW | Phase α'.4.1 estimate already allows 2 cycles |

### §7 Cycle 386 entry point

Recommended target: ship the 10th tree witness `mk [broom₃, cherry]`
(order 6).

- σ(mk [broom₃, cherry]) = 1 (no children-multiplicity).
- Predicted closed form: 10–12 terms in the polynomial (extrapolating
  cycle 384's 8 terms for order 5).
- Predicted elementary-weight kernels: 7–8 distinct (potentially
  including new order-5 kernels and `mk [broom₃, cherry]` itself).
- Proof template: cycle 384's recipe with binary product over the
  heterogeneous pair `(broom₃, cherry)` — the bilinear cross-term
  becomes asymmetric and exposes the order-mixing pattern.

LOC budget: ~250 LOC.

### §8 Cross-references

- `.prover-state/issues/def_422B_subLemmaA_inductive_plan.md` (cycle
  373) — Sub-lemma A inductive plan.
- `.prover-state/issues/def_422B_phase_alpha_prime_scoping.md`
  (cycle 379) — Phase α' recursive design.
- Section422.lean cycle 371 / 372 / 384 ships — the three Family C
  witnesses.
- `.prover-state/issues/def_422B_path.md` — overall `def:422B`
  roadmap.

### §9 Self-reference

- Cycle 385 ships this doc.
- Cycle 386 ships the 10th-tree Family C witness per §7.
- Cycle 387+ ships Phase α'.4.1 (`inversePolyTree` + helper).

## Priority 2 — IF time permits (stretch, optional)

If the scoping doc closes early, ship **one** non-vacuity sanity
witness for cycle 384's `mk [cherry, cherry]` closed form at a
**different** explicit RK method beyond `explicitEuler`. Candidates:

- `paddedEuler` (cycle 030, `RKTableau 2`): at this method,
  `Φ_η(vertex) = 1`, etc. (verify before shipping). Witness shape:
  `Φ_{⟦paddedEuler⟧⁻¹}(mk [cherry, cherry]) = <numerical value>`.

**Do NOT** ship another full closed-form witness (a 10th tree) as
P2 — that's cycle 386's job under the scoping doc plan, not a
stretch this cycle. Witness-treadmill restraint is the cycle 372/378
worker's standing directive.

## Priority 3 — NO LEAN CODE THIS CYCLE

Cycle 385 is a markdown-only scoping cycle. Do NOT modify
`Section422.lean` or any other Lean file. If the scoping doc takes
the full cycle budget, that's the expected outcome.

The cycle 373 precedent is the model: it shipped only markdown
(`def_422B_subLemmaA_inductive_plan.md`) and directly drove cycles
374–378's 8-tree ladder build-out. The cycle 379 precedent is the
same shape: shipped `def_422B_phase_alpha_prime_scoping.md`, drove
cycles 380–383's Family A/B migrations.

## What NOT to do

- **Do NOT continue the witness-accumulation treadmill** without
  scoping. The cycle 384 worker explicitly flagged Family C as
  needing a unified plan, not more individual closed forms. Adding
  10th, 11th, 12th witnesses without first identifying the recursive
  recipe is wasted effort. (P2 above is a sanity *example*, not a
  new closed form.)
- **Do NOT attempt the cycle 365 grandfathered sorry** general body
  this cycle. It remains gated on Phase α'.4 (and likely on Phase β
  / γ migration after that). Multi-cycle work, not a single-cycle
  target.
- **Do NOT attempt the cycle 370 broom-family general theorem**
  this cycle. Family B is fully ladder-migrated as of cycle 383; the
  general inductive form on `broomTree k` is deferred to a future
  cycle.
- **Do NOT modify `inversePolyChain` (Family A) or `inversePolyBroom`
  (Family B)**. Both are stable and consumed by `inversePolynomial`'s
  dispatch table; the scope here is Family C only.
- **Do NOT attempt to ship a `bichildPolynomial` helper in cycle 385**.
  The recipe needs at least one more data point (cycle 386's
  `mk [broom₃, cherry]` ship) before the recursive shape can be
  pinned down without speculation.
- **Do NOT pivot to a fresh entity** to break the §422 streak. While
  48 consecutive cycles is long, the streak is **productive** — each
  cycle ships axiom-clean progress toward `def:422B` closure. The
  cycle 384 worker's "Suggested next approach" recommends staying in
  §422 with the scoping doc. Pivoting now would lose compound
  momentum.
- **Do NOT attempt §441 Section441.lean work**. The GPFS-slowness
  blocker (cycle 182+ pathology) is still in effect; the standing
  guidance is "skip §441 path".
- **Do NOT introduce sorries**. Cycle 200/201 and 149/150 rollback
  precedents stand: sorry-first scaffolds on multi-cycle targets
  without single-cycle close paths get rolled back. The scoping doc
  has no Lean code, so this is trivially preserved.

## What success looks like

- One new markdown file at
  `.prover-state/issues/def_422B_phase_alpha_prime_family_C_scoping.md`.
- 400–600 lines covering §1–§9 above.
- Cross-links to cycles 371 (`mk [broom₃]`), 372 (`mk [vertex,
  cherry]`), 384 (`mk [cherry, cherry]`).
- Cross-links to cycle 373 (`subLemmaA_inductive_plan.md`) and
  cycle 379 (`phase_alpha_prime_scoping.md`).
- Concrete cycle 386 entry point (the 10th-tree witness target).
- Zero Lean changes (no new files, no diffs against `Section422.lean`
  or any other Lean file).
- Sorry count unchanged at 1 (the grandfathered cycle 365 sorry).
- §422 axiom-clean streak advances to 48 substantive + 2 doc cycles
  (336–385).

## Self-check before shipping

- [ ] Scoping doc has all 9 sections (§1 through §9).
- [ ] All three Family C witnesses' closed forms transcribed accurately
  from the cycle 371 / 372 / 384 ships (cross-reference the
  `Section422.lean` line numbers).
- [ ] Cycle 386 entry point names a concrete target tree and a
  concrete LOC budget.
- [ ] No Lean files modified (`git diff --stat` should show only
  `.prover-state/` paths).
- [ ] `task_results/cycle_385.md` documents the markdown-only ship
  pattern, citing cycle 373 / 379 precedent.
- [ ] `plan.md` row for `def:422B` left at `[~]` (still partial;
  no migration).
- [ ] `lean_status.json` row for `def:422B` left at `partial`.
