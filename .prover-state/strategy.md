# Cycle 379 strategy — Phase α' scoping doc (recursive `inversePolynomial` design)

## Context (read first)

Cycle 378 closed the 8-tree ladder for `def:422B` Sub-lemma A:
`vertex`, `cherry`, `broom₃`, `mk [cherry]`, `bushy`, `mk [broom₃]`,
`mk [vertex, cherry]`, `mk [mk [cherry]]`. Each tree has an axiom-clean
closed-form theorem `elementaryWeightQ_phi_inv_<tree>`, an m=0 corollary
of cycle 365's Sub-lemma A signature, an `inversePolynomial` branch
(Phase α.1–α.4), a calibration witness, a per-tree Phase β bridge,
and is uniformly handled by the Phase γ closed-subtree-agreement
theorem `inversePolynomial_eq_of_subtree_agreement`.

§422 axiom-clean streak: **43 substantive + 1 doc** (cycles 336–378).
Single grandfathered sorry remains at `Section422.lean:2279` (cycle
365's `powRep_sum_eq_of_strict_subtree_agreement` general body).
Section422.lean: 5595 LOC. Section381.lean: 5621 LOC. `grep -c sorry`
on Section422.lean = 5 (4 docstring references + 1 actual code sorry).

Cycle 378 worker's strong recommendation (their "Option A"): **pivot
to a Phase α' scoping doc** rather than accumulate a 9th ladder tree.
The witness library is sufficient for structural pattern identification,
and the strategic value of designing the recursive `inversePolynomial`
exceeds the marginal value of another empirical data point.

This cycle follows the cycle 373 precedent
(`def_422B_subLemmaA_inductive_plan.md`): pure markdown scoping doc,
zero Lean churn, prepares 3–5 cycles of Phase α' implementation work.

## Priority 1 — DELIVERABLE — Write the Phase α' scoping doc

Create **`.prover-state/issues/def_422B_phase_alpha_prime_scoping.md`**.

Target length: ~600–900 lines (matching cycle 373's
`def_422B_subLemmaA_inductive_plan.md` and cycle 357's
`def_422B_phase_D_3_scoping.md` precedents).

### Required sections

**§1. Status & blocker**
- One paragraph: what cycle 378 left in place, why Phase α' is the
  next natural step, why this is markdown-only (multi-cycle research
  effort).
- Reference the cycle 373 doc-only precedent + cycle 374's strategy
  authorization for doc-only ships.

**§2. The current `inversePolynomial` definition (Phase α.1–α.4 status)**
- Quote the definition's shape from `Section422.lean` (find it via
  `grep -n "noncomputable def inversePolynomial" OpenMath/Chapter4/Section422.lean`).
  It's an 8-way `if-then-else` pattern match on the 8 trees, with `0`
  as the placeholder for all other trees.
- List the 8 matched branches and their closed-form expressions.
- Note the limitation: any tree not in the 8-tree ladder evaluates to
  `0`, which is wrong for Sub-lemma A's general body (the cycle 365
  grandfathered sorry).

**§3. The 8 closed forms — empirical catalog**

Build a table:

| Cycle | Tree | Order | σ(t) | Closed form for `Φ_{η_q⁻¹}(t)` |
|---|---|---|---|---|
| 341 | `vertex` | 1 | 1 | `−v` |
| 367 | `cherry` | 2 | 1 | `v² − c` |
| 368 | `broom₃` | 3 | 2 | `−v³ + 2vc − b'` |
| 369 | `mk [cherry]` | 3 | 1 | `−v³ + 2vc − m` |
| 370 | `bushy` | 4 | 6 | `v⁴ − 3v²c + 3vb' − B` |
| 371 | `mk [broom₃]` | 4 | 2 | `v⁴ − 3v²c + vb' + 2vm − M` |
| 372 | `mk [vertex, cherry]` | 4 | 1 | `v⁴ − 3v²c + c² + vb' + vm − V` |
| 378 | `mk [mk [cherry]]` | 4 | 1 | `v⁴ − 3v²c + c² + 2vm − M_mkMkCherry` |

Where (notation): `v = Φ_η(vertex)`, `c = Φ_η(cherry)`, `b' =
Φ_η(broom₃)`, `m = Φ_η(mk [cherry])`, `B = Φ_η(bushy)`, `M =
Φ_η(mk [broom₃])`, `V = Φ_η(mk [vertex, cherry])`, `M_mkMkCherry =
Φ_η(mk [mk [cherry]])`.

Add `σ(t)` values for completeness. Look up the values via the cycle
017 `RootedTree.symmetry` recursion in
`OpenMath/Chapter3/Section301.lean` or by inspecting each closed-form
proof's `_inv_mk` invocation in `Section422.lean`.

**§4. Structural patterns identified (the core analysis)**

Break the 8 trees into three families and identify the structural
recipe for each. The cycle 378 worker's D1 discovery is the seed:

**Family A — Single-child ladder** (chain of `mk` applications):
- `vertex, cherry = mk [vertex], mk [cherry], mk [mk [cherry]]`
- Closed forms: `−v`, `v² − c`, `−v³ + 2vc − m`, `v⁴ − 3v²c + c² + 2vm − mmc`
- Coefficient counts: 1, 2, 3, 5 (Fibonacci-shaped? — investigate)
- The dependency set is the chain of left-most descendants ONLY (no
  lateral coupling). This is the key cycle 378 D1 discovery.
- Propose a recursive shape: `inversePolynomial (mk [t]) f` depends
  only on `inversePolynomial s f` for `s` in the left-most-descendant
  chain of `t`.

**Family B — Symmetric leaf brooms** (`mk [vertex^k]`):
- `vertex, cherry = mk [vertex], broom₃ = mk [vertex, vertex],
  bushy = mk [vertex, vertex, vertex]`
- Closed forms have the binomial expansion `(−1)^k Σⱼ (k choose j)·v^(k−j)·wⱼ`
  where `w₀ = v, w₁ = c, w₂ = b', w₃ = bushy weight`
  (the cycle 368/370 Discovery, `(Aᵢ − v)^k` per-row factor structure).
- Propose a recursive shape: binomial sum over the broom family.

**Family C — Mixed / heterogeneous children**:
- `mk [broom₃]` (single non-leaf child), `mk [vertex, cherry]`
  (mixed leaf and non-leaf)
- Closed forms have terms not predicted by either Family A or
  Family B alone: cycle 371's `+ 2vm − M` cross-term, cycle 372's
  unique `c²` quadratic.
- The structural recipe is unclear from 2 data points; identify what
  additional data points (e.g. `mk [cherry, cherry]`, `mk [vertex,
  broom₃]`, `mk [bushy]`) would be needed.

**§5. Proposed recursive shape for `inversePolynomial`**

Sketch (cycle 379 worker fills in details based on §4 analysis):

```lean
-- Strawman: recurse over children, separating leaf children (= vertex)
-- from non-leaf children. The two cases use different recipes.
noncomputable def inversePolynomial : RootedTree → (RootedTree → ℝ) → ℝ
  | RootedTree.mk children => fun f =>
      -- Partition children into:
      --   leafCount := children.count vertex
      --   nonLeafChildren := children.filter (· ≠ vertex)
      -- Apply Family-B binomial sum over leaf count.
      -- Recurse on nonLeafChildren via Family-A or Family-C recipe.
      sorry  -- TODO: pin the recipe in cycle 380+
  termination_by t => t.order
  decreasing_by ...  -- via cycle 343's order_lt_of_mem_children
```

The cycle 379 worker should sketch AT LEAST 2 plausible recursive
variants and weigh their pros/cons (e.g. partition-based vs.
fold-over-children-based). Do NOT attempt to ship the definition;
this is Phase α'.1 (cycle 380+) scope.

**§6. Project-hook inventory (verified at HEAD)**

List the existing hooks the recursive `inversePolynomial` would
consume. Verify each by `grep -n` against
`OpenMath/Chapter4/Section422.lean` and
`OpenMath/Chapter3/Section301.lean`:

- `RootedTree.WellFoundedRelation := measure RootedTree.order` (cycle 343).
- `RootedTree.order_lt_of_mem_children` (cycle 343, in `Section301.lean`).
- 8 axiom-clean closed-form theorems (cycles 341, 367–372, 378) — list
  symbol names and line numbers.
- 8 axiom-clean m=0 Sub-lemma A corollaries — list symbol names.
- 8 Phase β bridges + 1 Phase β aggregator (8-way disjunction
  `elementaryWeightQ_phi_inv_eq_inversePolynomial_on_ladder`).
- Phase γ closed-subtree-agreement theorem
  `inversePolynomial_eq_of_subtree_agreement`.

**§7. Gap inventory — what's missing for Phase α'**

- A theory of "tree composition" or "tree substitution" that captures
  cross-family interactions (Family C non-trivial coefficients).
- A combinatorial formula for the coefficient of `Φ_η(s)` in
  `Φ_{η_q⁻¹}(t)` when `s` is a non-immediate-subtree of `t`. (Open;
  the 8 closed forms hint at some pattern but it's not yet clean.)
- Migration strategy for the 8 existing per-tree bridges: do they
  remain valid corollaries of the recursive shape, or do they need
  restatement? (Cycle 378 worker's Discovery suggests `rfl`-evaluation
  on small trees should match the closed forms; this is the
  acceptance criterion.)

**§8. Phase decomposition (multi-cycle)**

Outline 4 phases at 1–2 cycles each. Suggested:

- **Phase α'.1 (cycles 380–381)**: ship the recursive
  `inversePolynomial` definition + Phase α matching proofs for the
  8 existing trees (each should evaluate by `rfl` or `unfold + ring`).
  If the unified shape is hard, fall back to a partial recursive
  definition that handles Family A (single-child ladder) only and
  defers Families B/C.
- **Phase α'.2 (cycle 382)**: migrate Phase β bridges to consume the
  recursive form (mechanical port if α'.1 succeeds).
- **Phase α'.3 (cycle 383)**: extend Phase γ
  `inversePolynomial_eq_of_subtree_agreement` to all trees (the
  load-bearing step toward closing the cycle 365 sorry).
- **Phase α'.4 (cycle 384+)**: close `powRep_sum_eq_of_strict_subtree_agreement`
  via Phase β + extended Phase γ. This closes the cycle 365
  grandfathered sorry and unlocks Phase D.3.b parametricity Step 2.

**§9. Risk assessment**

Per-phase risk + rollback precedents (cycle 200/201 thm:381H,
cycle 149/150 def:530B). The Phase α' design risks:

- **R1 (HIGH)**: the recursive shape may not match all 8 closed
  forms by `rfl` or `unfold + ring`. Mitigation: design the shape
  to closely mirror the cycle 358 `_inv_mk` formula's structural
  unfolding, then verify each tree via calibration witnesses BEFORE
  shipping the recursive definition.
- **R2 (MEDIUM)**: Phase α'.3 (extending Phase γ to all trees)
  may need new combinatorial machinery. Mitigation: scope this
  separately in a follow-up cycle if Phase α'.1/α'.2 reveal it
  as load-bearing.
- **R3 (MEDIUM)**: the 8-tree-ladder Phase β bridges may not all
  remain `rfl`-equal under the recursive form. Mitigation: be
  prepared to restate them as `unfold + ring` proofs.
- **R4 (LOW)**: well-founded recursion termination proof may need
  explicit `decreasing_by` annotations. Mitigation: cycle 343's
  `WellFoundedRelation` instance should make this automatic.

**§10. Cycle 380 entry point**

Concrete first task for cycle 380:
1. Read the cycle 358 `elementaryWeightQ_phi_inv_mk` proof body
   at `Section422.lean:582` (the structural recursion seed).
2. Read each of the 8 closed-form proofs to identify the recursive
   pattern.
3. Ship Phase α'.1 (recursive `inversePolynomial`) per §8 above.
4. Verify all 8 calibration witnesses pass.

If Phase α'.1's recursive shape isn't immediately clear from
inspecting the closed-form proofs, cycle 380 may need to ship a
partial recursive definition (e.g., for Family A only) with a
fallback to the cycle 374 pattern-match form for Family B/C trees.
This split-shipping pattern matches cycle 358's α.1/α.2/α.3
sub-phase precedent.

**§11. Self-reference & cross-links**

- `.prover-state/issues/def_422B_subLemmaA_inductive_plan.md`
  (cycle 373 — predecessor scoping doc; Phase α/β/γ/δ structure).
- `.prover-state/issues/def_422B_phase_D_3_scoping.md` (cycle 357
  — Phase D.3 sub-phases, including the cycle 363 audit and cycle
  365 split into Sub-lemma A/B).
- `.prover-state/issues/def_422B_path.md` (cycle 336 — overall
  `def:422B` roadmap).
- `extraction/raw_text/ch04.txt:1148–1173` — Butcher §422 textbook
  source.
- `OpenMath/Chapter4/Section422.lean` — file under analysis (1
  grandfathered sorry at line 2279).

## Priority 2 — Optional Lean ship (only if Priority 1 finishes early)

If the scoping doc lands in <2 hours with all 11 sections complete,
ship ONE small calibration witness as Lean evidence:

- **Candidate**: a paper-derived predicted value for `Φ_{η_q⁻¹}` on
  a 9th tree NOT in the current ladder, expected to follow the
  Family A single-child ladder pattern. E.g. `mk [mk [mk [cherry]]]`
  (depth-4 single-child ladder).
- **Format**: an inline comment in the scoping doc giving the
  paper-predicted closed form. Do NOT ship as a Lean theorem (that
  would extend the ladder, which is explicitly forbidden below).

This is strictly OPTIONAL. The scoping doc itself is the primary
deliverable.

## Things to AVOID this cycle

- **DO NOT extend the 8-tree ladder** to a 9th matched tree in
  `inversePolynomial`. The cycle 378 worker explicitly recommends
  against this; further ladder rungs are treadmill work with
  diminishing returns. The scoping doc replaces the treadmill.

- **DO NOT attempt the Phase α' recursive `inversePolynomial`
  definition this cycle.** That's a multi-cycle deliverable (Phase
  α'.1 in cycles 380+) and was explicitly anticipated by the cycle
  378 worker's suggested next approach.

- **DO NOT touch the cycle 365 grandfathered sorry** at
  `Section422.lean:2279`. It remains in place until Phase α'.4 is
  shipped (cycle 384+ per the scoping doc).

- **DO NOT attempt Phase δ** (general-`m` Sub-lemma A) on the
  8-tree ladder. Per cycle 366's heterogeneity analysis (in
  `def_422B_phase_D_3_scoping.md` §6 cycle 366 update), this is
  blocked on cross-side comparison of heterogeneous `powRep`-sums,
  which requires the Phase α' machinery as a prerequisite.

- **DO NOT pivot to a fresh entity** (e.g. `thm:535A`, `def:442A`,
  `thm:541A`). The cycle 378 task results note the 8-tree ladder
  closure is a natural strategic checkpoint, but the explicit
  recommendation is to invest one more cycle in scoping rather than
  to pivot mid-stream. After Phase α' lands (~5 cycles), the
  planner can re-evaluate the pivot.

- **DO NOT submit anything to Aristotle** this cycle. The
  deliverable is markdown-only; no proof obligations to delegate.
  Cycle 378 worker correctly noted that Aristotle's free compute is
  better reserved for the cycle 365 grandfathered sorry (Phase α'.4
  scope).

- **DO NOT update `lean_status.json` or `plan.md`** beyond cycle
  log entries. `def:422B` remains `partial`; this scoping cycle does
  not advance the formalization status.

- **DO NOT introduce sorries.** Markdown-only; sorry count must
  remain at 1 (the cycle 365 grandfathered sorry, unchanged).

- **DO NOT raise `maxHeartbeats`** — no Lean compilation in this
  cycle.

- **DO NOT modify `scripts/autonomous_loop.py`** or any other
  loop-infrastructure files.

## Verification checklist before commit

1. Scoping doc exists at the prescribed path and has all 11 sections.
2. All cited file paths and line numbers verified by `grep -n` /
   inspection (in particular the §6 project-hook inventory and the
   §3 σ(t) values).
3. The 8-tree catalog table is complete and matches the
   `Section422.lean` closed forms verbatim.
4. The cycle-373 precedent reference is explicit (markdown-only,
   no Lean churn, ~600+ lines).
5. `lake env lean OpenMath/Chapter4/Section422.lean` is NOT run
   this cycle (doc-only). If incidentally run, must exit 0.
6. `grep -c sorry OpenMath/Chapter4/Section422.lean` returns 5
   (unchanged from cycle 378).
7. Standard cycle bookkeeping: task results
   `.prover-state/task_results/cycle_379.md`, heartbeat update,
   history.jsonl row, attempts.md trim if needed.

## Why this strategy

- **Cycle 378 worker's explicit recommendation**: their task results
  §"Suggested next approach" Option A names a Phase α' scoping doc
  as the highest-value next move.
- **Precedent**: cycle 373 shipped a similar scoping doc
  (`def_422B_subLemmaA_inductive_plan.md`) which directly informed
  cycles 374–378's 8-tree ladder work. The doc was scored OK
  despite being markdown-only.
- **Strategic value**: 8 closed-form data points span all three
  observed structural patterns (single-child ladder, multi-leaf
  symmetric, heterogeneous children). The cycle 378 D1 discovery
  about single-child ladders is genuinely actionable.
- **Risk profile**: pure scoping doc has near-zero rollback risk
  (no Lean state changes, no axioms added, no `lean_status.json`
  mutations). The downside is one cycle of "no Lean ship", which
  is acceptable when followed by 3–5 cycles of focused Phase α'
  implementation.
- **Alternative considered**: extending to a 9th tree (cycle 378
  Option B). Rejected because the cycle 378 worker explicitly
  notes "probably less valuable than Option A's scoping."

## Sub-deliverable summary

Primary deliverable this cycle: one markdown file at
`.prover-state/issues/def_422B_phase_alpha_prime_scoping.md`,
~600–900 lines, 11 sections (§1–§11), informed by the cycle 373
template. No Lean changes; standard cycle bookkeeping (task results
+ heartbeat + history) only.
