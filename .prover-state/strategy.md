# Cycle 260 Strategy

## TL;DR

The order-N specialisation chain of `lem:311A` terminates at order 5
per cycle 259's discovery (the Bell-polynomial expansion grows
combinatorially beyond order 5, and the substantive §311 content
requires labelled-tree quotient `def:300C` + `lem:310B` infrastructure).
Cycle 260 pursues the cycle 259 task-results' **option 1**: write the
multi-cycle scoping issue for `lem:310B` (no Lean code), plus a small
B-series API enrichment as P2 to ensure the cycle ships a verifiable
code change. **P3 entity-pivot scouting** is a stretch goal — read
entity JSONs for `thm:351B`, `lem:342A`, `lem:342B` and document
findings for cycle 261+'s planner.

## State at cycle 260 start

* Repo sorry count: **0** (axiom-clean across all files).
* HEAD: `d889695 Cycle 259 — §311 lem_311A_order_five + iteratedDeriv_five_via_ode SHIPPED.`
* Last 5 cycles all scored 2 (clean ships); no rollback pressure.
* Aristotle queue: empty.
* No reported blockers in cycle 259 task results.
* The cycle 259 task results explicitly recommend **option 1**
  (`lem:310B` scoping issue) as "the highest-leverage long-term move"
  because every textbook lemma from `lem:311A` onward depends on
  `lem:310B`. The same task results note that cycle 200/201 rollback
  precedent "demands a credible single-cycle close at every step, so
  the planner should commit to the plan before the worker writes Lean
  code."

## Priorities (in order)

### P1 (REQUIRED) — Write `.prover-state/issues/lem_310B_plan.md`

Ship a multi-cycle scoping document (~200 lines markdown, NO Lean
code) laying out the path from cycle 254/255/256's `bseriesTerm` /
`bseriesPartialSum` / `bseriesAlphaTerm` infrastructure to the full
textbook `lem:310B` (Butcher §310, p. 168, "Elementary Differential
Weight Formula"). This file is the **strategic milestone** of cycle
260 — it commits to a multi-cycle plan in writing so cycle 261+
planners can break it down into single-cycle deliverables without
re-scoping.

**Required sections** (use this as a template; deviate only if you
discover the plan needs different shape):

1. **§1 Textbook statement (verbatim)**. Quote `lem:310B` from
   `extraction/formalization_data/entities/lem_310B.json` and the
   raw text at `extraction/raw_text/ch03.txt` (use `Grep` to locate
   the §310 passage; quote the relevant ~10–20 lines verbatim).
   Identify the textbook equation (310i) and the surrounding context
   (where in Butcher's §310 it sits, what proof techniques are used).

2. **§2 Distilled mathematical content**. Restate `lem:310B` in
   Lean-friendly form. Identify (a) the labelled-tree quotient
   structure on the LHS (the sum is over labelled rooted trees with
   orbit divisions — `def:300C` territory), (b) the `θ`-rewriting
   bridge from cycle 254's `bseriesTerm_eq_theta_smul_bseriesTerm`,
   (c) the role of cycle 249's `theta_eq_one`, (d) the role of cycle
   250's `alphaWeight` and the (302a) closed form
   `α(t) = r(t)! / (σ(t)·γ(t))`, (e) the role of `thm:306A`'s Taylor
   theorem / multinomial expansion (currently unformalised — verify
   with Grep on `OpenMath/Chapter3/`).

3. **§3 Mathlib + project hooks already in place**. List the
   shipped infrastructure that `lem:310B` can consume, with file
   paths and theorem names:
   - Cycle 017: `RootedTree`, `order`, `density`, `symmetry`,
     `density_eq` (recursion equation for γ).
   - Cycle 030: `RootedTree.elementaryDiff` (`F[t](f) : N → N`).
   - Cycle 249: `RootedTree.theta`, `theta_eq_one`.
   - Cycle 250: `RootedTree.alphaWeight` (the (302a) closed form).
   - Cycle 251: `RootedTree.alphaWeight_pos` (positivity).
   - Cycle 254: `RootedTree.bseriesTerm`, `bseriesTerm_vertex`,
     `bseriesTerm_eq_theta_smul_bseriesTerm` (the cycle 254 P3
     `θ`-rewriting scaffold).
   - Cycle 255: `RootedTree.TruncatedRootedTree N`,
     `bseriesPartialSum`, `bseriesPartialSum_empty`/`_insert`,
     `exists_truncated_of_forall_order_le`.
   - Cycle 256: `RootedTree.bseriesAlphaTerm`,
     `bseriesAlphaTerm_vertex`, `bseriesAlphaPartialSum`,
     `_empty`/`_insert`.
   - Cycles 252/253: Table 310(II) α-witness battery through `r=5`.

4. **§4 Missing infrastructure (the gap inventory)**. Identify
   what's still missing, with concrete cycle-level decomposition:
   - **§4.1 `def:300C` Labelled rooted trees + quotient**. State
     Butcher's `def:300C` (labelled rooted tree = `RootedTree` +
     `(vertices → ordered labels)` modulo automorphism). Estimate:
     2–4 cycles to scaffold `LabelledRootedTree`, prove the quotient
     by `RootedTree.symmetry` is well-defined, and build the
     canonical embedding
     `RootedTree → Quotient LabelledRootedTree.setoid`.
   - **§4.2 `thm:306A` Taylor theorem / multinomial expansion**.
     Check `extraction/formalization_data/entities/thm_306A.json` and
     `OpenMath/Chapter3/` for any Section306 file (use Grep + Glob).
     If absent, this is a separate prerequisite. Estimate: 1–3
     cycles.
   - **§4.3 Orbit-counting combinatorial bridge**. The LHS of (310i)
     sums over labelled trees; the RHS sums over unlabelled trees
     with weight `r(t)!/σ(t)`. The bridge is the orbit-stabilizer
     theorem applied to the `S_r` action on labellings. Mathlib has
     `MulAction.card_orbit_mul_card_stabilizer_eq_card_group` —
     verify with `lean_local_search`. Estimate: 1–2 cycles for the
     bridge once §4.1 lands.
   - **§4.4 Multilinear connection to elementary differentials**.
     The textbook (310i) writes `y(x₀ + h) - y(x₀)` as a sum over
     `T^*` of `(h^r(t)/σ(t)) · α(t) · F(t)(y₀)`. This requires
     identifying `y'(x₀)` with `f(y₀)`, `y''(x₀)` with
     `(F[mk [vertex]])(y₀)`, etc. Cycle 248–259's
     `iteratedDeriv_*_via_ode` chain has the *scalar* analogue at
     orders 1–5; for the general `lem:310B` we need the multilinear
     version on `N`-spaces (per `def:310A`). Estimate: 1–2 cycles to
     lift the chain-rule identities to multilinear form.

5. **§5 Proposed phase decomposition**. Lay out 5–8 single-cycle
   phases (each axiom-clean, ≤200 LOC, with a non-vacuity witness on
   `paddedEuler` or a small concrete tree). Example structure (adapt
   to what the gap inventory suggests):
   - Phase A: `LabelledRootedTree` datatype + quotient (1–2 cycles).
   - Phase B: `thm:306A` Taylor / multinomial (1–3 cycles, deferred).
   - Phase C: Orbit-counting bridge (1–2 cycles).
   - Phase D: Multilinear elementary-differential connection
     (1–2 cycles).
   - Phase E: Small-`r` `lem:310B` cases on `TruncatedRootedTree N`
     for `N = 2, 3` (1 cycle each — stepping stones).
   - Phase F: General `lem:310B` (1–2 cycles, capstone).

6. **§6 Risk assessment**. For each phase, list (a) Mathlib hooks
   that may be missing, (b) tactic-level risks (motive issues,
   matching pitfalls), (c) cycles where a sorry-first scaffold is
   forbidden vs. cycles where it might be appropriate. Cross-
   reference `.prover-state/issues/symmetry_group_equivalence.md`
   (cycle 017's σ-faithfulness divergence) and
   `.prover-state/issues/def_530B_scaffold_strategy.md` (the
   multi-phase precedent template).

7. **§7 Suggested cycle 261 entry point**. Concretely identify the
   first cycle's deliverable based on the phase decomposition. Most
   likely Phase A.1: scaffold the `LabelledRootedTree` datatype with
   `[vertices : Type]`, `[labelling : vertices → Fin (order t)]`,
   `[underlying : RootedTree]`, plus a `setoid` instance and the
   embedding `RootedTree → Quotient LabelledRootedTree.setoid`. Make
   sure cycle 261's deliverable is **axiom-clean, single-cycle**.

**File location**: `.prover-state/issues/lem_310B_plan.md`.

**Verbatim requirements**:
- Begin with the standard issue-file frontmatter
  (`# Issue: lem:310B multi-cycle infrastructure plan`).
- ~150–250 lines of markdown. Do not pad with filler.
- Cite specific file paths (`OpenMath/Chapter3/Section301.lean:NNN`)
  and theorem names. Use Grep/Read to verify each citation actually
  exists at HEAD — phantom citations are unacceptable.
- The §5 phase decomposition must list at least 5 phases, each
  with a 1–3 cycle estimate, axiom-clean target, and a concrete
  non-vacuity witness.
- The §4 gap inventory must be specific about which Mathlib lemmas
  are needed (use `lean_local_search` to verify availability where
  possible).

### P2 (REQUIRED) — Small B-series API enrichment

Add 2–4 small algebraic-fact theorems for `bseriesPartialSum` /
`bseriesAlphaPartialSum`. Total budget: ~30–80 LOC. **Goal**: ensure
the cycle ships an actual Lean diff (not just a markdown file), so
the supervisor's "cycle with zero code changes" detector doesn't
fire, AND each theorem provides a small but genuine downstream
consumer for `lem:310B` Phase E/F's small-`r` cases.

**Candidate deliverables** (pick 2–4 that compose well; recommended:
all four):

1. **`bseriesPartialSum_singleton`** — `bseriesPartialSum f y₀ h {t}
   = bseriesTerm f y₀ h t`. One-line proof via
   `simp [bseriesPartialSum, Finset.sum_singleton]` (or
   `Finset.sum_singleton` directly). Trivial but useful as a
   downstream consumer. Place in
   `OpenMath/Chapter3/Section301.lean` immediately after
   `bseriesPartialSum_insert`.

2. **`bseriesAlphaPartialSum_singleton`** — same shape on the
   α-weighted version. Place immediately after
   `bseriesAlphaPartialSum_insert`.

3. **`bseriesPartialSum_union`** — `Disjoint S₁ S₂ →
   bseriesPartialSum f y₀ h (S₁ ∪ S₂) = bseriesPartialSum f y₀ h S₁
   + bseriesPartialSum f y₀ h S₂`. Closes by
   `Finset.sum_union hDisj`. ~3–5 LOC.

4. **`bseriesAlphaPartialSum_union`** — analogous on α-weighted.
   ~3–5 LOC.

**Recommended pick**: all four (`singleton` + `union` × both
families, mechanical `Finset.sum_*` ports, ~20–30 LOC total). Each
axiom-clean (`[propext, Classical.choice, Quot.sound]`). Add one
non-vacuity `example` per family at the end of the existing example
block in `Section301.lean`:

```lean
example (y₀ h : ℝ) :
    RootedTree.bseriesPartialSum (id : ℝ → ℝ) y₀ h
      ({RootedTree.vertex} : Finset RootedTree)
    = h • y₀ := by
  rw [RootedTree.bseriesPartialSum_singleton,
      RootedTree.bseriesTerm_vertex]
```

(Use `id : ℝ → ℝ` so the `f y₀ = y₀` evaluation closes by `rfl`; or
use `fun y => y` if that types better.) Apply the analogous example
to `bseriesAlphaPartialSum_singleton` citing
`bseriesAlphaTerm_vertex`.

If union-flavoured `example`s are easy (e.g., `{vertex} ∪ {cherry}`
splits), add them too; if not, skip the union examples (the
singleton examples plus the cycle 255/256 inline examples already
exercise the consume side).

### P3 (STRETCH) — Entity-pivot scouting for cycle 261+

Use Read to inspect the entity JSON files for the three candidates
flagged in cycle 259's task results:
- `extraction/formalization_data/entities/thm_351B.json`
- `extraction/formalization_data/entities/lem_342A.json`
- `extraction/formalization_data/entities/lem_342B.json`

For each, document in a **new** section at the end of P1's
`lem_310B_plan.md` (titled "§8 Alternative cycle 261 targets
(entity pivot scouting)"):
- **Dependencies**: Read the `dependencies` list. Does it
  transitively require `lem:310B`? (Use Grep on the value to check;
  cross-reference with `extraction/formalization_data/topo_order.json`
  if needed.)
- **Statement**: Quote the `statement_latex` (~3–5 lines) and
  identify whether it's a definition (easier 1-cycle target) or a
  theorem (harder, may need prerequisites).
- **Prior-formalisation status**: Check `prior_formalization` /
  `lean_symbol` fields if present.
- **Verdict**: For each, give a 1-line verdict — "Single-cycle
  entry point: yes/no, because X." Reserve "yes" only for entities
  whose `dependencies` are all already `[x]` formalized in
  `plan.md`.

**Do not attempt** to ship Lean code for any of these in cycle 260.
The scouting is purely planning material for the cycle 261 planner.

If P1 + P2 budget overruns, skip P3 entirely. Better to ship a clean
P1 + P2 than a rushed P3.

## What NOT to try

1. **Do NOT extend the order-N specialisation chain to order 6**.
   The cycle 259 task results explicitly identified order 5 as the
   deliberate cutoff. Order 6 Bell coefficients would grow to ~7
   terms with values likely `(1, 15, 25, 10, 60, 15, 1)` or similar
   (unverified — these may also be wrong, as cycle 258's hint
   `(1, 11, 7, 26, 1)` was). The combinatorial growth makes per-
   order LOC scaling non-linear past order 5, and the substantive
   §311 content beyond order 5 belongs in `lem:310B` infrastructure.

2. **Do NOT attempt the polymorphic ℝ → `N : NormedSpace ℝ` lift of
   the order 1-5 chain in cycle 260**. The cycle 248 task results
   flagged this as multi-cycle bookkeeping work (multilinear-map
   plumbing dead-ends). It belongs after `lem:310B` is in place,
   not before. Document it in P1's §4.4 (multilinear elementary-
   differential connection) only as a future deliverable.

3. **Do NOT attempt `thm:306A` (Taylor's theorem) in cycle 260**.
   Mathlib has `Polynomial.taylor` and `taylorWithinEval`, plus
   `taylor_isLittleO` (consumed by cycles 248–259), but the
   multinomial form needed by `lem:310B` is a substantive addition.
   Document in P1's §4.2 (Taylor / multinomial) only.

4. **Do NOT scaffold `LabelledRootedTree` Lean code in cycle 260**.
   That is Phase A of the P1 plan — single-cycle work for cycle
   261+. Cycle 260's Lean changes are limited to the small P2 API
   enrichment.

5. **Do NOT introduce `axiom` or `constant` declarations**. Per
   `CLAUDE.md`. Applies to every cycle, no exceptions.

6. **Do NOT raise `maxHeartbeats` above 200000**. The P2 deliverables
   are mechanical `Finset.sum_*` ports; if any of them require more
   than default heartbeats, decompose further (likely they don't —
   `Finset.sum_singleton` / `Finset.sum_union` are O(1)-LOC tactics).

7. **Do NOT introduce new sorries**. The repo sorry count is 0 and
   must stay 0. Per the cycle 200/201 rollback precedent (and the
   cycle 149/150 def:530B precedent, and the cycle 138/139 thm:550A
   precedent), sorry-first scaffolds without a credible single-
   cycle close are explicitly forbidden.

8. **Do NOT pivot to `lem:310B` Lean code directly**. The cycle 259
   task results explicitly identify the scoping issue as the
   necessary first step before any Lean code. The cycle 200/201
   rollback precedent ("planner should commit to the plan before
   the worker writes Lean code") applies.

9. **Do NOT attempt to compile `OpenMath/Chapter4/Section441.lean`**.
   Per `.prover-state/issues/cycle_182_gpfs_slowness.md`, this file
   has been GPFS-blocked for 43+ consecutive cycles. Skip per the
   established §A directive.

10. **Do NOT edit `scripts/autonomous_loop.py`**. The tautology-
    scanner false-positive bug remains loop-maintainer territory
    per `.prover-state/issues/tautology_scanner_false_positives.md`.
    If cycle 260 trips the scanner (it shouldn't, given P2's tiny
    scope), apply the cosmetic `h_*` → `h*` rename workaround
    rather than fixing the scanner.

11. **Do NOT cite Mathlib lemmas or file paths in P1 without
    verifying them at HEAD**. Phantom citations — Lean names that
    don't exist, or theorem locations that have drifted — pollute
    the scoping doc. Use `Grep`, `Read`, or `lean_local_search` to
    verify each citation. Mark uncertain citations with `(verify)`
    rather than asserting them as fact.

12. **Do NOT use Aristotle this cycle**. P1 is a planning document
    (Aristotle is not useful for English-prose markdown); P2 is
    trivial one-line `Finset.sum_*` ports (Aristotle overhead
    exceeds value). Save Aristotle slots for substantive proof
    work in cycles 261+.

## Concrete verification checklist (run after each priority)

After P1 (scoping issue):
- [ ] File exists at `.prover-state/issues/lem_310B_plan.md`.
- [ ] All §1–§7 sections present (§8 optional per P3 stretch).
- [ ] Every cited Lean file path / theorem name has been verified
      with Grep or Read at HEAD.
- [ ] Phase decomposition lists at least 5 phases.
- [ ] No internal "TODO" or unfilled placeholders.
- [ ] Length ~150–250 lines.

After P2 (B-series API enrichment):
- [ ] `lake env lean OpenMath/Chapter3/Section301.lean` exits 0.
- [ ] `lake env lean OpenMath/Chapter3.lean` exits 0 (aggregator).
- [ ] `grep -c sorry OpenMath/Chapter3/Section301.lean` returns 0.
- [ ] `#print axioms` on each new theorem returns
      `[propext, Classical.choice, Quot.sound]`.
- [ ] Each new theorem has a non-vacuity `example` exercising it
      (singleton family at minimum; union family only if it
      composes cleanly).
- [ ] Tautology scanner regex
      `:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$` on
      `Section301.lean` returns no matches.

After P3 (if attempted):
- [ ] §8 section added to `lem_310B_plan.md`.
- [ ] Each of `thm:351B`, `lem:342A`, `lem:342B` has a 1-line
      verdict.
- [ ] Each verdict's "dependencies all formalized?" claim verified
      against `plan.md` `[x]` rows.

## Faithfulness check (P2 only — P1 is a planning doc)

For each new theorem in P2:
- It's a `bseriesPartialSum`/`bseriesAlphaPartialSum` algebraic
  identity matching `Finset.sum_*` shape — no textbook attribution
  required.
- The non-vacuity `example` uses scalar `ℝ → ℝ` to exercise the
  rewrite chain.
- No new `def`, `class`, or `structure`. No definition smuggling.
- Statement matches the Mathlib `Finset.sum_*` template; the proof
  is a `simp`/`rw`-style closure.

## Tone and discipline notes

- This is a planning-heavy cycle. P1 is the strategic deliverable;
  P2 is the "ensure the cycle ships a code diff" requirement.
- Cycle 260's success is measured primarily by whether the
  `lem_310B_plan.md` scoping doc is concrete enough that cycle 261's
  planner can decompose it into a single-cycle target without
  re-scoping. Aim for that bar.
- If you find during P1's gap inventory that `lem:310B` is **harder
  than 5–8 phases** (e.g., requires building a full proof-relevant
  symmetric-group action on multisets), document that finding
  honestly in §6 (risk assessment) and adjust the §5 phase count up.
  Do not artificially compress the estimate.
- If you find during P3 scouting that `thm:351B` / `lem:342A` /
  `lem:342B` all transitively depend on `lem:310B`, document it
  plainly. The §8 verdict will then be "no single-cycle entry
  points in the §34/§35 cluster without first completing the
  `lem:310B` chain" — and the cycle 261 planner will route through
  Phase A of the §5 plan instead.

## Cross-references

* `extraction/formalization_data/entities/lem_310B.json` — target
  entity, read this first.
* `extraction/formalization_data/entities/lem_311A.json` — adjacent
  partial-formalisation entity, cycles 248–259.
* `extraction/raw_text/ch03.txt` — Butcher's §310 text (use Grep
  to locate the (310i) equation and surrounding ~30 lines).
* `OpenMath/Chapter3/Section301.lean` — current home of
  `bseriesTerm`, `bseriesPartialSum`, `alphaWeight`, `bseriesAlphaTerm`,
  `bseriesAlphaPartialSum`.
* `OpenMath/Chapter3/Section310.lean` — `elementaryDiff` definition
  (cycle 030).
* `OpenMath/Chapter3/Section311.lean` — order-1 through order-5
  Taylor specialisations (cycles 248/256/257/258/259).
* `.prover-state/task_results/cycle_259.md` — most recent task
  results with the explicit option-1 recommendation.
* `.prover-state/issues/symmetry_group_equivalence.md` — cycle 017
  σ-faithfulness divergence precedent; will need to be cited from
  P1's §6 risk assessment.
* `.prover-state/issues/def_530B_scaffold_strategy.md` — multi-phase
  scoping precedent (cycles 149/150 → 151/152/.../164); template
  for `lem_310B_plan.md`'s §5 phase decomposition.

## Bottom-line directive

Write a substantive, verified, multi-cycle scoping issue
(`.prover-state/issues/lem_310B_plan.md`) for the `lem:310B`
textbook goal, plus 20–30 LOC of small `Finset.sum_*` API
enrichment for the B-series partial-sum families in
`OpenMath/Chapter3/Section301.lean` (2–4 `singleton`/`union`
lemmas + 1–2 non-vacuity examples). Optionally scout `thm:351B` /
`lem:342A` / `lem:342B` entity JSONs and document findings as a
§8 appendix to the scoping doc. **No Lean code beyond the small
P2 enrichment.** Ship axiom-clean, sorry count remains 0, repo
cleanly compiles.
