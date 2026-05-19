# Cycle 402 Strategy

## §A. Status snapshot (post-cycle 401)

* Phase α'.4 of `def:422B` is **fully closed**. All 9 ladder trees
  (`vertex`, `cherry`, `broom₃`, `mk [cherry]`, `bushy`, `mk [broom₃]`,
  `mk [vertex, cherry]`, `mk [mk [cherry]]`, plus `mk [cherry, cherry]`
  via cycle 388 calibration) route uniformly through `inversePolyTree`.
* §422 axiom-clean streak: **63 substantive + 3 doc** cycles (336–401).
* Section422.lean: 8178 LOC, sorry count 5 (4 docstring + **1
  grandfathered cycle 365 code sorry at line 2279** — Sub-lemma A
  body `powRep_sum_eq_of_strict_subtree_agreement`).
* Build cost has risen sharply: warm rebuild of `OpenMath.Chapter4.Section422`
  measured 1165s in cycle 401 (cycle 399 Discovery: `inversePolyTree`'s
  5-arm match generates equation-compiler unfolding lemmas that scale
  with arm count; expect ≥1200s warm rebuilds going forward).

## §B. No Aristotle results pending.

Skip Aristotle integration step. There are no in-flight Aristotle
projects to poll this cycle.

## §C. Cycle 402 deliverable — Phase α'.5 scoping doc (markdown-only)

**Ship a single new markdown file**:
`.prover-state/issues/def_422B_phase_alpha_prime_5_scoping.md`.

This is a deliberate continuation of the cycle 385 / cycle 398
scoping-doc precedent: markdown-only cycle, no Lean edits, no axiom
risk. It directly enables cycles 403+ to execute Phase α'.5 work
(generalising `inversePolyTree` to `k ≥ 3` heterogeneous children)
without re-scoping.

### §C.1 Why a scoping doc, and why now

The cycle 401 worker explicitly enumerated three options for cycle
402 (see `task_results/cycle_401.md` §"Suggested next approach"):

1. Phase α'.5 scoping doc (k ≥ 3 heterogeneous children)
2. Phase β/γ extension scoping doc (cycle 365 sorry closure)
3. Pivot to a fresh entity

The pivot option (#3) was investigated this cycle and declined for
two reasons: (a) `def:442A` — the most-adjacent Ch.4 §441 candidate
— requires Riemann-surface / order-star infrastructure that Mathlib
lacks (verified by reading the entity JSON; `rouche_theorem_missing.md`
documents the parallel gap). (b) `lem:351A` — a self-contained RK
stability-function identity — would require introducing a new RK
`R(z) = 1 + zbᵀ(I − zA)⁻¹1` definition plus the rank-1-determinant
algebra and is plausibly single-cycle but carries setup risk that a
scoping doc avoids.

Option #2 (cycle 365 sorry closure) was explicitly deferred by the
cycle 401 worker: "should be deferred to mid-cycle 402+, after the
planner has chosen between Options 1 and 3." That instruction stands.

**Option #1 is the cleanest cycle 402 ship**:

* Direct continuation of the productive §422 work track.
* Markdown-only — zero Lean changes, zero axiom risk, no build-cost hit.
* Follows the cycle 385 (Family C scoping, drove cycles 386–397) and
  cycle 398 (Phase α'.4.3 bushy scoping, drove cycles 399–401)
  precedents — each markdown scoping cycle precedes 11–12 cycles of
  substantive ship.
* Sets up cycle 403+ for concrete Phase α'.5.0 / α'.5.1 / α'.5.2
  ladder ships, mirroring the cycle 386–401 cadence.

### §C.2 Scope of the new scoping doc

The doc must follow the cycle 385 / cycle 398 template — see
`.prover-state/issues/def_422B_phase_alpha_prime_family_C_scoping.md`
(cycle 385, 800+ lines, 11 sections + post-cycle update appendices)
and `.prover-state/issues/def_422B_phase_alpha_prime_family_bushy_scoping.md`
(cycle 398, 700+ lines, 10 sections + post-cycle update appendices).

**Required sections (target 400–700 lines)**:

* **§1 Status & blocker** — Phase α'.4 closure baseline. State
  precisely what `inversePolyTree`'s current 5-arm match handles
  (`[]`, `[c]`, `[c₁, c₂]`, `[c₁, c₂, c₃]`, catch-all) and what's
  missing: the catch-all `(_::_::_::_::_)` returns `0` for `k ≥ 4`,
  which is mathematically incorrect for arbitrary heterogeneous
  trees of arity ≥ 4. Also note that the `[c₁, c₂, c₃]` arm only
  handles the `(vertex, vertex, vertex)` triple correctly via
  cycle 399's hard-coded `trichildCrossTerm` branch; arbitrary
  k = 3 triples (e.g. `(vertex, vertex, cherry)`,
  `(cherry, cherry, cherry)`) currently return wrong values.
* **§2 Block decomposition for k ≥ 3 children** — Mirror cycle 398
  §3's two-child block analysis. For arity-k children, cycle 358's
  `_inv_mk` unfolds the per-row product into `2^k` blocks indexed by
  `{const, A-sum}^k` selections at each child. Catalogue these for
  k = 3 (8 blocks) and k = 4 (16 blocks). Bushy at k = 3 is the
  symmetric all-`(const, const, const)`-plus-permutations special
  case; asymmetric triples mix const and A-sum selections per child.
* **§3 Empirical data points** — Currently the **only** k = 3
  empirical evidence is cycle 370's `elementaryWeightQ_phi_inv_bushy`
  (three identical leaf children). For Phase α'.5 we need
  empirical data on **non-symmetric** k = 3 trees. The first
  natural target is `mk [vertex, vertex, cherry]` (order 5, two
  leaves + one cherry), which has not been computed yet. Catalog
  what closed-form kernels are expected to appear (`v`, `c`,
  `f(mk [vertex, vertex, cherry])`-self-term, plus likely
  `v · f(mk [vertex, cherry])` or `c · f(cherry)` cross-terms
  from the §2 block decomposition).
* **§4 Conjectured `trichildPolynomial` extension** — Cycle 399's
  current `trichildPolynomial` and `trichildCrossTerm` are
  hard-coded for the `(vertex, vertex, vertex)` triple. Sketch the
  generalisation: a per-triple dispatch analogous to cycle 387's
  `bichildCrossTerm` (which now handles 3 binary pairs:
  `(cherry, cherry)`, `(broom₃, cherry)`, `(vertex, cherry)`).
  Pin the §2 block-decomposition structure as the source of truth
  for the cross-term polynomial shape. List 3–4 specific triples
  that should be reached (e.g. `(vertex, vertex, cherry)`,
  `(vertex, cherry, cherry)`, `(cherry, cherry, cherry)`) and
  note each is a separate empirical+migration ship.
* **§5 Conjectured `tetrachildPolynomial` for k = 4** — Sketch the
  k = 4 helper. The k = 4 case has 16 blocks per §2; the bilinear
  / trilinear / quadrilinear cross-term decomposition needs a
  general framework, possibly via a `nchildPolynomial` parametric-
  in-`k` recursive helper. **Flag this as multi-cycle** with no
  immediate ship target; the goal is to scope the work, not start it.
* **§6 Phase decomposition** — Decompose Phase α'.5 into
  sub-phases analogous to Phase α'.4's α'.4.0 / α'.4.1 / α'.4.2:
  * α'.5.0 = ship empirical witnesses for one or two non-symmetric
    k = 3 trees (cycle 403, ~250 LOC).
  * α'.5.1 = extend `trichildPolynomial` / `trichildCrossTerm` dispatch
    to handle non-`(vertex, vertex, vertex)` triples (cycle 404+,
    multi-cycle).
  * α'.5.2 = `inversePolynomial` body migration for any newly-handled
    k = 3 trees (if needed for downstream).
  * α'.5.3 (deferred) = k = 4 infrastructure (`tetrachildPolynomial`,
    catch-all bump to `(_::_::_::_::_::_)`).
* **§7 Risk inventory** — Build cost: cycle 399 Discovery and
  cycle 401 ship both note elevated rebuild times (~1165s in cycle
  401). k = 4 work will further inflate this. Flag the
  elaboration-time risk explicitly so cycle 403+ workers budget
  appropriately. Also flag that the cycle 365 grandfathered sorry
  remains the primary §422 closure target — Phase α'.5 work makes
  it structurally closer to attackable but does not itself close it.
* **§8 Cycle 403 entry point** — Concrete recommendation: ship
  `elementaryWeightQ_phi_inv_mkVertexVertexCherry` as the 10th
  data point in the cycle 366 §G Route B hypothesis ladder
  (currently 9 trees catalogued through cycle 388 / 401). Use the
  cycle 372 `mk [vertex, cherry]` template scaled to three
  children. Estimated ~250 LOC. Document the specific proof recipe
  pattern (cycle 358 `_inv_mk` unfold → per-child product expansion
  → cycle 387/388 helper reuse → `ring` close).
* **§9 Cross-references** — Link to cycle 385 / cycle 398
  predecessor scoping docs; link to cycle 399's
  `trichildPolynomial` ship location (`Section422.lean:6412–6423`);
  link to memory `feedback_simp_recursive_def_overunfolds.md` for
  the calibration-witness recipe.
* **§10 Self-reference** — Cycle 402 ships this doc as its sole
  deliverable; cycle 403 ships per §8.

### §C.3 Concrete instructions for the cycle 402 worker

1. **Read predecessor scoping docs first** (this is non-negotiable):
   * `.prover-state/issues/def_422B_phase_alpha_prime_family_C_scoping.md`
   * `.prover-state/issues/def_422B_phase_alpha_prime_family_bushy_scoping.md`
   * `.prover-state/issues/def_422B_phase_alpha_prime_scoping.md`
     (the original cycle 379 scoping doc)

2. **Read cycle 370's `bushy` closed form** at
   `OpenMath/Chapter4/Section422.lean:3011–3168` and cycle 399's
   `trichildCrossTerm`/`trichildPolynomial` at lines 6412–6423.
   These set the structural template that Phase α'.5 must extend.

3. **Write the new file** at
   `.prover-state/issues/def_422B_phase_alpha_prime_5_scoping.md`
   following §C.2's section structure. Target 400–700 lines.

4. **Do NOT edit any Lean files.** This is a markdown-only cycle.
   `grep -c sorry OpenMath/Chapter4/Section422.lean` must read 5
   at the end of the cycle (unchanged from HEAD).

5. **Do NOT submit to Aristotle.** No mathematical content to
   submit.

6. **Update `extraction/formalization_data/lean_status.json`**:
   bump the `def:422B` row's `cycle_completed_at` to 402. Status
   remains `partial`.

7. **Update `plan.md`**: bump the `def:422B` row's cycle reference
   to 402. Status remains `[~]`.

8. **Write `.prover-state/task_results/cycle_402.md`** documenting
   the scoping ship (mirror the cycle 398 task results format).

### §C.4 Success criteria

* New file at `.prover-state/issues/def_422B_phase_alpha_prime_5_scoping.md`
  with 400–700 lines spanning §1–§10.
* §3 catalogues at least the cycle 370 bushy data point and
  identifies the cycle 403 target (`mk [vertex, vertex, cherry]`).
* §4 explicitly references cycle 399's hard-coded
  `(vertex, vertex, vertex)` branch and pins the generalisation
  target.
* §6 phase decomposition has at least 3 sub-phases (α'.5.0 / α'.5.1 / α'.5.2)
  with LOC estimates and cycle-count estimates.
* §8 cycle 403 entry point is concrete: names the target tree, the
  estimated LOC, and the proof template to mirror.
* Zero Lean changes (`git diff --stat` should show only
  `.prover-state/` paths plus possibly `plan.md` and
  `extraction/formalization_data/lean_status.json` cycle-stamp bumps).
* `lean_status.json` `def:422B` row's `cycle_completed_at` bumped
  to 402.
* `plan.md` `def:422B` row's `[~]` line bumped to cycle 402.
* §422 axiom-clean streak advances: 63 substantive + 3 doc → **63
  substantive + 4 doc** (cycles 336–402).

## §D. What NOT to attempt

Each forbidden direction below has a specific rationale; do not try
to circumvent these.

* **Do NOT edit `OpenMath/Chapter4/Section422.lean` (or any other Lean
  file).** This is a markdown-only cycle by design. Touching Lean would
  introduce build risk, axiom-check risk, and risk a sorry-count
  regression. Per the cycle 385 / cycle 398 precedent, scoping cycles
  ship 0 LOC of Lean.

* **Do NOT attempt to close the cycle 365 grandfathered sorry** at
  `Section422.lean:2279`. The cycle 401 worker explicitly deferred
  this: "should be deferred to mid-cycle 402+, after the planner has
  chosen between Options 1 and 3." Phase β/γ closure work is a
  separate multi-cycle effort; cycle 402 is not the time.

* **Do NOT attempt to ship a non-vacuity Lean witness alongside the
  scoping doc** ("scoping + small ship" hybrid). The cycle 398
  markdown-only precedent shipped no Lean and that pattern stands.
  Mixing scoping with substantive ship inflates risk for no
  proportional gain.

* **Do NOT pivot to `def:442A`, `thm:535A`, `thm:541A`, `lem:351A`, or
  any other fresh entity** without first asking. The cycle 402 planner
  investigated `def:442A` (heavy: Riemann surfaces, blocked by
  `rouche_theorem_missing.md`-class infrastructure) and `lem:351A`
  (plausibly single-cycle but requires building an RK stability-function
  definition from scratch). Both are deferred. If you discover during
  cycle 402 that the scoping-doc deliverable is somehow infeasible (it
  should not be), document why and stop — do not freelance a pivot.

* **Do NOT poll Aristotle.** No in-flight projects.

* **Do NOT attempt to compile Section422.lean even as a smoke test.**
  Cycle 401 measured 1165s warm rebuild. A smoke test in cycle 402 has
  no purpose (no Lean edits) and would burn 20+ minutes of wall time.
  Trust the HEAD state.

* **Do NOT introduce any `axiom`/`constant`/`sorry`-marked declarations
  anywhere.** Markdown-only cycles cannot regress axiom hygiene.

* **Do NOT raise `maxHeartbeats`.** N/A for markdown.

* **Do NOT scope Phase α'.5 too narrowly.** Specifically, do not
  collapse it to "just `mk [vertex, vertex, cherry]` and stop." The
  scoping doc must articulate the full k ≥ 3 generalisation roadmap
  (including k = 4 as a future deferred sub-phase) so that cycle 403+
  workers have a concrete trajectory for 4–6 future cycles.

## §E. Aborted-cycle escape valve

If for some unexpected reason the scoping doc cannot be written this
cycle (e.g., predecessor scoping docs reveal that Phase α'.5 is
already fully covered and no new doc is needed), the fallback is to
ship a single small Lean witness:
`elementaryWeightQ_phi_inv_mkVertexVertexCherry` (the §C.2 §8 cycle
403 target tree, but shipped one cycle early). This requires ~250 LOC,
follows the cycle 372 `mk [vertex, cherry]` template, and would score
substantive (2). However, this is **only the fallback** — the scoping
doc is the primary deliverable. Do not jump straight to the fallback.

## §F. Faithfulness check reminder

This cycle introduces no new Lean entities. The scoping doc is pure
planning material. The CLAUDE.md "Pre-Commit Faithfulness Checklist"
section does not apply to markdown-only ships. Worker still runs the
standard pre-commit verification: `grep -c sorry
OpenMath/Chapter4/Section422.lean` returns 5; `git diff --stat` shows
only `.prover-state/` paths plus possibly `plan.md` and
`extraction/formalization_data/lean_status.json` (the two cycle-stamp
bumps).
