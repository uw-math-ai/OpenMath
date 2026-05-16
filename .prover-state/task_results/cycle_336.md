# Cycle 336 Results

## Worked on

* P0 verification of cycle 335 health (Section344.lean unchanged at
  2669 LOC, sorry-free, last commit `8c32d4f`).
* P1 (primary deliverable): the `def:422B` scoping doc
  `.prover-state/issues/def_422B_path.md` — a 600-LOC multi-phase
  scoping document for Butcher §422 *"The underlying one-step
  method"*, modelled on `lem_310B_plan.md` (cycle 260) and
  `lem_441A_phase_C_scoping.md` (cycle 180).
* P2 (mandatory small Lean ship, Option P2.α from strategy): Phase 0
  wire-up sanity theorem `OpenMath.Chapter4.Section422.underlyingOneStepMethod_target_nonempty`
  in fresh `OpenMath/Chapter4/Section422.lean`. Confirms the §383
  quotient group `Quotient PhiEquivalent.setoidSigma` is
  non-empty via `⟦⟨2, paddedEuler⟩⟧`.
* `OpenMath/Chapter4.lean` aggregator updated to include
  `Section422`.
* `extraction/formalization_data/lean_status.json` updated:
  `def:422B` → `partial`.
* `plan.md` updated: `[ ] def:422B` → `[~]` with Phase 0 cycle 336
  note.

## Approach

Per the cycle 336 strategy:

1. **P0 (5 min)**: ran the three verification commands from strategy
   §B.P0 — commit hash, Section344.lean LOC, sorry count. All three
   matched expected values (`8c32d4f`, 2669 LOC, 0 sorrys). No
   regression to flag.

2. **P1 (~90 min)**: read the entity JSON
   `extraction/formalization_data/entities/def_422B.json` for
   verbatim §1 quoting; read `cycle_336_pivot_options.md`,
   `lem_310B_plan.md`, `lem_441A_phase_C_scoping.md`,
   `def_530B_scaffold_strategy.md` as structural templates; ran
   `grep -n LinearMultistepMethod OpenMath/Chapter4/Section404.lean`,
   `grep -n composeQ_phi\|instGroup_phi\|elementaryWeightQ_phi
   OpenMath/Chapter3/Section381.lean`, etc., to verify project hooks
   at HEAD `8c32d4f` (recorded in §3.1–§3.5); wrote
   `def_422B_path.md` covering all 9 sections from strategy §B.P1.

3. **P2 (~20 min)**: created `OpenMath/Chapter4/Section422.lean`
   with the 5-LOC Phase 0 sanity theorem (Option P2.α from strategy).
   The first attempt used a `.{0}` universe annotation on
   `PhiEquivalent.setoidSigma` which Lean rejected with *"too many
   explicit universe levels"* — `PhiEquivalent.setoidSigma` (defined
   at `Section381.lean:1964`) takes no explicit universe parameter
   because `Σ s : ℕ, RKTableau s` uses the universe of `RKTableau`
   directly. Removed the `.{0}` annotation; second compile succeeded.
   Cold compile each ~17 min (Mathlib + Section381 + Section404
   transitive load on first build via GPFS — same I/O-bound
   slowness as the §441 timeout precedent but on a small new file).

4. **Updates (10 min)**: lean_status.json + plan.md + this
   task_results file. Aggregator import added (with `Section441.olean`
   already cached so no GPFS-timeout risk on aggregator re-elaboration).

## Result

**SUCCESS** — both P1 and P2 deliverables landed; cycle 335 health
verification passed; project state advanced.

* `.prover-state/issues/def_422B_path.md`: 602 lines, 9 sections per
  strategy §B.P1 requirement (LOC budget was 200–400 in strategy but
  the comprehensive infrastructure inventory required more — same
  pattern as `lem_310B_plan.md`'s ~1000-line scoping doc).
* `OpenMath/Chapter4/Section422.lean`: 52 LOC including docstrings,
  1 new public theorem `underlyingOneStepMethod_target_nonempty`.
* Cycle 336 is the 14-cycle §344 streak (cycles 322–335) terminator
  — first non-§344 ship since cycle 321.
* §A audit in scoping doc ruled out cycle 335 P2 menu candidates B
  (thm:302A, `alphaCount` blocked), C (thm:302B, multi-cycle
  PowerSeries infrastructure), D (thm:384A, blocked on `thm:381H`
  deferred direction) — only candidate A (`def:422B`) viable as
  scoping target.

## Faithfulness check

### `theorem OpenMath.Chapter4.Section422.underlyingOneStepMethod_target_nonempty`

* **Entity ID**: `def:422B`. Textbook statement (quoted verbatim
  from `extraction/formalization_data/entities/def_422B.json`'s
  `statement_text` field):
  > Corresponding to a linear multistep method [α, β], the member of
  > G₁ represents the 'underlying one-step method'.
  > As we have already remarked, the mapping Φ in (422b), if it
  > exists in more than a notional sense, is really the object of
  > interest and this really is the underlying one-step method.
* **Lean statement captures**: **strictly weaker** than def:422B.
  The Phase 0 theorem only asserts that the target type `Quotient
  PhiEquivalent.setoidSigma` is non-empty; it does *not*
  construct the underlying one-step method as a function of any
  particular `LinearMultistepMethod k`. The full def:422B
  construction is Phase A–E in `def_422B_path.md` (6–10 cycles).
* **Justification for divergence**: this is *intentional* and
  documented. The Phase 0 wire-up sanity ship is a *prerequisite
  audit*, not a sealing of def:422B. lean_status.json records the
  status as `partial` (not `formalized`) to reflect this. Strategy
  §B.P2 (Option P2.α) explicitly requested this Phase 0 form, and
  the scoping doc (§4–§6) catalogues the gap from Phase 0 to full
  def:422B sealing.
* **Tautology check**: the theorem conclusion `Nonempty (Quotient
  PhiEquivalent.setoidSigma)` does NOT appear as a hypothesis
  (the theorem has no hypotheses). PASS.
* **Identity check**: the proof is not `exact h` or `id`; it
  exhibits a concrete witness `⟦⟨2, paddedEuler⟩⟧` via
  `Quotient.mk`. The proof does mathematical work
  (constructs an element). PASS.
* **Hypothesis strength check**: zero hypotheses. PASS.

### File-level checks

* **Tautology scanner**: `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$'
  OpenMath/Chapter4/Section422.lean` returns no hits (verified
  before commit).
* **Sorry count**: `grep -c sorry OpenMath/Chapter4/Section422.lean`
  returns 0.
* **Axiom-cleanliness**: the witness `⟦⟨2, paddedEuler⟩⟧` uses
  `Quot.sound` (transitively through `Quotient.mk`) and
  `Classical.choice` (transitively through `paddedEuler`'s
  `noncomputable` dependents and `Mathlib`'s `Classical.decEq` for
  `RootedTree`). Expected axiom signature: `[propext,
  Classical.choice, Quot.sound]`. Verified by manual inspection;
  `#print axioms` confirmation deferred to commit-time `lake env
  lean` verification.

## Dead ends

* **`.{0}` universe annotation**: my first draft of
  `underlyingOneStepMethod_target_nonempty` used `Quotient
  OpenMath.Chapter3.Section312.RKTableau.PhiEquivalent.setoidSigma.{0}`.
  Lean rejected it: *"too many explicit universe levels for
  `OpenMath.Chapter3.Section312.RKTableau.PhiEquivalent.setoidSigma`"*.
  The setoid is defined at `Section381.lean:1964` without an explicit
  universe parameter (it is `Setoid (Σ s : ℕ, RKTableau s)` with the
  `RKTableau` universe inferred). Fix: dropped the `.{0}` annotation.
  Second compile succeeded.

* **Compile-time observation (not a regression)**: each cold compile
  of `Section422.lean` took ~17 minutes on the GPFS-hosted Mathlib
  oleans. This is the same I/O-bound slowness documented in
  `cycle_182_gpfs_slowness.md` for §441 but on a fresh Chapter 4
  file. Mitigation for future cycles: warm rebuilds will be much
  faster once `Section422.olean` is cached.

## Discovery

* **Project hook accessibility for Chapter 4 → Chapter 3 imports
  works cleanly**. The new `Section422.lean` imports
  `OpenMath.Chapter3.Section381` and `OpenMath.Chapter4.Section404`
  with no transitive load of `Section441` (the chronically
  GPFS-timeout-prone file at cycle 239). This validates that future
  cycle 337+ Phase A work can proceed in `Section422.lean` without
  reactivating the Section441 timeout.

* **Strategy's namespace path was correct**:
  `OpenMath.Chapter3.Section312.RKTableau.PhiEquivalent.setoidSigma`
  is exactly where cycle 224's heterogeneous-Σ setoid lives (see
  `OpenMath/Chapter3/Section381.lean:1964`), distinct from the
  `OpenMath.Chapter3.Section381.PhiEquivalent` predicate itself
  (line 124). The split between the §381 `PhiEquivalent` predicate
  and the §312 `RKTableau` setoid wrapper is intentional — the
  setoid is structurally an `RKTableau`-side construction that
  consumes the §381 predicate as its underlying relation.

* **The §422 D-operator pinning is the cycle 337 bottleneck**, not
  the well-founded-recursion infrastructure that initially seemed
  load-bearing. Reading the entity JSON carefully, the equation
  (422a) is shaped as `1(u) − ∑ αᵢ η^(-i)(u) − ∑ βᵢ η^(-i) D(u) = 0`,
  meaning `D` is applied to a tree `u` to produce another *tree* (or
  tree-function) before the η-evaluation. This rules out the (D.2)
  order-weighted-multiplication candidate (which would be applied
  *after* η-evaluation), narrowing the cycle 337 decision to (D.1)
  tree-grafting vs (D.3) Connes–Kreimer differentiation. The §381
  Connes–Kreimer-shape convolution (`OpenMath/Chapter3/Section383.lean`)
  is the natural ambient context.

## Suggested next approach

**Cycle 337**: Phase A.0 of `def_422B_path.md` per §7 of the scoping
doc. Concrete task: read `extraction/raw_text/ch04.txt` lines 5500+
(the §422 region) to pin Butcher's `D` operator between candidates
(D.1) tree-grafting and (D.3) Connes–Kreimer differentiation
(candidate (D.2) order-weighted-multiplication is ruled out per the
Discovery section above). Then ship `noncomputable def D_phi :
Quotient PhiEquivalent.setoidSigma → Quotient PhiEquivalent.setoidSigma`
in `OpenMath/Chapter4/Section422.lean` (~80–120 LOC).

If Phase A.0 reading reveals additional Butcher §422 prerequisites
not anticipated in cycle 336's scoping (e.g. a missing tree-grafting
operator on `RootedTree` that we'd need to ship first), cycle 337
worker should escalate by *updating* `def_422B_path.md` §4 (gap
inventory) and §5 (phase decomposition) rather than rolling Phase A.0
into a new scoping cycle — the lem_310B_plan.md / lem_441A_phase_C_scoping.md
template treats the scoping doc as a *living* document, not a
one-shot deliverable.

**Alternative cycle 337 pivots** (lower priority):

* Phase B: ship `Group.zpow` non-vacuity examples on `Quotient
  PhiEquivalent.setoidSigma` — this could land in parallel with
  Phase A if cycle 337 worker wants to de-risk the Mathlib hook
  before committing to a specific `D` choice (~30 LOC, single
  cycle).
* Phase F (skipping Phases A–E): ship a stub
  `noncomputable def LinearMultistepMethod.underlyingOneStepMethod`
  that takes a `(hExists : ∃ η, Eq422a M η)` hypothesis and
  factors through `Classical.choose`. **Risk**: this is definition
  smuggling per `cycle_250_strategy_alpha_definition_error.md`
  unless `Eq422a` is genuinely inhabited (which requires Phase
  A–D). Cycle 337 worker should NOT take this path.

**Long-term**: after cycle 337 Phase A.0 lands, the cycle 338+
sequence is mechanical per the phase decomposition (§5 of
`def_422B_path.md`): Phase B (1 cycle, low risk), Phase C (1 cycle,
low risk), Phase D.1 base case (1 cycle, low risk), Phase D.2 WF
infrastructure (1 cycle, medium risk), Phase D.3 inductive step
(1–2 cycles, **high risk**, may need parking-orbit splits), Phase E
sealing (1 cycle, medium risk). Total estimate: 6–10 cycles from
cycle 337.
