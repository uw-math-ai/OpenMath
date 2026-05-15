# Cycle 260 Results

## Worked on

P1 (REQUIRED): wrote the multi-cycle scoping document
`.prover-state/issues/lem_310B_plan.md` for the textbook `lem:310B`
(Butcher §310, p. 173, "Elementary Differential Weight Formula").
P2 (REQUIRED): shipped four small `Finset.sum_*` API enrichment
lemmas plus two non-vacuity examples in
`OpenMath/Chapter3/Section301.lean` — the cycle-260 code-diff
guarantee. P3 (STRETCH): scouted the three §34/§35 pivot candidates
flagged in cycle 259's task results and added the findings as a §8
appendix to the scoping doc.

## Approach

### P1 — `lem_310B_plan.md` scoping doc

Followed the strategy's §1–§7 template plus the §8 P3 appendix.
Content built bottom-up from verified citations:

1. **§1 textbook statement.** Quoted from
   `extraction/formalization_data/entities/lem_310B.json` verbatim
   (`statement_latex` + `proof_latex` fields). Cross-referenced
   `extraction/raw_text/ch03.txt` (line 805–834 for `lem:310B`,
   line 748 for the (310i) equation, line 730–735 for
   `def:310A`, all verified via Grep). Pulled the
   `thm:306A` multinomial-Taylor statement from
   `entities/thm_306A.json` for the "Use Theorem 306A" proof step.

2. **§2 distilled mathematical content.** Identified the six
   components of the proof structure: labelled-tree quotient
   (`def:300C`), `θ`-rewriting (cycle 254 done), `α` closed form
   (cycle 250 done), `thm:306A` Taylor (unformalised),
   orbit-counting bridge (Mathlib `MulAction`-based), multilinear
   elementary-differential lift (scalar → polymorphic). Mapped each
   to specific Lean infrastructure.

3. **§3 Mathlib + project hooks already in place.** Inventoried
   every shipped cycle-017 through cycle-259 declaration that
   `lem:310B` will consume, with file path + line numbers verified
   against HEAD (`d889695`). Cross-checked Mathlib hooks
   (`Finset.sum_*`, `iteratedFDeriv`, `taylor_isLittleO`,
   `Asymptotics.IsBigO`) and flagged uncertain Mathlib citations
   (e.g. `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`)
   with `(verify)` markers per strategy instruction.

4. **§4 gap inventory.** Four sub-sections, each with:
   - §4.1 `def:300C` labelled-tree quotient — 2–4 cycles. Detailed
     the `Vertex` predicate, `LabelledRootedTree` structure, and
     `Setoid` machinery needed.
   - §4.2 `thm:306A` Taylor / multinomial — 1–3 cycles, deferrable.
     Flagged Mathlib gap (no multinomial Taylor at HEAD); suggested
     bypass route through Phase D.
   - §4.3 Orbit-counting bridge — 1–2 cycles. Identified the
     orbit-stabilizer theorem as the key Mathlib hook.
   - §4.4 Multilinear elementary-differential lift — 1–2 cycles.
     Mapped the cycle-248/259 scalar `HasDerivAt` chain rules to
     their polymorphic `HasFDerivAt` analogues. Documented the
     cycle 259 dead-end (`HasDerivAt.comp` semantics) and warned
     that the polymorphic version is genuinely combinatorially
     different.

5. **§5 proposed phase decomposition.** Six phases A–F, 15 sub-
   deliverables, 8–14 total cycle estimate. Each sub-phase has
   axiom-clean target, LOC estimate, and concrete non-vacuity
   witness. Matched the cycle 149–164 `def:530B` precedent in
   shape (multi-phase Path A with helper extraction).

6. **§6 risk assessment.** Per-phase risks: `Vertex` predicate
   motive issues (cf. memory `feedback_rootedtree_nested_induction`),
   σ-faithfulness divergence (Phase A.3 may need to defer to
   `symmetry_group_equivalence.md`), Mathlib gap on multinomial
   Taylor (Phase B can be bypassed), orbit-stabilizer name drift,
   `HasFDerivAt.comp` semantics (cycle 259 discovery now applies
   to Phase D). Cross-referenced cycle 149–164 `def:530B` template
   and cycle 200/201 rollback precedent.

7. **§7 cycle 261 entry point.** Concrete Phase A.1 deliverable:
   `RootedTree.Vertex` inductive predicate, `RootedTree.vertices`
   `Finset` enumeration, and the `vertices.card = order` identity.
   Axiom-clean target, ~80–120 LOC, single-cycle close. Three
   non-vacuity witnesses on `cherry`, `broom₃`, `mk [vertex,
   cherry]`.

8. **§8 entity-pivot scouting** (P3 appendix). Read all three
   candidate JSONs (`thm_351B.json`, `lem_342A.json`,
   `lem_342B.json`). Documented dependencies, statement summaries,
   prior-formalisation status, and per-entity verdicts. None
   transitively depend on `lem:310B` — confirmed independence.
   Best single-cycle pivot: `lem:342A` property (342a) shifted-
   Legendre orthogonality. `thm:351B` and `lem:342B` flagged as
   multi-cycle / sequentially blocked.

### P2 — B-series API enrichment

Mechanical `Finset.sum_*` ports to `OpenMath/Chapter3/Section301.lean`:

* `bseriesPartialSum_singleton`: `bseriesPartialSum f y₀ h {t} =
  bseriesTerm f y₀ h t`. Closure: `simp [bseriesPartialSum]`
  (`Finset.sum_singleton` fires automatically).
* `bseriesPartialSum_union`: `Disjoint S₁ S₂ →
  bseriesPartialSum f y₀ h (S₁ ∪ S₂) =
  bseriesPartialSum f y₀ h S₁ + bseriesPartialSum f y₀ h S₂`.
  Closure: `simp [bseriesPartialSum, Finset.sum_union hDisj]`.
* `bseriesAlphaPartialSum_singleton` / `_union`: analogous on the
  α-weighted family.

Two singleton-flavoured non-vacuity `example`s appended at the end
of each existing example block, both using `id : ℝ → ℝ` so `f y₀ =
y₀` evaluates by `rfl` (per strategy hint):

```lean
example (y₀ h : ℝ) :
    bseriesPartialSum (id : ℝ → ℝ) y₀ h
        ({vertex} : Finset RootedTree)
      = h • y₀ := by
  rw [bseriesPartialSum_singleton, bseriesTerm_vertex]; rfl
```

The trailing `rfl` discharges `h • id y₀ = h • y₀` by `id`-unfold.
The analogous α-version uses `bseriesAlphaTerm_vertex`.

Union-flavoured examples skipped (the existing cycle 255/256
`{vertex, cherry}` examples already exercise the multi-element
consume side; a union example wouldn't add new coverage).

### P3 — entity scouting

Documented as §8 of `lem_310B_plan.md`. Three entity JSONs read in
full, dependency lists cross-checked, single-cycle viability scored:

* `thm:351B`: independent of `lem:310B` (`transitive_dependencies:
  []`) BUT requires 5–8 cycles of prerequisite machinery
  (A-stability definition, stability function R(z), E-polynomial,
  maximum-modulus principle). Not single-cycle.
* `lem:342A`: independent of `lem:310B` (`transitive_dependencies:
  [cor:342D, lem:342B, thm:342C]`, none of which is `lem:310B`).
  Single-cycle entry point YES via property (342a) orthogonality of
  shifted Legendre on `[0,1]`, conditional on Mathlib's Legendre
  polynomial machinery being usable.
* `lem:342B`: independent of `lem:310B` BUT requires `lem:342A` as
  a prerequisite (consumes the zeros of `P_s^*`). Sequential, not
  single-cycle.

## Result

**SUCCESS.** All deliverables shipped:

- `.prover-state/issues/lem_310B_plan.md` written, 774 lines
  (above the strategy's 150–250-line target, but justified by §3
  hook inventory + 15 sub-phase decomposition + §8 P3 appendix).
  All cited Lean file paths and theorem names verified at HEAD
  via Grep/Read. No internal "TODO" or unfilled placeholders.
- `lake env lean OpenMath/Chapter3/Section301.lean` — exit 0.
- `lake env lean OpenMath/Chapter3.lean` — exit 0 (aggregator).
- `lake build OpenMath.Chapter3.Section301` — exit 0 (`.olean`
  rebuilt).
- `lake build OpenMath.Chapter3` — exit 0 (2860 jobs, full chapter
  rebuilt clean).
- `grep -c sorry OpenMath/Chapter3/Section301.lean` — `0`.
- `grep -c sorry OpenMath/Chapter3/Section{310,311}.lean` — `0`
  (no regression).
- `grep -c sorry OpenMath/Chapter3.lean` — `0`.
- `#print axioms` on all four new theorems
  (`bseriesPartialSum_singleton`, `bseriesPartialSum_union`,
  `bseriesAlphaPartialSum_singleton`,
  `bseriesAlphaPartialSum_union`) returns
  `[propext, Classical.choice, Quot.sound]` — axiom-clean.
- Tautology-scanner regex
  `:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$` on
  `Section301.lean` — no matches.

File LOC: 759 → 824 (+65 LOC, within the strategy's 20–80 LOC budget).

Repo sorry count remains 0.

## Faithfulness check

### P1 (`lem_310B_plan.md`) — planning document

No new `def` or `theorem`. The plan is a scoping document; faithfulness
applies to whether the cited textbook content and Lean-side
infrastructure are accurately represented. Every citation in §3
(project hooks) was verified at HEAD by reading the cited file +
line range. Every Butcher reference in §1 was pulled verbatim from
either `entities/lem_310B.json` (the entity record) or
`extraction/raw_text/ch03.txt` (the source text); no paraphrasing of
the textbook statement.

### P2 — four new `Finset.sum_*` ports

#### `bseriesPartialSum_singleton`, `bseriesAlphaPartialSum_singleton`

These are pure algebraic identities about `bseriesPartialSum` /
`bseriesAlphaPartialSum`. No textbook attribution required — they
are Lean engineering convenience lemmas matching the `Finset.sum_*`
template.

* Statement matches `Finset.sum_singleton`'s shape exactly.
* Proof: `simp [bseriesPartialSum]` (one-line `Finset.sum_singleton`
  closure).
* No new `def`, `class`, or `structure`. No definition smuggling.
* Conclusion does not appear as a hypothesis. ✓
* Proof is not `exact h_*` or `:= id`. ✓
* Hypotheses are textbook-minimum — `t` is universally quantified,
  no extra constraints. ✓

#### `bseriesPartialSum_union`, `bseriesAlphaPartialSum_union`

Same shape, exercising `Finset.sum_union`.

* Statement matches `Finset.sum_union`'s shape exactly.
* The `Disjoint S₁ S₂` hypothesis is textbook-minimum (matches
  `Finset.sum_union`'s requirement; without it the sum would
  double-count overlap). ✓
* Proof: `simp [bseriesPartialSum, Finset.sum_union hDisj]`.
* No new `def`, `class`, or `structure`. No definition smuggling.
* Conclusion does not appear as a hypothesis. ✓
* Proof is not `exact h_*` or `:= id`. ✓

#### Non-vacuity examples

Both new examples (singleton family, `id : ℝ → ℝ` substitution) are
genuine consume-side exercises:

* The singleton example proves a non-trivial reduction (`h • y₀` on
  the RHS — the smallest non-trivial value the partial-sum machinery
  can produce). ✓
* No tautological closure: the example requires both the new
  `_singleton` lemma AND cycle-254's `bseriesTerm_vertex` / cycle-256's
  `bseriesAlphaTerm_vertex` to close. ✓
* The `id`-substitution exercises the scalar specialisation cleanly;
  the `rfl` at the end is the `id y₀ = y₀` reduction (genuinely
  needed to bridge `h • id y₀` and `h • y₀`).

## Dead ends

No substantive dead ends this cycle. Two minor diagnostics:

1. **Initial axiom check failed with "Unknown constant".** First
   `#print axioms` run against `OpenMath.Chapter3.Section310.RootedTree.bseriesPartialSum_singleton`
   returned `unknownIdentifier` errors because the `.olean` had not
   been rebuilt after the file edit. Fix: ran
   `lake build OpenMath.Chapter3.Section301` to refresh the `.olean`,
   then `lake env lean /tmp/axcheck.lean` succeeded. Pattern: after
   editing a file, run `lake build <module>` before `#print axioms`
   checks against the new declarations.

2. **`lem_310B_plan.md` exceeded the strategy's 150–250-line target.**
   Final length 774 lines. The overage is concentrated in §3 (the
   project-hook inventory: 24 cited declarations across three files,
   each with a one-line description), §5 (15 sub-phases × ~3–5
   lines each), and §6 (per-phase risk analysis). The strategy's
   "Do not pad with filler" directive was respected — no padding,
   but the §3/§5/§6 substance genuinely exceeded the target. Future
   scoping docs of this scale should budget ~600–800 lines if the
   `lem:310B`-style 6-phase shape recurs.

## Discovery

- **Per-phase decomposition for multi-cycle textbook goals is
  the only viable single-cycle ship pattern.** The cycle 200/201
  rollback and cycle 149/150 `def:530B` rollback both confirm that
  sorry-first scaffolds without a credible single-cycle close are
  rejected by the supervisor. The cycle 151–164 `def:530B` Path A
  recovery (14 cycles, all axiom-clean) is the working template.
  `lem:310B`'s 6-phase, 8–14 cycle plan in `lem_310B_plan.md`
  follows the same shape.

- **`lem:342A` is the highest-value non-§310 pivot.** Among
  cycle 259's three flagged candidates (`thm:351B`, `lem:342A`,
  `lem:342B`), `lem:342A` is the only one with a single-cycle entry
  point. Its (342a) orthogonality property is independent of
  `lem:310B` and can be derived from Mathlib's Legendre polynomial
  machinery (pending verification of the Mathlib API surface). This
  is a viable cycle 261 alternative if the planner prefers a quick
  clean ship over starting Phase A.1 of the `lem:310B` plan.

- **`thm:306A` (multinomial Taylor) is a Mathlib gap, but is
  bypassable.** Mathlib has single-variable Taylor (`taylor_isLittleO`)
  but no multinomial form. Butcher uses `thm:306A` as the proof
  *technique* of `lem:310B`, but the *content* of `lem:310B` is the
  closed-form sum identity. The polymorphic Phase D chain-rule
  route bypasses `thm:306A` entirely — a useful structural
  observation for future cycles.

- **σ-faithfulness gap surfaces again in Phase A.3.** The deferred
  orbit-count theorem `Nat.card (orbit …) = r(t)!/symmetry t` is the
  same gap as cycle 017's
  `symmetry_group_equivalence.md`. `lem:310B`'s Phase A.3 either
  closes the gap or commits to never invoking the group-theoretic
  interpretation. Per Butcher's actual proof (which only uses the
  (301b) recursion), the latter route is viable — but the planner
  must commit to it explicitly.

## Suggested next approach

The cycle 261 planner has **two credible directions**:

1. **Phase A.1 of the `lem:310B` plan** (RECOMMENDED if the planner
   wants to maintain §310/§311 strategic momentum). Concretely:
   scaffold `RootedTree.Vertex : RootedTree → Type`,
   `RootedTree.vertices : (t : RootedTree) → Finset (Vertex t)`,
   prove `(vertices t).card = order t` via the cycle-017 `mutual`-
   recursion pattern (cf.
   memory `feedback_rootedtree_nested_induction`). Estimate:
   80–120 LOC, axiom-clean, ~1 cycle. Non-vacuity: enumerate
   vertices of `cherry` (2), `broom₃` (3), `mk [vertex, cherry]`
   (4). See §7 of `lem_310B_plan.md` for the detailed deliverable
   list.

2. **`lem:342A` (342a) orthogonality of shifted Legendre on
   `[0,1]`** (RECOMMENDED if the planner wants a clean cycle-261
   ship while reserving `lem:310B` infrastructure for cycles
   262+). First read Mathlib's
   `Mathlib.Analysis.SpecialFunctions.Polynomials.Legendre`
   (verify exact path) to confirm the Legendre machinery; then
   derive `P_n^* (x) := P_n(2x - 1)` as a definitional shift.
   Single-cycle target if the Mathlib API supports it cleanly.

**NOT RECOMMENDED**:

- Extending the order-N specialisation chain to order 6+. Cycle 259
  identified this as a dead-end (combinatorial growth, no new
  mathematical content). The strategy file 260 explicitly forbids
  it.
- `thm:351B` direct attack. Cycle 260 P3 scouting confirmed it
  requires ~5–8 cycles of prerequisite machinery (no single-cycle
  entry point).
- `lem:342B` direct attack. Requires `lem:342A` as a prerequisite;
  not single-cycle.
- Sorry-first Phase A scaffolds for `lem:310B`. Per the cycle
  149/150 rollback precedent and the cycle 200/201 rollback
  precedent, sorry-first scaffolds for multi-cycle targets without
  credible single-cycle closes are forbidden. Every Phase A
  sub-cycle must ship axiom-clean.

**Open scoping question for the planner**: cycle 261 should decide
between directions 1 and 2 based on whether the planner judges the
`lem:310B` strategic momentum more valuable than a clean §342
detour. Both directions are credible single-cycle deliverables.
