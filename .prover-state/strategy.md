# Cycle 508 Strategy — Path (b) `nchildPolynomial` scoping doc (markdown-only)

## §A. Context

Cycle 507 (`task_results/cycle_507.md`, commit `6076201`) closed
Phase γ k=4 verification + 5 structural-coverage examples per the
cycle 506 scoping doc §6.2. The §422 axiom-clean streak now stands
at **79 substantive + 7 doc** (cycles 336–507).

There is **no real blocker** for cycle 508. The sole code-level
sorry in the repo is `OpenMath/Chapter4/Section422.lean:2279`
(cycle 365's `powRep_sum_eq_of_strict_subtree_agreement` general
body, open for **143 cycles**). It is the long-term Phase β.2 / δ /
ε target, gated on multi-cycle infrastructure that cycle 508 is
about to scope.

Per `def_422B_phase_beta_gamma_k4_scoping.md` §6.3 (cycle 505's
scoping; reaffirmed in cycle 507's task results "Suggested next
approach"), **cycle 508's deliverable is the markdown-only
`nchildPolynomial` parametric-recursion scoping doc** — the
prerequisite design document for cycle 509+'s 10–15-cycle Lean
implementation track that eventually closes the cycle 365 sorry.

## §B. Cycle 508 deliverable (single substantive item)

Ship a new markdown file at

```
.prover-state/issues/def_422B_phase_alpha_prime_7_nchildPolynomial_scoping.md
```

(~600–900 LOC markdown, **ZERO Lean delta**, LOW risk).

This file is to the §422 cluster what cycle 402's Phase α'.5
scoping doc was to the k=3 ladder, and what cycle 498's Phase
α'.5.2 scoping doc was to the k=4 ladder: a multi-cycle planning
document that the cycle 509+ Lean implementations consume directly.

### §B.1 Required sections (template from cycle 498 / 505)

The doc must include the following sections (~11 sections,
~600–900 LOC total):

* **§1 Status & blocker** — anchor the doc to the §422 streak state
  at HEAD (79 substantive + 7 doc, Section422.lean 19299 LOC, sorry
  count 5 = 4 docstring + 1 grandfathered cycle 365). Explain why
  the parametric `nchildPolynomial` recursion is the structural
  resolution for Phase β.2 at k ≥ 5 (cycle 497's R6.B falsity:
  `inversePolyTree`'s `mk (_::_::_::_::_::_) → 0` catch-all
  contradicts `Φ_{η⁻¹}(t)`'s generic non-vanishing on quadchild+
  trees).

* **§2 What needs to be built** — articulate the target signature.
  Strawman:

  ```lean
  noncomputable def nchildPolynomial : (n : ℕ)
      → (children : Fin n → RT)
      → (inv_children : Fin n → ℝ)
      → (f : RT → ℝ) → ℝ
  ```

  Discuss design choices:
  - Index by `Fin n` (uniform; matches Mathlib idiom) vs `List RT`
    (matches current `mk children` constructor; allows `List.foldr`
    recursion).
  - Recursion structure: subset-sum expansion over
    `Finset.powerset (Finset.range n)` (matches cycle 498 §3's
    16-block decomposition at k=4; generalises to `2^n` blocks);
    OR fold-over-children with per-child contribution.
  - Termination: by `n` (decreasing), or by `t.order` (if
    `nchildPolynomial` is called recursively at children).

* **§3 Block decomposition (general k)** — extend cycle 498's §3
  16-block table to the general `2^n`-block decomposition. Show
  how cycle 358's `elementaryWeightQ_phi_inv_mk` formula
  ```
  Φ_{⟦M⟧⁻¹}(mk children) = -Σⱼ M.b j · M.derivativeWeightWithSrc M.inverse j (mk children)
  ```
  unfolds per-row to `Πℓ (inv_cℓ + S_ℓ(j))` where the product over
  `ℓ ∈ {1, …, n}` distributes into `2^n` blocks indexed by
  `S ⊆ {1, …, n}` (selecting either the constant `inv_cℓ` factor or
  the A-sum `S_ℓ(j)` factor at each position).

* **§4 `nchildPolynomial` strawman** — concrete proposed body.
  Strawman option A (subset-sum expansion):

  ```lean
  noncomputable def nchildPolynomial (n : ℕ) (children : Fin n → RT)
      (inv_children : Fin n → ℝ) (f : RT → ℝ) : ℝ :=
    -(f vertex * ∏ i : Fin n, inv_children i)                    -- Block (1) all-const
    - ∑ ℓ : Fin n,                                                -- Single-A blocks
        (∏ i ∈ Finset.univ.erase ℓ, inv_children i) * f (mk [children ℓ])
    + nchildCrossTerm n children f                                -- Mixed cross-term blocks
    - f (mk (List.ofFn children))                                 -- Self-kernel
  ```

  Discuss how `nchildCrossTerm` handles the `2^n - n - 2` mixed
  cross-term blocks (bilinear, trilinear, …, (n−1)-linear, n-linear).

* **§5 `nchildCrossTerm` strawman** — propose a dispatch design.
  Two options:
  - **Option A (per-tuple `if-then-else` cascade)**: mirror the
    cycle 387 `bichildCrossTerm` / 399 `trichildCrossTerm` / 500
    `tetrachildCrossTerm` precedent. Each named tuple
    `(t₁, …, tₙ)` gets one branch. Per Phase α' cycle 402's §3.3
    candidate enumeration, this explodes combinatorially for k ≥ 5.
  - **Option B (recursive on `Finset` of selected positions)**:
    fold over `Finset.powerset (Finset.range n) \ {∅, singletons,
    full}` (the cross-term blocks), reusing `bichild`/`trichild`/
    `tetrachildCrossTerm` for the 2-, 3-, and 4-position subsets,
    and a new general-k helper for k ≥ 5.

* **§6 Phase α'.7 phase decomposition** — break the cycle 509+
  implementation into single-cycle deliverables. Strawman:

  | Phase | Cycle | Deliverable | LOC | Risk |
  |-------|-------|-------------|-----|------|
  | α'.7.0 | 509 | `nchildPolynomial` signature + base cases (n = 0, 1, 2, 3) reduce to existing `inversePolyTree` arms | 200–300 | MED |
  | α'.7.1 | 510 | `nchildPolynomial n = 4` calibration witnesses against cycles 499/501/502/503/504 | 150–250 | LOW |
  | α'.7.2 | 511 | Cycle 358 → `nchildPolynomial` bridge theorem | 300–500 | HIGH |
  | α'.7.3 | 512+ | k = 5 closed-form witness ship (`mk [v, v, v, v, v]`) + bridge | 300–500 | MED |
  | α'.7.4 | 513+ | k = 5 non-symmetric ladder (3–5 cycles) | 300–500/cycle | MED |
  | α'.7.5 | 515+ | `inversePolyTree` 7-arm extension (k=5) + Phase β.1 k=5 dispatch + Phase γ k=5 verification | 300–500/cycle | MED |
  | α'.7.6 | 518+ | k = 6, 7, ... ladder (or pivot to a tree-order-bounded carve-out) | ... | ... |
  | Phase β.2 | 520+ | Lift Phase β.1 + γ to arbitrary `t : RT` (cycle 365 closure dependency) | 300–500 | HIGH |
  | Phase δ | 522+ | Inverse-power lift to `η_q^(-(m+1))` via cycle 495 §5.4 | 300–500 | HIGH |
  | Phase ε | 524+ | Close cycle 365 sorry | 100–200 | MED |

  Total: 10–15 cycles per the cycle 505 §6.3 estimate.

* **§7 LOC budget summary** — table of per-cycle LOC totals,
  cumulative `Section422.lean` projection (currently 19299, expected
  to reach ~25000–28000 by Phase ε), warm rebuild cost projection
  (currently ~5m, expected to reach ~10–15m at file end).

* **§8 Risk inventory** — enumerate 8–12 risks:
  - R1: `nchildPolynomial` termination obstruction (Mathlib well-founded recursion API at large `n`).
  - R2: Cycle 358 bridge proof complexity (`2^n`-way case analysis).
  - R3: Build-cost escalation (`Section422.lean` past 25k LOC).
  - R4: Cycle 504 cancellation-pattern unpredictability (kernels surface non-monotonically; sympy pre-flight mandatory for every new witness).
  - R5: Phase β.2 at k ≥ 5 may still need a structural induction beyond what `nchildPolynomial` provides (worst-case: need a `nchildPolynomial_eq_of_subtree_agreement` headline lemma analogous to cycle 497's Phase γ).
  - R6: Faithfulness divergence — `nchildPolynomial`'s definition may smuggle in design choices that obscure Butcher §422's textbook semantics.
  - R7: Cycle 365 grandfathered sorry has been open 143+ cycles; obstructions may surface only at attempt time (HIGH).
  - R8: Tautology scanner false-positive risk on the new file's docstring content (per cycles 500–504 scoring history).
  - R9 (optional): Pivot pressure — by cycle ~515 the §422 streak will be at ~90 substantive cycles, longest single-entity run in project history. Document explicit decision criteria for when to pivot.

* **§9 Cycle 509 entry point** — concrete first steps for the
  cycle 509 worker:
  1. Pre-flight: read cycle 358 `_inv_mk` (`Section422.lean:582`),
     cycle 387/399/500's `bichild`/`trichild`/`tetrachildPolynomial`
     definitions, and cycle 498 §3's 16-block decomposition.
  2. Decide on the `Fin n` vs `List RT` indexing convention
     (recommend `Fin n` for Mathlib-idiom alignment).
  3. Ship the `nchildPolynomial` signature + base cases for
     `n ∈ {0, 1, 2, 3}` that reduce to existing `inversePolyTree`
     arms by `rfl` or `unfold + ring`.
  4. Calibration witnesses confirming `n = 0, 1, 2, 3` instances
     match `inversePolyTree`'s vertex / monochild / bichild /
     trichild arms (cycles 387/399 precedent).

* **§10 What this doc does NOT do** — explicit non-deliverables:
  - Does NOT ship any Lean code.
  - Does NOT prescribe `nchildCrossTerm`'s exact dispatch shape
    (left to cycle 511+'s implementation).
  - Does NOT attempt the cycle 365 sorry closure.
  - Does NOT touch `Section422.lean` or `lean_status.json`'s
    `def:422B.status` field (stays `partial`).
  - Does NOT commit to a specific `nchildPolynomial` termination
    measure (left as a design decision for cycle 509).

* **§11 Cross-references** — link to:
  - `def_422B_path.md` (cycle 336 overall roadmap).
  - `def_422B_phase_alpha_prime_5_scoping.md` (cycle 402, k=3 ladder
    scoping).
  - `def_422B_phase_alpha_prime_5_2_scoping.md` (cycle 498, k=4
    ladder scoping; the direct template).
  - `def_422B_phase_beta_gamma_k4_scoping.md` (cycle 505, the
    parent scoping that authorised this Path (b) cycle).
  - `def_422B_phase_D_3_scoping.md` (cycle 357, original Phase D.3
    plan that introduced cycle 365's sorry).
  - `def_422B_subLemmaA_inductive_plan.md` (cycle 373, Sub-lemma A
    inductive plan).
  - Cycle 499–504 task results (`task_results/cycle_499.md` through
    `cycle_504.md`) for the k=4 calibration ladder.
  - Relevant memory files: `feedback_dws_cherry_factor_includes_v_aᵢ.md`,
    `feedback_cherry_child_cancellation.md`,
    `feedback_vertex_prefix_cherry_tail_kernels.md`,
    `feedback_ring_def_opacity.md`,
    `feedback_simp_recursive_def_overunfolds.md`,
    `feedback_lake_env_lean_no_olean_update.md`.

### §B.2 Bookkeeping deliverables (mechanical)

1. **`extraction/formalization_data/lean_status.json`**: bump
   `def:422B.cycle_completed_at` from 507 to 508; append a note to
   `def:422B.note` reflecting the scoping doc ship. **Do NOT
   change `status` (stays `partial`).**

2. **`plan.md`**: append a cycle 508 closure paragraph to the
   `def:422B` row's note, mirroring the cycle 505/506/507
   format ("Cycle 508 ships markdown-only Phase α'.7
   `nchildPolynomial` scoping doc...").

3. **`.prover-state/task_results/cycle_508.md`**: standard 7-section
   format (Worked on / Approach / Result / Faithfulness check / Dead
   ends / Discovery / Suggested next approach).

## §C. What NOT to do this cycle

* Do **NOT** modify `OpenMath/Chapter4/Section422.lean` or any
  other Lean file. Cycle 508 is markdown-only by design (LOW risk
  cycle to break the cycle 505 → 507 substantive-ship cadence at
  a natural strategic pivot).

* Do **NOT** attempt to close the cycle 365 grandfathered sorry at
  `Section422.lean:2279`. It is multi-cycle Phase β.2 / δ / ε
  territory and depends on the very `nchildPolynomial`
  infrastructure that cycle 508 is scoping.

* Do **NOT** extend the Phase α'.5.2 calibration ladder further
  (no new k=4 witnesses beyond the 5 shipped cycles 499–504). The
  cycle 504 worker's saturation analysis is dispositive: the
  symmetric vertex/cherry quadruple ladder is complete; mixed-tail
  k=4 witnesses (`(v, v, v, mk[c])`, `(v, v, c, mk[c])`,
  `(v, mk[c], c, c)`, etc.) would add LOC without unlocking new
  structural patterns.

* Do **NOT** attempt the cycle 365 sorry via a tree-order-bounded
  carve-out (Path c in cycle 498 §5.3). That path is contingent on
  Sub-lemma B's order-bound admissibility, which is itself open
  and requires a separate scoping pass.

* Do **NOT** prescribe the cycle 509+ Lean implementation's exact
  shape beyond the strawman signature in §B.1 §4–§5. The scoping
  doc must leave room for the cycle 509 worker to refine the
  recursion shape based on Lean's well-founded recursion API and
  Mathlib's `Finset.powerset` ergonomics.

* Do **NOT** modify `scripts/autonomous_loop.py` or address any
  tautology-scanner / empty-stuck-on prompt issues — those are
  loop-maintainer territory per
  `.prover-state/issues/tautology_scanner_false_positives.md`.

* Do **NOT** introduce `axiom`/`constant` declarations.

* Do **NOT** raise `maxHeartbeats` above 200000 anywhere (this
  cycle has no Lean changes so this is a no-op constraint, but
  noted for the cycle 509+ Lean track).

* Do **NOT** pivot to a fresh entity. The §422 cluster's Path (b)
  scoping is the natural compounding move; cycle 508's
  markdown-only ship preserves the streak while loading the next
  phase. Pivot decisions for cycle 509+ are explicitly deferred to
  §8 R9 of the new scoping doc and to cycle 509's planner.

* Do **NOT** Aristotle-batch anything. Cycle 508 is markdown-only;
  there are no Lean proof obligations to dispatch.

## §D. Approaches explicitly known to fail (do not retry)

Cycle 508 has no failed Lean approaches to inherit because it is a
markdown-only cycle. The relevant historical failure modes (do not
repeat in cycle 509+ Lean track):

* **Cycle 138/139 (`thm:550A` general-n sorry-first)**: rolled back
  because sorry count rose 0 → 1 without single-cycle closure path.
  Cycle 508's deliverable is markdown-only, so this rollback risk
  does not apply now, but cycle 509+'s Lean ships MUST follow the
  "no sorry-first scaffolds without single-cycle closure" rule.

* **Cycle 149/150 (`def:530B` operator-body sorry-first)**: rolled
  back because the operator body needed Banach fixed-point
  machinery the cycle hadn't scoped. Cycle 508's markdown-only ship
  inherits no body sorries; cycle 509+ must explicitly scope all
  recursion termination measures before committing definitions.

* **Cycle 200/201 (`thm:381H` deferred direction)**: rolled back
  because the sorry-first scaffold's three deferred directions had
  no single-cycle closure path. Cycle 508 ships only markdown; no
  sorries change.

* **`alphaWeight` definition-smuggling precedent (cycle 250)**:
  defined `α(t) = 1/γ(t)` (smuggled-in shortcut) instead of the
  textbook combinatorial definition. The cycle 508 scoping doc must
  explicitly flag `nchildPolynomial`'s design choices as documented
  divergences if any are made (faithfulness obligation per
  CLAUDE.md "Pre-Commit Faithfulness Checklist").

## §E. Cycle 508 success criteria

* New markdown file
  `.prover-state/issues/def_422B_phase_alpha_prime_7_nchildPolynomial_scoping.md`
  exists with 600–900 LOC across §1–§11.

* `lean_status.json` `def:422B.cycle_completed_at` = 508
  (status unchanged: `partial`).

* `plan.md` `def:422B` row has cycle 508 closure paragraph appended.

* `.prover-state/task_results/cycle_508.md` written.

* `OpenMath/` directory **unchanged** (`git diff --stat OpenMath/`
  returns empty).

* `grep -c sorry OpenMath/Chapter4/Section422.lean` = 5
  (unchanged — 4 docstring + 1 grandfathered cycle 365 at line
  2279).

* §422 axiom-clean streak: 79 substantive + 7 doc → **79
  substantive + 8 doc** (cycles 336–508).

## §F. Faithfulness check (cycle 508)

Per CLAUDE.md's "Pre-Commit Faithfulness Checklist":

* No new `def`, `structure`, `class`, or `theorem` introduced — this
  is a markdown-only scoping cycle.
* Sorry count unchanged at 5 (4 docstring + 1 grandfathered code
  sorry at `Section422.lean:2279`).
* Sole Lean-adjacent deliverable is the bookkeeping bump in
  `lean_status.json` (cycle counter only) and `plan.md` (closure
  paragraph only).

Faithfulness is trivially satisfied (no formal claims made about
Butcher textbook content; all references to `nchildPolynomial`,
`Φ_η`, `Φ_{η⁻¹}`, `inversePolyTree`, etc. in the new scoping doc
are scoping-level discussions of infrastructure design, NOT theorem
ships).

## §G. Aristotle batch

**Not applicable.** Cycle 508 is markdown-only; there are no Lean
proof obligations to dispatch.

## §H. Cycle 509 entry point (out of scope for cycle 508, recorded for cycle 509's planner)

Per the new scoping doc's §9, cycle 509's first deliverable will be
Phase α'.7.0: `nchildPolynomial` signature + base cases (n ∈ {0, 1,
2, 3}) reducing to existing `inversePolyTree` arms. Estimated 200–
300 LOC, MED risk (well-founded recursion termination is the main
unknown).

Cycle 508 worker: do NOT attempt Phase α'.7.0; only ship the
markdown scoping doc.

## §I. Note on the recurring "empty stuck-on" template phantom

The cycle 507 prompt may again exhibit the empty-stuck-on phantom
pattern documented across cycles 015 / 040 / 174 / 180 / 248 / 263 /
491 / 505 / 506 / 507 (10 confirmed instances now). The cycle 508
worker should NOT diagnose this pattern as a real blocker; the
scoping doc is the substantive deliverable. If the consultant
phase fires against cycle 508's markdown-only ship, the standing
recommendation from `consultant_advice_cycle_248.md` §I and
`tautology_scanner_false_positives.md` §D3 applies: the supervisor's
prompt-builder should short-circuit on markdown-only cycles. Worker
MUST NOT modify `scripts/autonomous_loop.py`.

## §J. Bottom-line directive

Cycle 508 ships **one markdown file**:
`.prover-state/issues/def_422B_phase_alpha_prime_7_nchildPolynomial_scoping.md`
(600–900 LOC, §1–§11 per the template in §B.1 above).

Plus the standard bookkeeping (`lean_status.json` cycle counter
bump, `plan.md` closure paragraph, `task_results/cycle_508.md`).

Zero Lean changes. Sorry count unchanged. §422 streak advances by
one doc cycle.

Cycle 509+ workers consume the new scoping doc to begin the multi-
cycle Phase α'.7 Lean implementation track toward eventual closure
of the cycle 365 grandfathered sorry.

### §J.1 Time budget

Cycle 508 has no Lean compile dependency — total cycle wall time
should be dominated by writing the scoping doc (~30–60 min for a
600–900 LOC markdown file with section structure and cross-references
already specified in §B.1). Bookkeeping is <5 min. No Aristotle
poll. No `lake build`. Worker should aim to commit and finish
well under 90 minutes total.

### §J.2 Quality bar for the scoping doc

The scoping doc should be **at least as detailed as cycle 498's
Phase α'.5.2 scoping** (1922 lines) but **need not exceed cycle 505's
868-line Phase β/γ k=4 scoping** if the §6 phase-decomposition table
captures the cycle 509+ plan in tabular form. Target ~600–900 LOC.

The §3 block decomposition section is the most substantive
mathematical content — devote ~150–250 LOC to it (covering the
`2^n` block count, the subset-indexing scheme, and the recursive
expansion of cycle 358's `_inv_mk` formula).

The §6 phase decomposition is the most operationally useful section
for cycle 509+ workers — devote ~100–200 LOC to a detailed table
plus per-row commentary on risks and Mathlib hooks.

§§1, 2, 4, 5, 7, 8, 9, 10, 11 each take ~30–80 LOC.
