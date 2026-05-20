# Cycle 498 strategy — Phase α'.5.2 scoping doc (markdown-only)

## §A Context

Cycle 497 shipped **Phase γ** (`inversePolyTree_eq_of_subtree_agreement`)
clean, axiom-clean, advancing the §422 streak to **70 substantive + 5
doc** cycles. The cycle 497 worker also confirmed the cycle 495 scoping
doc's **R6.B claim is false**: Phase β.2 as scoped cannot close cycle
365's grandfathered sorry until `inversePolyTree` is extended to k ≥ 4
heterogeneous children (Phase α'.5.2/3). Cycle 358's
`elementaryWeightQ_phi_inv_mk` formula (Section422.lean:582) is
**generically nonzero** at k ≥ 4 trees, while `inversePolyTree`'s
default arm returns `0` — the equality is structurally false on
quadchild+ trees.

The cycle 365 grandfathered sorry at `OpenMath/Chapter4/Section422.lean:2279`
(`powRep_sum_eq_of_strict_subtree_agreement`) cannot be closed without
**first** extending `inversePolyTree` to k ≥ 4. That extension is the
explicit purpose of Phase α'.5.2/3 per the cycle 402 Phase α'.5
scoping doc, but the design specifics (analogous of cycle 387's
`bichildPolynomial` / cycle 399's `trichildPolynomial` scaled to
k = 4) have **not been scoped**.

**Aristotle results**: none pending.

**Sorry state**: 1 actual code sorry at `Section422.lean:2279` (cycle
365 grandfathered) + 4 docstring mentions. Unchanged from cycle 497.

## §B Decision: ship the Phase α'.5.2 scoping doc

Per the cycle 497 worker's explicit recommendation (cycle 497 task
results §"Suggested next approach", Option A) and the cycle 402
scoping precedent.

**Why a scoping doc, not substantive work**:

1. **Path is blocked without scoping.** Phase α'.5.2's
   `tetrachildPolynomial` + `tetrachildCrossTerm` infrastructure
   involves 16 block-decomposition terms (vs cycle 399's 8 for
   k = 3 and cycle 387's 4 for k = 2). Without a scoping pass, a
   substantive cycle would risk shipping a wrong recursive shape or
   missing kernel dependencies (analogous of cycle 384's
   "`mk [vertex, cherry]` kernel surprise" — only larger).

2. **Strong precedent**. Each of cycles 373 / 379 / 385 / 398 / 402 /
   495 shipped scoping docs that drove 3–11 subsequent substantive
   cycles. Each was scored neutrally or positively despite the
   markdown-only ship. The pattern works.

3. **Cycle 497's discovery (R6.B false) demands a fresh plan**, not a
   continuation of cycle 495's structurally-flawed roadmap. A scoping
   doc is the appropriate vehicle to formalize the pivot.

4. **No Aristotle results pending**, so no integration work pulls
   cycle 498 toward substantive territory.

5. **Empirical surface is sufficient**. The 14-tree Family C
   calibration ladder (cycles 371/372/384/386 + 391/393/396/397 +
   400/401 + 403/491–494) provides enough cross-term structural data
   to design the k = 4 case. Further empirical accumulation
   without a design plan is treadmill work.

## §C Deliverable

**One markdown file at**
`.prover-state/issues/def_422B_phase_alpha_prime_5_2_scoping.md`,
following the cycle 402 / cycle 495 scoping doc template. Target
~800–1100 LOC of Markdown, structured by §§1–11 below.

### §C.1 Required sections (template — adapt names/numbers as needed)

| § | Content |
|---|---|
| §1 | **Status & blocker.** Note: no Lean code shipped this cycle. Cite cycle 497's R6.B falsity and the cycle 365 sorry's blocked status. State that Phase α'.5.2/3 is a prerequisite. §422 streak status: 70 substantive + 5 doc (336–497) → 70 substantive + 6 doc (336–498). |
| §2 | **What needs to be built.** The `inversePolyTree` recursion currently has 5 arms (`mk []`, `mk [c]`, `mk [c₁,c₂]`, `mk [c₁,c₂,c₃]`, `mk (_::_::_::_::_) → 0`). Phase α'.5.2 extends to **6 arms** by adding `mk [c₁,c₂,c₃,c₄] → tetrachildPolynomial …` (with the catch-all bumped to k ≥ 5). |
| §3 | **The k=4 block decomposition.** Cycle 358's `_inv_mk` formula expands `Φ_{η⁻¹}(mk [c₁,c₂,c₃,c₄])` as a sum over `Πℓ (inv_ℓ + S_ℓ(i))` for ℓ ∈ {1,2,3,4}. That's 2⁴ = 16 blocks indexed by `{const, A-sum}⁴`. Decompose into: 1 all-const block, 4 single-A-sum blocks, 6 two-A-sum blocks (bilinear cross-terms), 4 three-A-sum blocks (trilinear cross-terms), 1 four-A-sum block (the self-kernel). Enumerate each and identify which yield reusable kernels vs new ones. |
| §4 | **`tetrachildPolynomial` strawman.** Sketch the structural decomposition mirroring cycle 387's `bichildPolynomial` and cycle 399's `trichildPolynomial`. Identify which 5 blocks are absorbed into the leading + 4 single-A-sum terms (Block (1) → `-(v · inv₁ · inv₂ · inv₃ · inv₄)`; Blocks (2)/(3)/(4)/(5) → `-(inv_{others} · f (mk [t_ℓ]))`). The 6 + 4 + 1 = 11 remaining blocks become `+tetrachildCrossTerm` and `-f (mk [t₁,t₂,t₃,t₄])`. |
| §5 | **`tetrachildCrossTerm` strawman.** Cross-term has shape `Σ (bilinear contributions) + Σ (trilinear contributions)`. Six bilinear positions (`{1,2}, {1,3}, {1,4}, {2,3}, {2,4}, {3,4}`) + four trilinear positions (`{1,2,3}, {1,2,4}, {1,3,4}, {2,3,4}`). At each position, identify the kernel signature: which `Φ_η(mk [...])` values surface. (Likely candidates: `mk [vertex, t_a, t_b]`, `mk [t_a, t_b]`, etc.) |
| §6 | **Phase decomposition.** Sub-phases α'.5.2.0 through α'.5.2.k: |
| | • α'.5.2.0 (1 cycle): empirical `mk [v,v,v,v]` (= `bushy_4`?) closed-form witness analogous to cycle 370's `bushy` for k=3 symmetric. Mirror cycle 370 template. |
| | • α'.5.2.1 (1 cycle): ship `tetrachildPolynomial` def + `tetrachildCrossTerm` placeholder dispatch (one branch for `(v,v,v,v)`). Update `inversePolyTree` recursion to 6 arms. Bump catch-all to k ≥ 5. Calibration witness `inversePolyTree_bushy_4` matching the α'.5.2.0 closed form. Mirror cycle 399. |
| | • α'.5.2.2+ (multi-cycle, ~5–10 cycles): k=4 non-symmetric witnesses, mirroring cycles 491–494 for k=3. Candidates: `mk [v,v,v,c]`, `mk [v,v,c,c]`, `mk [v,c,c,c]`, `mk [c,c,c,c]`, `mk [v,v,v,broom₃]`, etc. Each adds one `else if` branch to `tetrachildCrossTerm`. |
| | • α'.5.2.k+1 (1–2 cycles, deferred): once enough k=4 empirical surface exists, attempt to extend Phase β.1 dispatch and Phase γ structural induction to k=4 trees. |
| §7 | **LOC budgets per sub-phase.** α'.5.2.0: ~150–250 LOC (single closed-form theorem like cycle 370). α'.5.2.1: ~80–120 LOC (def + dispatch placeholder + calibration). α'.5.2.2+: ~250–400 LOC per witness (mirror cycle 491/492/493/494). Total Phase α'.5.2: ~1500–3000 LOC over 7–12 cycles. |
| §8 | **Risk inventory.** R1: cycle 384/491-style "kernel surprise" — k=4 cross-terms may introduce new tree shapes not yet in the calibration matrix (analogous of cycle 384's `mk [vertex, cherry]` discovery). R2: build-cost escalation — Section422.lean's equation-compiler load grows with each `inversePolyTree` arm; the 6th arm may push past usable rebuild times. R3: cycle 365 sorry remains open until k=4 (and possibly k=5+) lands. |
| §9 | **Cycle 499+ entry point.** Specify: cycle 499 ships α'.5.2.0 (empirical `bushy_4` closed form). Mirror cycle 370 template verbatim (3 helpers: `h_dw_bushy_4`, `h_dws_bushy_4`, `h_inv_bushy_4`; final `h_sum` step; non-vacuity on `⟦explicitEuler⟧` evaluating to `1`). LOC budget ~150–250. **Concrete recipe**: at `(t₁,t₂,t₃,t₄) = (v,v,v,v)` with `inv_v = -v`, all four child-factors are identical `(-v + Aᵢ)`. The per-row product is `(-v + Aᵢ)⁴ = Aᵢ⁴ - 4v·Aᵢ³ + 6v²·Aᵢ² - 4v³·Aᵢ + v⁴`. Summing against `bᵢ`: `Σ bᵢ · Aᵢ⁴ = Φ_η(bushy_4)` (kernel name TBD; check cycle 370 for `bushy = mk [v,v,v]` and extrapolate). The four sub-terms collapse to known kernels (`bushy`, `broom₃`, `cherry`, `vertex`). After the outer `−` prefix from `_inv_mk`, the closed form is `v⁵ − 4v³·c + 6v²·b' − 4v·bu − Φ_η(bushy_4)` (or similar — derive carefully). |
| §10 | **What this doc does NOT do.** Does not ship any Lean code. Does not attempt the cycle 365 sorry closure. Does not pivot to a fresh entity. Does not modify cycle 497's Phase γ deliverable. |
| §11 | **Cross-references.** Link to: cycle 402 scoping doc (`def_422B_phase_alpha_prime_5_scoping.md`), cycle 495 scoping doc (`def_422B_phase_beta_gamma_scoping.md`), cycle 497 task results, cycle 358 `_inv_mk` formula, cycles 370/387/399's per-arity templates, cycle 384's kernel-surprise precedent. |

### §C.2 Required Lean prep (zero code, but verification)

Before writing the doc body, **verify these claims by reading the
referenced Lean code**:

1. `OpenMath/Chapter4/Section422.lean:582` — confirm cycle 358's
   `elementaryWeightQ_phi_inv_mk` formula matches the §3 derivation.

2. `OpenMath/Chapter4/Section422.lean:9718–9738` (approx) — locate
   `inversePolyTree`'s 5-arm match. Note exact line numbers for the
   k = 3 arm and the catch-all. **These will need to change in
   cycle 499+ work, so doc must reference precise line numbers.**

3. `OpenMath/Chapter4/Section422.lean:3011–3168` (approx) — read
   cycle 370's `elementaryWeightQ_phi_inv_bushy` proof structure
   (closed form + helpers `h_dw_bushy`, `h_dws_bushy`, `h_sum`,
   non-vacuity at `⟦explicitEuler⟧`). The α'.5.2.0 cycle 499 ship
   will mirror this exactly with the 4-leaf analog.

4. `OpenMath/Chapter4/Section422.lean:9588–9684` (approx) — read
   cycle 399's `trichildCrossTerm` + `trichildPolynomial` definitions
   for the k = 3 template that α'.5.2.1's cycle 500 ship mirrors.

5. `.prover-state/issues/def_422B_phase_alpha_prime_5_scoping.md`
   §3 / §4 (full file) — the cycle 402 scoping that established the
   k = 3 design. Cycle 498's new scoping doc should follow the same
   structural template.

These reads should take ~30 minutes total; the doc body is then ~2
hours of writing.

## §D What NOT to attempt

* **Do NOT ship Lean code this cycle.** The cycle 402 / 495
  precedents are explicit: scoping cycles are markdown-only. Adding
  Lean code on top of a scoping doc historically dilutes the doc's
  utility and is scored as cycle scope-creep.

* **Do NOT attempt to close the cycle 365 sorry.** Per cycle 497's
  R6.B finding, this requires Phase α'.5.2/3 to land first. Multi-
  cycle work.

* **Do NOT attempt Phase β.2** (the cycle 495 scoping doc's plan).
  R6.B falsity makes it structurally impossible.

* **Do NOT attempt to write a `bushy_4` closed-form theorem.**
  That's cycle 499's α'.5.2.0 deliverable. Reading cycle 370 is OK
  for scoping; deriving the kernels is fine for §3/§9; *writing
  Lean code* is not.

* **Do NOT pivot to a fresh entity** (def:451A, def:442A, etc.).
  The §422 cluster's strategic momentum is unbroken; cycle 365's
  closure within 7–12 cycles via Phase α'.5.2/3 is a tangible
  endpoint, and pivoting now would lose that compounding.

* **Do NOT attempt to extend `inversePolyTree`'s arms unilaterally.**
  Without the scoping doc establishing the `tetrachildPolynomial`
  shape first, any Lean ship risks the wrong recursion structure.
  Wait for cycle 500.

* **Do NOT submit anything to Aristotle.** Scoping work has no
  Aristotle target; submissions on multi-cycle infrastructure
  consistently stall (cf. cycle 141's 24h cancellation of the
  thm:550A general-n attempt, cycle 151's 89h cancellation).

* **Do NOT modify `OpenMath/Chapter4/Section422.lean`.** This is a
  doc-only cycle. The file should not appear in `git diff` for this
  cycle.

* **Do NOT modify `extraction/formalization_data/lean_status.json`
  for def:422B.** Status remains `partial`; only the
  `cycle_completed_at` field updates (497 → 498).

## §E Concrete file actions

1. **Create** `.prover-state/issues/def_422B_phase_alpha_prime_5_2_scoping.md`
   with §§1–11 per §C.1 above. Target ~800–1100 LOC of Markdown.

2. **Update** `extraction/formalization_data/lean_status.json`:
   `def:422B` row's `cycle_completed_at` field to 498. Status field
   unchanged (`partial`).

3. **Update** `plan.md`: append cycle 498 closure note to def:422B's
   row, mentioning that cycle 498 is the Phase α'.5.2 scoping ship.
   Mirror cycle 402's `plan.md` update precedent.

4. **Write** `.prover-state/task_results/cycle_498.md` per the
   CLAUDE.md format. Note this is a scoping cycle; deliverable is
   the markdown file from step 1.

5. **Do not commit** until §C.2's Lean reads are completed and the
   doc body is finalized. The cycle 497 worker's notes already
   document R6.B; reference them in the doc rather than rederiving.

## §F Success criteria

* The new doc file exists at the prescribed path and is
  500–1500 LOC.
* §1 cites cycle 497's R6.B finding and the cycle 365 sorry's
  blocked status.
* §3 has the 16-block decomposition fully enumerated.
* §6 has a per-sub-phase cycle plan with at least α'.5.2.0
  through α'.5.2.4 (or equivalent labelling) specified.
* §9 has a concrete cycle 499 entry point with LOC budget and
  proof recipe sketch.
* `lean_status.json`'s def:422B row has `cycle_completed_at: 498`.
* `plan.md` has a cycle 498 closure annotation on the def:422B row.
* Section422.lean is **not** in `git diff` for cycle 498.
* `grep -c sorry OpenMath/Chapter4/Section422.lean` remains 5
  (unchanged from cycle 497).
* No new Lean files created.
* No Aristotle submissions.

## §G Faithfulness check (cycle 498 scoping)

Per CLAUDE.md's "Pre-Commit Faithfulness Checklist":

* **No new `def` introduced** — this is a scoping cycle.
* **No new `structure` introduced.**
* **No new `theorem` introduced.**
* Sorry count unchanged (5 lines, 1 grandfathered code).
* Sole deliverable is a planning document.

Faithfulness is trivially satisfied (no formal claims made about
Butcher textbook content).

## §H Cycle 499+ outlook (preview)

Once the scoping doc lands in cycle 498, cycle 499 ships Phase
α'.5.2.0 per §C.1 §9: the `bushy_4 = mk [v,v,v,v]` quotient-level
closed-form theorem (`elementaryWeightQ_phi_inv_bushy_4`),
mirroring cycle 370's `bushy` ship verbatim with one extra
layer of `_dw`/`_dws` infrastructure. ~150–250 LOC, axiom-clean
target.

Cycle 500 ships Phase α'.5.2.1: `tetrachildPolynomial` +
`tetrachildCrossTerm` defs + `inversePolyTree` extension to 6
arms + `inversePolyTree_bushy_4` calibration. ~80–120 LOC.

Cycles 501+ ship Phase α'.5.2.2+ k=4 non-symmetric witnesses
analogous to cycles 491–494's k=3 ladder.

Cycle ~510 (after sufficient k=4 surface): re-attempt Phase β.1
extension to k=4 trees and re-attempt Phase β.2 structural
induction (now no longer R6.B-blocked).

Cycle ~512–515: finally close the cycle 365 grandfathered sorry
via the full Phase β.2 + γ + δ + ε chain.

The §422 streak compounds toward cycle 365's eventual closure.

---

**Bottom line for the worker**: Write the scoping doc. Do not write
Lean. Do not touch Section422.lean. Do not submit to Aristotle.
Follow the §C.1 template, verify against the §C.2 Lean reads, ship
the markdown file plus the three bookkeeping updates (lean_status,
plan, task_results). Cycle 498 should compile clean trivially (no
Lean changes) and should not affect sorry count.
