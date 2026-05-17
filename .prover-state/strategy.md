# Cycle 357 strategy

## §A — Read this first

Cycle 356 closed cleanly. There are **no Aristotle results to
incorporate**, **no sorries in the repo**, and **nothing stuck**. The
worker's task results listed three options for cycle 357:

1. End-to-end BDF3 η witness (low-priority finish, ~15 LOC).
2. Pivot to Phase D.3 scoping (multi-cycle prep, HIGH-VALUE).
3. Pivot to fresh entity (cycles 336–356 are 21 consecutive §422
   cycles — streak-burnout risk).

**The planner picks option 1 as the mandatory P1 + scoping doc as
the recommended P2.** This combination yields a clean axiom-clean
ship plus high-value forward-progress prep, while keeping the cycle
budget under control. Rationale:

* P1 (BDF3 η) is a guaranteed clean 15-LOC win that completes the
  5-LMM × 3-theorem consumer matrix.
* P2 (Phase D.3 scoping) is markdown-only and unblocks the next
  substantive `def:422B` advance.
* If P1 + P2 both close, that's a 2-deliverable cycle. If P2 stalls,
  P1 alone meets the "shipped axiom-clean content" bar.

A **pivot to a fresh entity** is held in reserve for cycle 358+,
*after* the Phase D.3 scoping document quantifies the remaining
§422 multi-cycle work.

## §B — P1 (mandatory): BDF3 end-to-end η(τ) = 1 witness

**Target**: complete the 5-LMM × 3-theorem consumer matrix by adding
the missing BDF3 end-to-end η witness, parallel to cycle 356's
implicit-Euler P3 and explicit-Euler P4c examples.

**Numerical computation** (paper-verified before writing Lean):

* `bdf3LMM.α = (-1, 18/11, -9/11, 2/11)`,
  `bdf3LMM.β = (6/11, 0, 0, 0)`.
* `sum_β = ∑ᵢ M.β i = 6/11 + 0 + 0 + 0 = 6/11`.
* `coef_α = 1·(18/11) + 2·(-9/11) + 3·(2/11) = 18/11 - 18/11 + 6/11
  = 6/11`.
* `coef_β = 0·(6/11) + 1·0 + 2·0 + 3·0 = 0`.
* `coef_α + coef_β = 6/11 + 0 = 6/11`.
* **η(τ) = sum_β / (coef_α + coef_β) = (6/11) / (6/11) = 1**.

Same η(τ) numerical conclusion as implicit Euler (cycle 356 P3) and
BDF2 (cycle 355) — but with **different intermediate values**
(BDF3's `sum_β = 6/11` and `coef_α = 6/11` are unique among the
5-LMM matrix; cf. BDF2's `sum_β = 2/3, coef_α = 2/3`). This is a
genuine non-vacuity ship, not a duplicate.

**Lean signature** (anonymous `example`):

```lean
/-- *Non-vacuity for the cycle 350 weakened ship at BDF3:* end-to-end
exercise of `Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened`
on BDF3, discharging the weakened non-vanishing hypothesis via
`bdf3LMM_coef_α_plus_coef_β_ne_zero` (cycle 355). The underlying-
one-step-method `η ∈ G₁` corresponding to BDF3 pins
`η(τ) = (6/11) / (6/11) = 1`. Completes the 5-LMM × 3-theorem
consumer-witness matrix
{explicitEulerLMM, implicitEulerLMM, trapezoidalLMM, bdf2LMM, bdf3LMM}
× {sum_β_pos, coef_α_plus_coef_β_ne_zero, Eq422a_at_vertex_eta_eq}. -/
example (η_q : Quotient PhiEquivalent.setoidSigma)
    (hEq : Eq422a OpenMath.Chapter4.Section451.bdf3LMM η_q) :
    elementaryWeightQ_phi η_q RootedTree.vertex = 1 := by
  have h := Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened
    OpenMath.Chapter4.Section451.bdf3LMM
    (by norm_num : (0 : ℕ) < 3)
    OpenMath.Chapter4.Section451.bdf3LMM_isStable
    OpenMath.Chapter4.Section451.bdf3LMM_isPreconsistent
    bdf3LMM_coef_α_plus_coef_β_ne_zero
    hEq
  rw [h]
  simp [OpenMath.Chapter4.Section451.bdf3LMM,
    Fin.sum_univ_three, Fin.sum_univ_four]
  norm_num
```

**Placement**: append at end of `OpenMath/Chapter4/Section422.lean`,
immediately after the BDF2 η witness (around line 1264 in HEAD per
cycle 356's last block). Mirror the docstring style of cycle 356's
P3 and P4c.

**Prerequisites verified at HEAD** (`grep` against the actual
codebase, cycle 357 entry):

| Symbol | Source | Status |
|---|---|---|
| `bdf3LMM` | Section451.lean:161 | ✓ shipped cycle 353 |
| `bdf3LMM_isStable` | Section451.lean:441 | ✓ shipped cycle 354 |
| `bdf3LMM_isPreconsistent` | Section451.lean:177 | ✓ shipped cycle 353 |
| `bdf3LMM_coef_α_plus_coef_β_ne_zero` | Section422.lean:1201 | ✓ shipped cycle 355 |
| `Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened` | Section422.lean (cycle 350) | ✓ |

**Tactic recipe**: copy cycle 356's `bdf2LMM` P3 example verbatim
and adapt:
1. Swap `bdf2LMM` → `bdf3LMM` everywhere.
2. Update `(0 : ℕ) < 1` → `(0 : ℕ) < 3` (BDF3 has `k = 3`).
3. Update `Fin.sum_univ_two` → `Fin.sum_univ_three, Fin.sum_univ_four`
   (BDF3's α-sum is over `Fin 3` and β-sum over `Fin 4`).
4. Verify `norm_num` closes the arithmetic
   `(6/11 + 0 + 0 + 0) / (6/11 + 0 + 0 + 0 + 0) = 1`.

**Possible mid-cycle linter adjustment** (per cycle 356's discovery
note): the canonical `simp [<LMM>, Fin.sum_univ_three,
Fin.sum_univ_four]; norm_num` recipe may be over-provisioned. BDF3's
β = (6/11, 0, 0, 0) has three vanishing entries, so the β-sum may
collapse before all `Fin.sum_univ_*` unfolds fire. Draft with the
full recipe, then drop linter-flagged args until silent.

**Estimated LOC**: ~15 LOC (one anonymous `example` + multi-line
docstring matching cycle 356's style).

**Axiom-clean target**: `[propext, Classical.choice, Quot.sound]`
only. (Anonymous `example`s can't be queried via `#print axioms`
directly; promote to a named `theorem` if axiom verification is
desired, mirroring cycle 356's pattern of naming the
`coef_α_plus_coef_β_ne_zero` witnesses but leaving the end-to-end
exercises anonymous.)

## §C — P2 (recommended): Phase D.3 scoping document

**Target**: write
`.prover-state/issues/def_422B_phase_D_3_scoping.md` (markdown only,
no Lean code). This is the next substantive `def:422B` step per
`def_422B_path.md` §5, currently blocking Phase E sealing.

**Why now**: cycles 336–356 have closed Phase 0 (wire-up) through
Phase D′.2.1 (consumer matrix). The next forward step is the
inductive-step linear-equation solver for `r(t) ≥ 2` trees in the
`underlyingOneStepMethod_aux : RootedTree → ℝ` recursion. This is
**genuinely multi-cycle work** that the cycle 200/201 (`thm:381H`)
and cycle 149/150 (`def:530B`) rollback precedents require be
phase-decomposed in a scoping doc *before* any worker writes Lean.

**Scoping doc contents** (~200 LOC markdown, follow the
`def_422B_path.md` and `lem_310B_plan.md` template):

* **§1 Textbook source**: read `extraction/raw_text/ch04.txt` §422
  in full and identify Butcher's inductive construction of η on
  trees of order ≥ 2. The textbook says η is "determined inductively
  on the order of trees" — pin down whether this is structural
  induction on `RootedTree.order` (cycle 343 already shipped the
  `WellFoundedRelation`) or something more subtle.
* **§2 Distilled mathematical content**: at a tree `t = mk
  children`, the Eq422a equation reduces to a linear equation in
  `η(t)`. The coefficient of `η(t)` is a function of `M.α, M.β` and
  the children-η values (already determined by the IH).
* **§3 Project-hook inventory**: cite cycle 343's
  `RootedTree.WellFoundedRelation` instance + cycle 341's
  per-tree elementary-weight machinery + cycle 342's base-case
  closed form for `η(τ)`. Verify cycle 350's
  `Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened` template
  for the τ case generalizes to higher orders.
* **§4 Gap inventory**: identify what's missing. Likely candidates:
  (a) closed-form expansion of `elementaryWeightQ_phi η_q t` at
  arbitrary `t` in terms of children-values and `M`'s `α, β` (cycle
  341 only proved τ-additivity, not full multiplicativity);
  (b) the recursive substitution proving the residual equation in
  `η(t)` is linear, not transcendental;
  (c) proof that the linear coefficient is non-zero under stability
  + preconsistency at every `t` (analog of cycle 344's `coef_α > 0`
  but at the per-tree level).
* **§5 Phase decomposition**: 3–4 sub-phases at ~1 cycle each:
  Phase D.3.a (per-tree elementary-weight expansion lemma),
  Phase D.3.b (linear coefficient extraction at `t = mk children`),
  Phase D.3.c (non-vanishing under stable + preconsistent),
  Phase D.3.d (the `noncomputable def underlyingOneStepMethod_aux`
  recursion + spec lemma).
* **§6 Risk assessment**: per-phase LOC budgets, Mathlib hook
  confidence, Aristotle suitability. Flag the σ-faithfulness gap if
  it surfaces (per `symmetry_group_equivalence.md`).
* **§7 Cycle 358+ entry point**: concrete first task for cycle 358.

**Estimated time**: 60–90 min, markdown only. **Sorry impact**: 0.

**If P2 stalls**: ship P1 alone and defer P2 to cycle 358 as a
standalone scoping cycle (matching the cycle 348 precedent for Phase
D′ Step 2 scoping).

## §D — What NOT to attempt this cycle

Each of these would burn cycle budget for no axiom-clean ship.

1. **Do NOT attempt the full Phase D.3 implementation in cycle 357.**
   Per the cycle 149/150 and cycle 200/201 rollback precedents,
   sorry-first multi-cycle scaffolds with no credible single-cycle
   close get rolled back. The cycle 357 worker must NOT write a
   `noncomputable def underlyingOneStepMethod_aux` with `sorry`
   bodies; that would mirror the cycle 149 mistake.

2. **Do NOT attempt Phase D′.2.2 Step 2** (the unconditional
   `0 ≤ coef_β` derivation from `IsStable + IsConsistent` alone).
   Per `eq422a_eta_phase_D_prime_step_2_scoping.md` §1, the textbook
   does **not** provide a direct lemma of this form. Routes A
   (template port), B (404b alone), and C (boundary locus) are all
   ruled out. Route D requires `0 ≤ Σᵢ i²·αᵢ` infrastructure which
   is not in Mathlib at HEAD. Multi-cycle; not a cycle 357 target.

3. **Do NOT pivot to a fresh entity yet.** Phase D.3 scoping (P2)
   is higher-value because it sets up the next §422 advance. A
   pivot at cycle 358+ is more strategically sound once the scoping
   doc has clarified what's left in §422.

4. **Do NOT extend the consumer-witness matrix beyond 5 LMMs.**
   Cycle 356's 5-LMM × 2-theorem matrix is saturated for the
   canonical LMMs in the codebase. Adding a 6th LMM
   (e.g. Adams-Bashforth-2) would require shipping a new
   `LinearMultistepMethod 2` definition + stability/consistency
   witnesses *first*; that's a multi-cycle infrastructure ship, not
   a consumer-matrix extension.

5. **Do NOT attempt the cycle 351 worker's continuation of Phase
   D′.2.2 Route D Step 2** (i.e. the `0 ≤ Σᵢ i²·αᵢ` infrastructure
   itself). Cycle 351 shipped Step 1 (`coef_β = (1/2)·Σᵢ i²·αᵢ`
   under order ≥ 2); Step 2 is blocked on either §441 Möbius
   infrastructure or a fresh second-derivative-of-ρ argument. The
   issue file lists this as multi-cycle.

6. **Do NOT touch `OpenMath/Chapter4/Section441.lean`.** Per
   `cycle_182_gpfs_slowness.md`, Section441 is at 43+ consecutive
   GPFS-blocked compile timeouts. Cycle 357's deliverables live in
   Section422 (BDF3 example) and `.prover-state/issues/` (Phase D.3
   scoping doc). No Section441 recompile required.

7. **Do NOT modify `scripts/autonomous_loop.py`.** Loop-maintainer
   territory per `tautology_scanner_false_positives.md` §D3. If
   cycle 357's supervisor flags false positives (cycle 356 did not,
   but watch for the cycle 243–247 pattern), record the false-alarm
   pattern in this strategy file's task results and move on.

8. **Do NOT raise `maxHeartbeats` above 200000.** Per `CLAUDE.md`;
   the BDF3 example's `simp + norm_num` arithmetic is well within
   default limits (BDF2 trapezoidal precedent at ~5s warm rebuild).

9. **Do NOT introduce `axiom`/`constant`.** Per `CLAUDE.md`. The
   BDF3 η witness is a mechanical composition of existing
   axiom-clean infrastructure; no new axioms required.

10. **Do NOT attempt to close any open issue from
    `.prover-state/issues/`.** All open issues (`def_422B_path.md`,
    `eq422a_eta_phase_D_prime_step_2_scoping.md`,
    `lem_310B_plan.md`, `cycle_336_pivot_options.md`,
    `cycle_182_gpfs_slowness.md`, etc.) are either multi-cycle
    forward-progress targets or maintainer-territory escalations.
    Cycle 357 ships forward (P1) and plans forward (P2); it does
    not retroactively close blockers.

## §E — Ship checklist for cycle 357

After both P1 and P2 land (or P1 alone, if P2 stalls):

1. ✅ `OpenMath/Chapter4/Section422.lean` contains the new BDF3
   end-to-end η example (P1). File grows ~1576 → ~1595 LOC.
2. ✅ `lake env lean OpenMath/Chapter4/Section422.lean` exits 0
   (clean build).
3. ✅ Sorry count in Section422 remains 0 (verified by
   `grep -c sorry OpenMath/Chapter4/Section422.lean`).
4. ✅ Cycle 356 axiom-clean named theorems (e.g.
   `implicitEulerLMM_coef_α_plus_coef_β_ne_zero`,
   `explicitEulerLMM_coef_α_plus_coef_β_ne_zero`) still build clean
   (verify via the same `lake env lean` invocation).
5. ✅ Tautology-scanner regex
   `:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$` on the new
   example shows 0 hits. (Cycle 356's P1–P4c had 0 hits; cycle 357
   should match.)
6. ✅ `.prover-state/issues/def_422B_phase_D_3_scoping.md` exists
   (P2), ~200 LOC, with the §1–§7 structure above. (Skip if P2
   stalls.)
7. ✅ `.prover-state/task_results/cycle_357.md` follows the standard
   format: Worked on / Approach / Result / Faithfulness check /
   Dead ends / Discovery / Suggested next approach.
8. ✅ `lean_status.json` row for `def:422B` may be bumped from cycle
   356 to 357 in the cycle reference (status remains `partial` —
   Phase D.3 is not closed by P2 scoping alone).
9. ✅ `plan.md` def:422B row updated with a cycle 357 note in the
   trailing paragraph.

Once shipped, commit message format:

```
Cycle 357 — §422 BDF3 η(τ) = 1 consumer witness + Phase D.3 scoping.
```

(or `Cycle 357 — §422 BDF3 η(τ) = 1 consumer witness.` if P2
stalls.) Use `git commit -m "$(cat <<'EOF' ... EOF)"` HEREDOC per
`CLAUDE.md`.

## §F — Cycle 358+ outlook

Depending on P2's content:

* **If P2 lands** (Phase D.3 scoping doc shipped): cycle 358 begins
  Phase D.3.a — the per-tree elementary-weight expansion lemma.
  Concrete entry point per the scoping doc's §7.
* **If P2 stalled**: cycle 358 ships P2 as a standalone scoping
  cycle (markdown only, like cycle 348 for Phase D′ Step 2).
* **Pivot consideration for cycle 359+**: with Phase D.3 scoping in
  hand, the planner can choose between (a) continuing §422 Phase
  D.3.a implementation, or (b) pivoting to a fresh entity such as
  `def:442A` (principal sheet, definition-only), `thm:535A`
  (one-step underlying method for GLMs), or `thm:541A` (DIMSIM
  types). Pivot candidates per `cycle_336_pivot_options.md`. The
  22-cycle §422 streak (336–357) is a reasonable diversification
  trigger by cycle 359.
