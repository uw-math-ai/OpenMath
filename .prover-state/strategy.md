# Cycle 295 Strategy — §342 (342g) Aristotle poll + manual anchor extension

## Status entering cycle 295

Cycle 294 closed the §342 manual track for (342g) at the **empirical
anchor** level. Shipped at commit `421716c`:

* `butcherShiftedLegendre_one_root` — `P_1^*(1/2) = 0 ∧ 1/2 ∈ (0,1)`
  (Section342.lean line 3565).
* `butcherShiftedLegendre_two_roots` — two distinct roots
  `(3 ± √3)/6 ∈ (0,1)` of `P_2^*` (line 3582).
* `butcherShiftedLegendre_card_roots_le n : (P_n^*).roots.toFinset.card ≤ n`
  (line 3632, the upper-bound half of (342g)).
* Aristotle project **`5939f28b-c890-4b7f-be4f-ed0f31f0d0b5`** submitted
  for the **general** (342g) statement. File:
  `.prover-state/aristotle_submissions/cycle_294/342g_zeros.lean`. Status
  at end of cycle 294: `QUEUED`.

§342 close-out tally: (342a) ✓ (342b) ✓ (342c) ✓ (342d) ✓ (342e) ✓
(342f) ✓ — only (342g) remains, with the Aristotle job out and three
small-`n` anchors in hand. Section342.lean = 3641 LOC, 0 sorries,
axiom-clean throughout.

The cycle 294 task results (§"Suggested next approach") prescribe the
exact branching logic below. This strategy follows it verbatim.

## Priority 0 — single Aristotle poll (5 min, mandatory)

Run **exactly once** at the start of the cycle:

```
mcp__aristotle__get_status with project_id = "5939f28b-c890-4b7f-be4f-ed0f31f0d0b5"
```

Per CLAUDE.md ("one check after 30 min is enough; do not poll
repeatedly"), this is the only Aristotle call this cycle. The
submission was at 2026-05-15 22:11:40 UTC; sufficient time has
elapsed for one poll.

Record the returned `progress_percentage` and `status` for the
attempts log and proceed to the appropriate branch below.

## Branch A — Aristotle returned COMPLETE (highest priority)

Trigger: `status = COMPLETE` (or `COMPLETE_WITH_ERRORS`).

### A.1 — Extract and audit the proof (20 min)

1. `mcp__aristotle__extract_result` with `project_id =
   "5939f28b-c890-4b7f-be4f-ed0f31f0d0b5"` to retrieve the proof
   text. The Aristotle submission file cites every closed §342 clause
   as an axiom; the returned proof should reference those axioms
   directly (with names matching the submission file's `axiom`
   declarations — `butcherShiftedLegendre_orthogonal`,
   `butcherShiftedLegendre_norm_sq`, `butcherShiftedLegendre_eval_one`,
   `butcherShiftedLegendre_eval_zero`, `butcherShiftedLegendre_rodrigues`,
   `butcherShiftedLegendre_recurrence`, `butcherShiftedLegendre_natDegree`,
   `butcherShiftedLegendre_orthogonal_to_lower_degree`).
2. If the proof relies on auxiliary helpers Aristotle introduced
   (e.g. a `signChangeSet` extraction or a `Polynomial.roots_card_eq`
   chain), factor those into either inline private helpers in
   `OpenMath/Chapter3/Section342.lean`, or a fresh
   `OpenMath/Chapter3/Section342GZerosHelpers.lean` (mirror cycle
   281's `Section342NormSqHelpers.lean` pattern when helper-LOC
   exceeds ~200).
3. Faithfulness check the textbook target: the headline theorem
   should be a `Finset` of `n` reals in `(0, 1)` (or equivalently
   `(P_n^*).roots.toFinset.card = n ∧ ∀ x ∈ roots.toFinset, x ∈ (0,1)`),
   not a weakened existential. Reject any restatement that drops to
   `∃ S : Finset ℝ, S.card = n ∧ …` without showing it equals
   `roots.toFinset`. Reject any statement parametrised by an extra
   hypothesis not present in Butcher's (342g) (the textbook says
   "for n = 0, 1, 2, …", so all-`n` quantification is the target;
   the `n = 0` case is vacuously fine since `P_0^* = 1` has 0 roots).

### A.2 — Integrate the proof (30 min)

1. Translate Aristotle's `axiom`-cited proof to use the actual Lean
   names (the axioms in the submission file mirror the public
   theorems verbatim, so this should be a search-and-replace if
   names align). The headline theorem name should be something like
   `butcherShiftedLegendre_distinct_real_roots` — keep Aristotle's
   naming if reasonable.
2. Place the public theorem at the bottom of
   `OpenMath/Chapter3/Section342.lean`, after
   `butcherShiftedLegendre_card_roots_le` (line 3632+). Any
   private helpers go immediately before it.
3. Run `lake env lean OpenMath/Chapter3/Section342.lean` to verify.
   Expected: clean exit. If errors fire, fix by simp-set adjustment
   or one-line rewrites — do NOT attempt structural changes to the
   proof.
4. Run axiom check: `#print axioms` on the new headline theorem
   should return `[propext, Classical.choice, Quot.sound]`.
   `Classical.choice` is acceptable (orbit/sign-change arguments
   often route through it).

### A.3 — Update bookkeeping (10 min)

1. `extraction/formalization_data/lean_status.json`: `lem:342A` row
   `partial` → `formalized`. Bump `cycle` to 295. Update
   `lean_symbol` to point at the headline (342g) theorem name.
2. `plan.md`: `lem:342A` row `[~]` → `[x]`. Append cycle 295
   closure note covering all 7 properties (342a)–(342g).
3. Update progress counter (71 → 72 of 175).
4. Append closure note to
   `.prover-state/issues/lem_342A_g_zeros_scoping.md`: "Aristotle
   project `5939f28b-…` returned COMPLETE in cycle 295; (342g)
   closed via [proof technique]. `lem:342A` fully formalised."

## Branch B — Aristotle IN_PROGRESS with healthy progress (likely)

Trigger: `status = IN_PROGRESS` AND (`progress_percentage` shows any
non-zero growth since cycle 294's QUEUED state, OR is ≥ 10%).

This is the **expected** branch for cycle 295: cycle 281's (342d)
returned COMPLETE only after ~14 cycles. Cycle 277's (342a) took 6
cycles. One cycle is too soon to expect (342g) closure.

### B.1 — Continue Aristotle (do nothing further with the project) (0 min)

Leave `5939f28b-…` running. NO resubmission, NO cancellation, NO
second poll this cycle. Cycle 296+ will check again.

### B.2 — Ship one more empirical anchor: `n = 3` zeros (60 min)

The natural next manual anchor per the cycle 294 task results
"Branch B" guidance. Target:

```lean
theorem butcherShiftedLegendre_three_roots :
    ∃ x₁ x₂ x₃ : ℝ,
      x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₂ ≠ x₃ ∧
      x₁ ∈ Set.Ioo (0:ℝ) 1 ∧
      x₂ ∈ Set.Ioo (0:ℝ) 1 ∧
      x₃ ∈ Set.Ioo (0:ℝ) 1 ∧
      (butcherShiftedLegendre 3).eval x₁ = 0 ∧
      (butcherShiftedLegendre 3).eval x₂ = 0 ∧
      (butcherShiftedLegendre 3).eval x₃ = 0
```

**Strategy**: NOT closed-form (cubic-formula nested radicals are out
of scope per the cycle 294 abort list). Instead, **use IVT on the
cubic** `P_3^*(x) = 20x³ - 30x² + 12x - 1` (cycle 273's
`butcherShiftedLegendre_three`):

* `P_3^*(0) = -1 < 0` (via cycle 273's `butcherShiftedLegendre_eval_zero`
  at `n = 3`: `(-1)^3 = -1`).
* `P_3^*(1) = 1 > 0` (via cycle 271's `butcherShiftedLegendre_eval_one`).
* By parity (342c, cycle 272's `butcherShiftedLegendre_eval_one_sub`),
  at `x = 1/2`: `(P_3^*).eval (1 - 1/2) = (-1)^3 · (P_3^*).eval (1/2)`,
  i.e. `(P_3^*).eval (1/2) = -(P_3^*).eval (1/2)`, hence
  `2 · (P_3^*).eval (1/2) = 0`, so `(P_3^*).eval (1/2) = 0`.
  **That gives the middle root.**
* For the other two: compute `(P_3^*).eval (1/5)` and
  `(P_3^*).eval (4/5)` explicitly via cycle-273's closed form +
  `simp [eval_*]` + `norm_num`. Paper-verify signs:
  - `P_3^*(1/5) = 20·(1/125) - 30·(1/25) + 12·(1/5) - 1 =
    4/25 - 6/5 + 12/5 - 1 = 4/25 + 6/5 - 1 = 4/25 + 30/25 - 25/25 = 9/25 > 0`.
  - `P_3^*(4/5) = 20·(64/125) - 30·(16/25) + 12·(4/5) - 1 =
    256/25 - 96/5 + 48/5 - 1 = 256/25 - 48/5 - 1 = 256/25 - 240/25 - 25/25 = -9/25 < 0`.
* IVT on `[0, 1/5]` (continuity from `Polynomial.continuous`, sign
  flip from -1 to 9/25) ⇒ root in `(0, 1/5)`.
* IVT on `[4/5, 1]` (sign flip from -9/25 to 1) ⇒ root in `(4/5, 1)`.

**Recipe in Lean**:
1. `have hP3_eval_0 : (P_3^*).eval 0 = -1` from
   `butcherShiftedLegendre_eval_zero 3` + `pow_succ + neg_one_sq + simp` or
   `simp; norm_num`.
2. `have hP3_eval_1 : (P_3^*).eval 1 = 1` from
   `butcherShiftedLegendre_eval_one 3`.
3. `have hP3_eval_half : (P_3^*).eval (1/2) = 0`:
   ```lean
   have h := butcherShiftedLegendre_eval_one_sub 3 (1/2 : ℝ)
   simp at h
   -- h : (P_3^*).eval (1/2) = -(P_3^*).eval (1/2)
   linarith
   ```
4. `have hP3_eval_one_fifth : (P_3^*).eval (1/5) = 9/25` via
   `rw [butcherShiftedLegendre_three]; simp [eval_*]; norm_num`.
   And `have hP3_eval_four_fifths : (P_3^*).eval (4/5) = -9/25`.
5. IVT on `[0, 1/5]`:
   ```lean
   have hCont : ContinuousOn (fun x => (P_3^*).eval x) (Set.Icc 0 (1/5)) :=
     (Polynomial.continuous _).continuousOn
   -- intermediate_value_Ioo: 0 ∈ open interval between -1 and 9/25
   obtain ⟨x₁, hx₁_mem, hx₁_eval⟩ :=
     intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1/5) hCont ⟨...⟩
   ```
6. Mirror on `[4/5, 1]`.
7. Distinctness: `1/2 ∉ Ioo 0 (1/5)` and `1/2 ∉ Ioo (4/5) 1` by
   `norm_num`-style arithmetic; the two open intervals `(0, 1/5)` and
   `(4/5, 1)` are disjoint so their inhabitants differ.

**Mathlib hooks**:
* `intermediate_value_Ioo` (`Mathlib.Topology.Algebra.Order.IntermediateValue`).
* `Polynomial.continuous` (gives `Continuous _.eval`).
* `Continuous.continuousOn` for the `Icc` lift.

**LOC budget**: ~100–130 LOC. Mostly mechanical arithmetic and IVT
invocations. Aristotle suitability: medium (mechanical).

### B.3 — Optional stretch (only if B.2 closed quickly with time remaining)

Ship the generalised parity helper:

```lean
theorem butcherShiftedLegendre_eval_half_eq_zero_of_odd
    (n : ℕ) (hn : Odd n) :
    (butcherShiftedLegendre n).eval (1/2) = 0 := by
  have h := butcherShiftedLegendre_eval_one_sub n (1/2 : ℝ)
  -- h : (P_n^*).eval (1 - 1/2) = (-1)^n · (P_n^*).eval (1/2)
  -- Simplify: 1 - 1/2 = 1/2; (-1)^n = -1 when n odd
  rw [show (1 : ℝ) - 1/2 = 1/2 from by norm_num] at h
  rw [hn.neg_one_pow] at h
  linarith
```

Reusable helper that proves `P_n^*(1/2) = 0` for ALL odd `n` —
makes future anchors at `n = 5, 7, 9, …` trivial one-liners (the
middle root is automatic).

**LOC budget**: ~10 LOC. Only ship if B.2 takes < 45 min.

## Branch C — Aristotle stalled with no growth (observation 1 of 3)

Trigger: `status = IN_PROGRESS` AND `progress_percentage` shows no
growth since cycle 294's QUEUED state (i.e. still QUEUED or stuck
at 0%).

The three-stall protocol from cycle 285 / cycle 289 (full closure of
(342f) via Branch D pivot) applies.

### C.1 — First stall observation (this cycle): leave running, ship anchor

Do NOT cancel yet. The cycle 285 precedent shows that 0% → 5%
between submission and the first poll is not a true stall (it
takes Aristotle some time to ramp up). Treat this cycle as
observation #1 of 3.

Same deliverable as Branch B.2: ship `butcherShiftedLegendre_three_roots`
via IVT (~100 LOC).

Document the stall in attempts.md ("cycle 295 stall observation #1
of 3 — leave running"). If cycle 296's poll shows still 0% with no
growth, that's observation #2 — and cycle 296+ planner decides
whether to cancel. If cycle 297's poll is the third consecutive
flat observation, the three-stall protocol fires.

### C.2 — Three-stall fire (NOT this cycle; documenting for cycle 297+)

If observation #3 fires in cycle 297:

1. Cancel `5939f28b-…` via `mcp__aristotle__cancel_project`.
2. Open `.prover-state/issues/lem_342A_g_zeros_manual_closure_plan.md`
   (mirror cycle 289's `lem_342A_342f_manual_closure_plan.md`
   structure). The plan would scope manual (342g) closure into 3
   phases:
   * Phase A: `signChangeSet : Polynomial ℝ → Finset ℝ` infrastructure
     (extracting sign-change points; ~80 LOC).
   * Phase B: orthogonality contradiction `(P_n^*) · Q > 0 ∧
     ∫₀¹ P_n^* · Q = 0` where `Q := ∏ᵢ (X − C xᵢ)` (~150 LOC).
   * Phase C: closure (~30 LOC). Total ~5 cycles.

Cycle 295 does NOT execute Branch C.2 — only document it as the
planned escalation path.

## Hard constraints (all branches)

* **One Aristotle poll only.** Per CLAUDE.md. Do not re-poll
  `5939f28b-…` after Priority 0.
* **Sorry count must stay at 0.** No sorry-first scaffolds (per
  cycle 138/139, 149/150, 200/201 rollback precedent). If
  `butcherShiftedLegendre_three_roots` cannot be closed in this
  cycle's budget, abort B.2 and skip; don't leave a sorry behind.
* **No new entity is closed unless §342 (342g) is shipped.** B.2's
  `butcherShiftedLegendre_three_roots` is an *anchor*, not a new
  textbook entity — do NOT update `lean_status.json` or `plan.md`
  row for `lem:342A` based on B.2 alone. Branch A is the only
  branch that touches the entity status.
* **No `axiom`/`constant` declarations** anywhere.
* **No `maxHeartbeats` increase**.
* **No `lean_status.json` `formalized` claim for `lem:342A` until
  Aristotle returns** (Branch A) **or until a full manual closure
  ships** (Branch C.2 multi-cycle).
* **`Section441.lean` smoke test**: do NOT attempt. 43+ consecutive
  GPFS timeouts since cycle 182 per
  `.prover-state/issues/cycle_182_gpfs_slowness.md`. Section441
  Phase C.2 work remains permanently deferred at the smoke-test
  level for cycles 295+.

## What NOT to try (explicit failures from prior cycles)

* **Do NOT submit a new Aristotle job for (342g) this cycle.** The
  existing `5939f28b-…` job has not finished its first cycle —
  resubmission would waste the slot. Resubmission only fires on
  three-stall confirmation (Branch C.2, cycle 297+).
* **Do NOT attempt closed-form `n = 3` zeros via cubic formula.**
  The exact roots `(3 ± √(3 - √(?))) / something` involve nested
  radicals from Cardano's formula; cycle 294 strategy abort list
  explicitly excludes this. IVT (Branch B.2 / C.1) is the right
  approach.
* **Do NOT attempt `n = 3` via direct factorisation of the cubic
  `20x³ - 30x² + 12x - 1` into `(2x - 1)(10x² - 10x + 1)`.** The
  quadratic factor has roots `(5 ± √15)/10`, which involves `√15`
  (not the `√3` of (342f) cycle-282/277 witnesses). Doable but uglier
  than IVT and adds `Real.sqrt` arithmetic that's avoidable.
* **Do NOT extend the (342f) recurrence ladder past `n = 11`.** Per
  cycle 285's three-stall protocol and the cycle 294 task results,
  the empirical base at `n ∈ {2..11}` is sufficient. (342f) is
  closed at cycle 293; further ladder rungs add no value.
* **Do NOT modify cycles 271–293's (342a)–(342f) closed theorems.**
  They are axiom-clean and referenced by the Aristotle submission.
* **Do NOT modify `scripts/autonomous_loop.py`.** Per CLAUDE.md.
* **Do NOT introduce new tree-related entities, RKTableau entities,
  GLM entities, or other Chapter 3/4/5 work this cycle.** Focus
  exclusively on §342 (342g) closure.
* **Do NOT pivot to a fresh entity.** §342 is the active cluster.
  Even on Branch B/C.1, the cycle deliverable is a §342 anchor
  (Branch B.2's `butcherShiftedLegendre_three_roots`), not a new
  entity from Chapter 3 §31x / §35x / §38x.

## Sequencing summary

```
Step 0 (5 min):  Single Aristotle poll on 5939f28b-…
Step 1 (5 min):  Determine branch (A / B / C.1)
Step 2 (varies): Execute branch.
    A: ~60 min total (extract + integrate + bookkeeping)
    B / C.1: ~60–90 min for butcherShiftedLegendre_three_roots
             (+ ~10 min stretch helper if B.3 fires)
Step 3 (15 min): Write task_results/cycle_295.md
Step 4 (10 min): Commit + push
```

Maximum cycle budget: ~90–135 min. The branching is designed so
that **the cycle ships a measurable deliverable in every branch**:
* Branch A: full (342g) + `lem:342A` closure (the BIG win — closes
  the entire `lem:342A` for the first time, all 7 clauses).
* Branch B / C.1: one more `n = 3` empirical anchor (and document
  the Aristotle status); optional `Odd n → P_n^*(1/2) = 0` helper.

A cycle with zero changes is unacceptable per CLAUDE.md, but every
branch above guarantees ≥1 named theorem shipped.

## Cycle 295 entry point

1. **Run Priority 0** (the single Aristotle poll).
2. **Branch on result** per §A/§B/§C.1.
3. **Ship**.
4. **Update task_results + commit**.

Cycle 296+ planner will use the Aristotle status reported in cycle
295's task results to decide the next branching (continued poll,
three-stall fire, or post-closure pivot to `lem:342B`).
