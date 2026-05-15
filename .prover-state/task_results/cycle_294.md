# Cycle 294 Results

## Worked on

§342 (342g) — `P_n^*` has `n` distinct real zeros in `(0, 1)`.
Per the cycle-294 strategy (measured cycle, not capstone), shipped:

1. **§B (fire-and-forget)**: submitted (342g) target to Aristotle as
   project `5939f28b-c890-4b7f-be4f-ed0f31f0d0b5`. Submission file:
   `.prover-state/aristotle_submissions/cycle_294/342g_zeros.lean`.
   Cites every closed §342 clause (342a)–(342f) plus the cycle-292
   `butcherShiftedLegendre_orthogonal_to_lower_degree` basis-span
   lemma. Single-poll discipline: cycle 295 polls once.
2. **§C P2.1**: `butcherShiftedLegendre_one_root` —
   `P_1^*(1/2) = 0 ∧ 1/2 ∈ Set.Ioo 0 1`.
3. **§C P2.2**: `butcherShiftedLegendre_two_roots` — existence of
   two distinct roots `(3 ± √3)/6 ∈ (0, 1)` of `P_2^*`.
4. **§D P3**: `butcherShiftedLegendre_card_roots_le` — upper-bound
   half of (342g): `(P_n^*).roots.toFinset.card ≤ n` for every `n`.

P2.3 (n = 3 zeros) was explicitly out of scope per the strategy
abort list — closed-form cubic roots involve cubic-formula nested
radicals.

## Approach

* **§B**: built the Aristotle file pattern after cycle 273/277/281
  examples. Loaded all closed §342 clauses as `axiom` statements (full
  forms, not just signatures, so Aristotle sees the exact integral
  form `intervalIntegral ∫ x in (0:ℝ)..1, …`). Strategy hint in the
  docstring describes the textbook contradiction via sign-change
  pairing on `Q := ∏ᵢ (X − C xᵢ)`. Submitted via
  `mcp__aristotle__submit_file`.
* **§C P2.1**: `refine ⟨?_, ?_⟩`; eval branch reduces to
  `simp [eval_sub, eval_mul, eval_C, eval_X]` on
  `butcherShiftedLegendre_one`; membership branch closes with
  `simp [Set.mem_Ioo]; norm_num`. The `norm_num` after `simp` on the
  eval was redundant (`simp` already closed the goal) — initial
  compile flagged "No goals to be solved"; removed and the proof
  ships clean.
* **§C P2.2**: standard √3 toolkit — `Real.sqrt_pos.mpr`,
  `Real.sq_sqrt` for `(√3)² = 3`. Derived `√3 < 2` via
  `nlinarith [hsqrt3_sq, hsqrt3_nonneg]` instead of going through
  `Real.sqrt_four`. Membership in `(0, 1)`: each bound is a linear
  consequence of `√3 ∈ (0, 3)` (since `(√3)² = 3 < 9 = 3²`). Eval=0:
  `simp only [Polynomial.eval_*]` then `nlinarith [hsqrt3_sq]`
  closes both root cases in one shot (the residue `(3 ± √3)² = 12 ± 6√3`
  arithmetic is a quadratic in `√3` which `nlinarith` dispatches
  using the `(√3)² = 3` fact).
* **§D P3**: clean three-step `calc`. The crucial Mathlib name is
  `Polynomial.card_roots'` (not `card_roots'_le_natDegree` — the
  primed form is the multiset-card statement
  `Multiset.card p.roots ≤ natDegree p`). Combined with cycle 273's
  `butcherShiftedLegendre_natDegree` and `Multiset.toFinset_card_le`.

## Result

**SUCCESS** — all three new theorems are axiom-clean
(`[propext, Classical.choice, Quot.sound]`). The Aristotle submission
is `QUEUED` (single-poll deferred to cycle 295). `lake env lean
OpenMath/Chapter3/Section342.lean` exits 0 (warnings unchanged from
HEAD). `lake build OpenMath.Chapter3.Section342` exits 0.

## Faithfulness check

For each new `theorem` introduced this cycle:

### `butcherShiftedLegendre_one_root`
- Entity ID: `lem:342A` clause (342g) — empirical witness at `n = 1`.
- Textbook statement (Butcher §342, p. 236):
  > `P_n^*` has `n` distinct real zeros in the interval `(0, 1)`,
  > `n = 0, 1, 2, …`. (342g)
- This cycle's Lean statement: `(P_1^*).eval (1/2) = 0 ∧ 1/2 ∈ Ioo 0 1`.
  This is a concrete witness for `n = 1` (one distinct root `1/2 ∈ (0,1)`),
  not the full (342g). Documented as an *empirical anchor* per the
  cycle 294 strategy §C P2.1. **Weaker** than the textbook statement
  (it only addresses `n = 1`, not all `n`). The general statement is
  the Aristotle target.

### `butcherShiftedLegendre_two_roots`
- Entity ID: `lem:342A` clause (342g) — empirical witness at `n = 2`.
- Lean statement: existence of `x₁ ≠ x₂` both in `Ioo 0 1` with
  `P_2^*.eval xᵢ = 0`. Concrete witness for `n = 2`; **weaker** than
  the textbook statement (only `n = 2`, not all `n`). The witnesses
  `(3 ± √3)/6` match the closed-form quadratic roots of `6X² − 6X + 1`.

### `butcherShiftedLegendre_card_roots_le`
- Entity ID: `lem:342A` clause (342g) — upper-bound half.
- Textbook statement implies both `≥ n` and `≤ n` zero counts; the
  `≤ n` direction is what this theorem captures
  (`(P_n^*).roots.toFinset.card ≤ n`). **Weaker** than the textbook
  statement (it does not show the zeros are in `(0, 1)` and does not
  give the lower bound). Justification: this is the easy half via
  the general `Polynomial.card_roots'` bound combined with cycle
  273's `natDegree = n`; the harder lower bound `≥ n` zeros in
  `(0, 1)` is the (342g) Aristotle target. This is intentional per
  strategy §D and the scoping doc.

### Definition smuggling check
No new `def` or `structure` was introduced. All three new theorems
are `theorem` statements about the existing
`butcherShiftedLegendre` definition (which already passed faithfulness
in cycle 271).

### Tautology / identity / hypothesis-strength checks
- No theorem conclusion appears verbatim as one of its own
  hypotheses (P2.1/P2.2/P3 are all unconditional except P3 has the
  trivial `(n : ℕ)` index — no actual hypothesis).
- No `exact h_…` or `:= id` proof shortcuts. P2.1 ends with `simp` /
  `norm_num`; P2.2 ends with `nlinarith`; P3 ends with the
  `butcherShiftedLegendre_natDegree` chain.
- No hypotheses introduced beyond the textbook (P2.1 / P2.2 have no
  hypotheses; P3 has the trivial `n : ℕ`).
- No absent-theorem promises — the in-file docstring header for the
  (342g) section names exactly the three theorems shipped.

## Dead ends

* Initial P2.1 proof had `simp [...]; norm_num` on the eval branch;
  `simp` already closes the goal so `norm_num` errored with "No
  goals to be solved". Dropped the redundant `norm_num`.
* Considered using `Real.sqrt_lt_sqrt` + `Real.sqrt_four` for the
  `√3 < 2` bound but `nlinarith [hsqrt3_sq, hsqrt3_nonneg]` worked
  directly — no need for the chain.
* Originally drafted P3 with the alias `card_roots'_le_natDegree`
  per the strategy hint; the actual Mathlib name (at HEAD in
  `Mathlib/Algebra/Polynomial/Roots.lean:79`) is
  `Polynomial.card_roots' : Multiset.card p.roots ≤ natDegree p`.
  The `'`-suffixed name is the natDegree version; the unprimed
  `card_roots` is the `WithBot ℕ` degree version.

## Discovery

* **`Polynomial.card_roots'` naming**: the natDegree-form upper bound
  is `Polynomial.card_roots'` (multiset cardinality version), not
  `card_roots'_le_natDegree`. The strategy doc's hint was slightly
  off but the path was clear from the Mathlib grep.
* **`simp` + `norm_num` redundancy**: `simp [eval_sub, eval_mul,
  eval_C, eval_X]` on `(2x - 1) at x = 1/2` directly computes the
  result; no `norm_num` chaser needed.
* **`nlinarith` + `(√3)² = 3` is robust**: both quadratic-residue
  eval-at-root subgoals close in one `nlinarith [hsqrt3_sq]` call
  each, well within the abort threshold.
* The **scoping doc was load-bearing**: having a documented strategy
  for (342g) (`.prover-state/issues/lem_342A_g_zeros_scoping.md`)
  meant the Aristotle submission file came together quickly with the
  full prerequisite axiom list.

## Suggested next approach

**Cycle 295**:
* Single-poll Aristotle project `5939f28b-c890-4b7f-be4f-ed0f31f0d0b5`
  for (342g). Apply the standard three-stall protocol per
  CLAUDE.md — if stalled below progress threshold by cycle 297,
  cancel and resubmit with strengthened axiom list (e.g. provide
  sign-change extraction as an axiom).
* **Branch A (Aristotle COMPLETE)**: integrate, update
  `lean_status.json` for `lem:342A` → `formalized`. Then pivot to
  `lem:342B` (Gaussian quadrature exactness) — the §342 layer is
  fully closed and (342f)+(342g) directly enable the exactness
  argument.
* **Branch B (Aristotle IN_PROGRESS)**: continue manual anchors —
  next natural step is the sign-change extraction
  `signChangeSet : Polynomial ℝ → Finset ℝ` infrastructure
  (~50 LOC), or the `n = 3` zeros via IVT (~80 LOC,
  IVT sign-change argument: `P_3^*(0) = −1, P_3^*(1/2) = ?,
  P_3^*(1) = 1` plus parity-based reflection at `1/2`).
* **Branch C (Aristotle stalls)**: open
  `lem_342A_g_zeros_manual_closure_plan.md` with three phases
  (sign-change extraction, orthogonality contradiction, closure),
  analogous to the cycle 289 Branch D plan for (342f).

If §342 is fully closed by cycle ~298, the natural next theorem is
`lem:342B` — Gaussian quadrature exactness of the `s`-stage
quadrature with nodes at the zeros of `P_s^*`. The cycle 293 task
results explicitly identified this as the natural downstream target.
