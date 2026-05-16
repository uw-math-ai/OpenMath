# Cycle 334 strategy — §344 Phase D.13 follow-up: `SatisfiesC 3` certificate for Lobatto IIIA `s = 3`

## §A. Status entering cycle 334

Cycle 333 closed §344 Phase D.13 cleanly: `butcherLobattoIIIA_three`
collocation-form `RKTableau`, `butcherLobattoIIIADirect_three` direct
Simpson's-rule form, the coincidence theorem
`butcherLobattoIIIA_three_eq_direct`, and a `SatisfiesB 4`
non-vacuity witness. All axiom-clean
(`[propext, Classical.choice, Quot.sound]`); zero sorries; aggregator
builds.

Section344.lean ends at the `SatisfiesB 4` example
(`OpenMath/Chapter3/Section344.lean:2570`). That's where cycle 334
appends.

Cycle 333's task-results §"Suggested next approach" lists three
options:
1. Pivot to fresh entity (`def:422B`, `def:442A`, etc.).
2. Stretch `SatisfiesC 3` certificate for `butcherLobattoIIIA_three`.
3. Phase B.2 of `thm:344A` (multi-cycle headline).

**Cycle 334 picks option 2** (NOT option 1). Justification below in §B.

## §B. Why option 2 over option 1

Pre-cycle planner inspection of `def:422B` and `def:442A` JSONs
(`extraction/formalization_data/entities/`):

* **`def:422B` ("underlying one-step method", §422 p. 359)**: requires
  the group `G₁` of tree-indexed mappings (related to `def:381B`
  Φ-equivalence), equation (422a) inductively constructing η on tree
  order, and an existence/uniqueness story for preconsistent+stable
  LMMs. This is **non-trivial multi-cycle infrastructure**, not a
  single-cycle definition-only entity. The current §381 quotient-group
  machinery (cycle 222) is adjacent but not directly applicable; the
  bridge needs careful design.
* **`def:442A` ("principal sheet", §442 p. 377)**: introduces
  Riemann surfaces `R_Φ = {(w, z) : Φ(w, z) = 0}`, order stars,
  branch points, and the principal-sheet neighbourhood of `(0, 1)`.
  Substantial complex-analytic content with no current Lean
  infrastructure (Mathlib's Riemann-surface support is partial at
  best). **Multi-cycle; not single-cycle scope.**

Neither qualifies as a clean single-cycle deliverable.
**Pivoting requires multi-cycle scoping work which itself consumes a
cycle.** That is fine to do *eventually*, but cycle 334's safest
deliverable is the cycle 333 option 2 (SatisfiesC 3): one more clean
§344 ship, then cycle 335's planner can scope a genuine pivot with
proper Phase-decomposition work.

The cycle 327 worker's "mechanical-template" hypothesis has now been
validated across cycles 322/323/324/325/329/332/333 — seven
consecutive C(s)-coincidence / direct-form ships. Adding the
`SatisfiesC 3` certificate for Lobatto IIIA `s = 3` continues this
rhythm at low risk. Cycle 335 pivots.

## §C. Cycle 334 deliverable (Priority 1)

Ship the `SatisfiesC 3` certificate for `butcherLobattoIIIA_three`,
routing via cycle 333's coincidence theorem to the direct form.

### Definition recap

```
-- OpenMath/Chapter3/Section321.lean:99
def SatisfiesC {s : ℕ} (M : RKTableau s) (ξ : ℕ) : Prop :=
  ∀ i : Fin s, ∀ k : ℕ, 1 ≤ k → k ≤ ξ →
    (∑ j : Fin s, M.A i j * M.c j ^ (k - 1)) = M.c i ^ k / (k : ℝ)
```

For Lobatto IIIA `s = 3` direct form with `c = (0, 1/2, 1)` and
`A = !![0, 0, 0; 5/24, 1/3, -1/24; 1/6, 2/3, 1/6]`, the certificate
has **9 arms** (3 stages × 3 exponents `k ∈ {1, 2, 3}`).

### Arm-by-arm sanity check (paper verification before writing Lean)

* **Row 0** (`c_0 = 0`): RHS = `0^k / k = 0` for `k ≥ 1`. LHS =
  `0·0^(k-1) + 0·(1/2)^(k-1) + 0·1^(k-1) = 0`. All three arms close
  trivially.
* **Row 1** (`c_1 = 1/2`, A-row = `(5/24, 1/3, -1/24)`):
  - `k = 1`: LHS = `5/24·1 + 1/3·1 + (-1/24)·1 = 12/24 = 1/2`.
    RHS = `(1/2)^1 / 1 = 1/2`. ✓
  - `k = 2`: LHS = `5/24·0 + 1/3·(1/2) + (-1/24)·1 = 4/24 - 1/24
    = 3/24 = 1/8`. RHS = `(1/2)^2 / 2 = 1/8`. ✓
  - `k = 3`: LHS = `5/24·0 + 1/3·(1/4) + (-1/24)·1 = 2/24 - 1/24
    = 1/24`. RHS = `(1/2)^3 / 3 = (1/8)/3 = 1/24`. ✓
* **Row 2** (`c_2 = 1`, A-row = `(1/6, 2/3, 1/6)`):
  - `k = 1`: LHS = `1/6·1 + 2/3·1 + 1/6·1 = 1`.
    RHS = `1^1 / 1 = 1`. ✓
  - `k = 2`: LHS = `1/6·0 + 2/3·(1/2) + 1/6·1 = 1/3 + 1/6 = 1/2`.
    RHS = `1^2 / 2 = 1/2`. ✓
  - `k = 3`: LHS = `1/6·0 + 2/3·(1/4) + 1/6·1 = 1/6 + 1/6 = 1/3`.
    RHS = `1^3 / 3 = 1/3`. ✓

All 9 arms paper-verified.

### Target form (named theorem recommended over `example`)

```lean
/-- **`SatisfiesC 3` certificate** for the cycle 333
collocation-assembled Lobatto IIIA `s = 3` tableau: the C(s)-defining
collocation simplifying assumption holds. Routes via cycle 333's
coincidence theorem to the direct Simpson's-rule form. Mirrors
cycle 332's `butcherRadauI_collocation_two.SatisfiesC 2` certificate
at one higher dimension. -/
theorem butcherLobattoIIIA_three_satisfiesC :
    butcherLobattoIIIA_three.SatisfiesC 3 := by
  rw [butcherLobattoIIIA_three_eq_direct]
  intro i k h1 hk
  fin_cases i <;> interval_cases k <;>
    simp [butcherLobattoIIIADirect_three, Fin.sum_univ_three] <;>
    norm_num
```

Naming the deliverable as a `theorem` (not `example`) enables
`#print axioms` for axiom-clean verification — matches cycles
322/325's `_satisfiesB_*` named pattern. Cycles 323/324/329/332/333
used `example` for the same content, so either is acceptable, but
**prefer the named form**.

Placement: append immediately after the cycle 333 `SatisfiesB 4`
example (currently line 2570), just before
`end OpenMath.Chapter3.Section344`.

LOC estimate: ~10 LOC (docstring + theorem body).

### Risk assessment (each "should work" claim with a fallback)

* **R1 — `fin_cases i <;> interval_cases k <;> ...` Cartesian explosion:**
  If the 9-way `<;>` chain confuses Lean, fall back to explicit
  nested forms:
  ```lean
  intro i k h1 hk
  fin_cases i
  · interval_cases k
    · simp [butcherLobattoIIIADirect_three, Fin.sum_univ_three]
    · simp [butcherLobattoIIIADirect_three, Fin.sum_univ_three]
    · simp [butcherLobattoIIIADirect_three, Fin.sum_univ_three]
  · interval_cases k
    · simp [butcherLobattoIIIADirect_three, Fin.sum_univ_three]; norm_num
    · simp [butcherLobattoIIIADirect_three, Fin.sum_univ_three]; norm_num
    · simp [butcherLobattoIIIADirect_three, Fin.sum_univ_three]; norm_num
  · interval_cases k
    · simp [butcherLobattoIIIADirect_three, Fin.sum_univ_three]; norm_num
    · simp [butcherLobattoIIIADirect_three, Fin.sum_univ_three]; norm_num
    · simp [butcherLobattoIIIADirect_three, Fin.sum_univ_three]; norm_num
  ```
  This is the cycle 329 `SatisfiesC 2` recipe scaled up.

* **R2 — Row-0 `0^k` reduction for general `k ∈ {1, 2, 3}`:**
  `simp` should reduce `0^(k - 1) = 0` for `k ≥ 1` via `zero_pow` and
  `Nat.sub_one_add_one`-style lemmas; the row-0 arms should close
  without needing `norm_num` (LHS reduces to `0`, RHS reduces to
  `0^k / k = 0`). If `simp` over-reduces (e.g. tries to prove
  `0 = 0^k / k`), add `pow_zero, pow_one, zero_pow, ne_of_gt, h1`
  to the simp set or drop in an explicit `omega` discharge.

* **R3 — Rational arithmetic across 9 arms:** `norm_num` is robust
  on denominators ≤ 24 (paper-verified above). No issues expected.

* **R4 — `Nat.sub` edge at `k = 1`:** `k - 1 = 0` so `c_j^(k-1) = 1`
  uniformly. The simp set should handle this via `pow_zero` and
  `Nat.sub_self`; cycle 322's `SatisfiesB 1` example confirms the
  `k = 1` arm closes cleanly via the same chain.

The recipe is identical to cycle 329's `butcherRadauIDirect_two.SatisfiesC 2`
template (`fin_cases i <;> interval_cases k <;> simp <;> norm_num`),
scaled from 4 arms to 9 arms. Both cycles 329 and 332 validated this
exact tactic chain.

## §D. Cycle 334 verification

```bash
# 1. File compiles standalone.
lake env lean OpenMath/Chapter3/Section344.lean

# 2. Aggregator clean.
lake env lean OpenMath/Chapter3.lean

# 3. Sorry count check.
grep -c sorry OpenMath/Chapter3/Section344.lean   # expect 0

# 4. Tautology scanner clean.
rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/Chapter3/Section344.lean

# 5. Axiom check on the new theorem.
echo '#print axioms OpenMath.Chapter3.Section344.butcherLobattoIIIA_three_satisfiesC' \
  | lake env lean --stdin OpenMath/Chapter3/Section344.lean
# Expected: [propext, Classical.choice, Quot.sound] only.
```

## §E. Deliverable summary

* **One new public theorem** (`butcherLobattoIIIA_three_satisfiesC`):
  the cycle 333 C(s) classification certificate at `s = 3`.
* **Axiom-clean target**: `[propext, Classical.choice, Quot.sound]`.
* **Sorry count**: 0 → 0 (must remain).
* **LOC delta**: +~10 (one theorem + docstring).
* **Aggregator build**: must still pass.

## §F. What NOT to try this cycle

* Do **NOT** attempt `def:422B` or `def:442A` as a cycle 334
  deliverable. Both require multi-cycle scoping doc + Phase
  decomposition. Reserve for a future cycle when the planner has
  budget for a dedicated scoping cycle.
* Do **NOT** attempt Phase B.2 of `thm:344A` (polynomial-exactness
  `2s − 2` / `2s − 3` headline). Multi-cycle, requires `B(2s − 2)` /
  `B(2s − 3)` order-condition machinery and polynomial-division
  reasoning (Butcher p. 244 proof outline). Out of scope.
* Do **NOT** rewrite or audit cycle 333's deliverables. They are
  shipped axiom-clean; touching them risks regression.
* Do **NOT** raise `maxHeartbeats` above 200000. The 9-arm certificate
  is well within default elaboration budget. If `<;>` chains time out
  (R1), decompose into explicit nested `fin_cases` / `interval_cases`
  per the §C fallback recipe.
* Do **NOT** introduce `sorry`/`axiom`/`constant` declarations.
* Do **NOT** edit `scripts/autonomous_loop.py` from the worker. Per
  CLAUDE.md, prompt-builder / scanner false positives are
  loop-maintainer territory (see
  `.prover-state/issues/tautology_scanner_false_positives.md` and
  `.prover-state/issues/phantom_commit_verdict_pattern.md`).
* Do **NOT** attempt to compile `OpenMath/Chapter4/Section441.lean` on
  this cluster. 43+ consecutive GPFS timeouts since cycle 182; skip
  per `.prover-state/issues/cycle_182_gpfs_slowness.md`.
* Do **NOT** retry `bdf2LMM_aPoly_eq` (Polynomial.ext path); cycles
  172/173 stalled because `ring` cannot fold `Polynomial.C`
  arithmetic. The cycle 180 `Polynomial.funext + ring` recipe is
  the canonical closure pattern for `Polynomial ℝ` constant arithmetic
  — irrelevant to cycle 334's §344 target.
* Do **NOT** generalize to a `SatisfiesD 3` or `SatisfiesE 3 3`
  certificate this cycle. Each would be a separate ship; cycle 334
  deliverable is **only** `SatisfiesC 3`. Other certificates may be
  candidates for cycle 335+ small-ship work.

## §G. Cycle 335+ outlook

Once cycle 334's `SatisfiesC 3` lands, candidate pivots for cycle 335:

* **Definition-only pivots** (multi-cycle scoping required):
  - `def:422B` (G₁-group on top of cycle 222's quotient group).
  - `def:442A` (Riemann surfaces + principal sheet).
  - Either requires a dedicated scoping cycle (analogous to
    `.prover-state/issues/lem_310B_plan.md` or
    `.prover-state/issues/lem_441A_phase_C_scoping.md`) **before**
    shipping any Lean code.
* **§300 tree-combinatorics pivot**: `thm:302A` (combinatorial
  questions on rooted trees) or `thm:302B` (rooted tree generating
  function identity). Both unformalised; consumes cycles 254–270
  rooted-tree infrastructure. `thm:302A` may be single-cycle if
  enumerative; `thm:302B` likely multi-cycle.
* **§310/§311 multilinear-`E` Phase D**: lift cycle 266–270's
  scalar `bseriesExactTerm_<tree>_scalar` chain to polymorphic `E`.
  MEDIUM-HIGH risk per cycle 248/265 task results. Multi-cycle.
* **Continue §344 ladder**: e.g. `butcherLobattoIIIDirect_three`
  (Lobatto III C(s−1) variant at `s = 3`, mechanical extension of
  cycle 331's `s = 2`). Extends §344 streak to 18+ cycles; valuable
  only if cycle 335 needs another safe small-cycle deliverable while
  a multi-cycle pivot is being scoped in parallel.

The planner of cycle 335 should pick **one** of these and commit
to a Phase decomposition / scoping document if the target is
multi-cycle. Avoid the cycle 200/201 sorry-first scaffold rollback
pattern (cycle 138/139 `thm:550A`, cycle 149/150 `def:530B`,
cycle 200/201 `thm:381H` all hit it when planners under-scoped).

## §H. Worker checklist

1. (5 min) Read `OpenMath/Chapter3/Section344.lean:2506-2570` to
   confirm cycle 333 deliverables are at HEAD.
2. (2 min) Confirm `SatisfiesC` definition at
   `OpenMath/Chapter3/Section321.lean:99`.
3. (15 min) Write the cycle 334 deliverable per §C. Use named
   `theorem` form for axiom-cleanliness verification.
4. (5 min) Run verification commands per §D.
5. (5 min) Confirm axiom-clean via `#print axioms ...`.
6. (10 min) Write `task_results/cycle_334.md` per CLAUDE.md format.
7. (5 min) Update `plan.md`: append cycle 334 line to the Lobatto IIIA
   row inside the `[~] thm:344A` entry.
8. (commit + push) standard cycle close.

Total expected effort: ~50 minutes. Cycle 334 is a low-risk
high-confidence ship.

## §I. Faithfulness check checklist

Cycle 334 introduces **one new theorem** (no new `def`, no new
`structure`, no new `class`). Pre-commit checklist per CLAUDE.md:

* **Tautology check**: `SatisfiesC 3` is a non-trivial assertion
  (9 distinct equational identities). The conclusion does NOT appear
  verbatim as a hypothesis. Pass.
* **Identity check**: the proof uses `fin_cases` + `interval_cases`
  + `simp` + `norm_num` — a substantive 9-arm computation across
  rational arithmetic. Not a trivial `exact h`. Pass.
* **Hypothesis strength check**: none beyond `SatisfiesC`'s standard
  form. Pass.
* **Absent theorem check**: no comments promise unwritten content.
  Pass.

The cycle 334 deliverable is the textbook-faithful C(s)-collocation
classification certificate at `s = 3`. The C(s) condition (Butcher
§321 equation (321b)) is *exactly* the row-sum-of-A-weighted-c-powers
identity, and Lobatto IIIA's Table 344(I) "C(s)" row entry directly
asserts this. No divergence; no faithfulness gap.
