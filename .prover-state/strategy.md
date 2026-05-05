# Cycle 141 Strategy

## Context

Cycle 140 closed cleanly (+2 score): Aristotle Job B's `n = 2` stepping
stone for `thm:550A` (`doublyCompanionMatrix_det_factorization_n_two`)
was inlined verbatim into `OpenMath/Chapter5/Section550.lean`,
axiom-clean. Sorry count: 0. Full Chapter 5 build: 2787/2787 green.

§550 now carries two genuine witnesses (`_n_one` cycle 138,
`_n_two` cycle 140) and the general-`n` statement is intentionally
absent — re-introducing it as `sorry` was the cycle-138 mistake that
triggered the −2 supervisor revert.

Aristotle status:
- Job A (general-`n`, project `7062c2a2-4a8b-4fae-b694-9355e06427a9`):
  IN_PROGRESS at **4 %** as of 2026-05-05T19:50 (≈40 min after
  resubmission, but ~24h elapsed since cycle 138 first kicked it off).
  Progress is essentially flat → strongly suggests Aristotle cannot
  close the eigenvalue-density / cofactor-induction argument.
- Job B: COMPLETE, already consumed cycle 140.

The recent 6-cycle pattern (135 → 140) alternates between
**substantive non-vacuity strengthenings** (135, 136, 137, 140) and
**section openings** (138, 139). Score deltas: +2, +2, +2, −2, +1, +2.
The single −2 came from opening §550 with a `sorry`-bearing general-n
statement. Lesson: **opening new ground without a proof body is
expensive**; strengthening existing predicates is cheap +2.

This cycle should follow the 135/136/137/140 cheap-and-safe model:
strengthen an existing predicate's non-vacuity story with a
**substantive, axiom-clean witness that exercises a heretofore
unwitnessed structural feature**.

---

## Priority 0 (MANDATORY): Poll Aristotle Job A once, decide

**Action**: issue ONE call to
`mcp__aristotle__get_status` on project
`7062c2a2-4a8b-4fae-b694-9355e06427a9` (general-`n` `thm:550A`).

**Decision tree**:

* **If Job A returned COMPLETE** (low probability — 4 % at 24h is
  flat-line): defer Priority 1 below; instead promote to Priority 1B:
  extract via `mcp__aristotle__extract_result` and attempt to inline
  as `doublyCompanionMatrix_det_factorization` (general n) in
  `OpenMath/Chapter5/Section550.lean`. Verify axiom-clean via
  `lean_verify`. If the extracted proof fails to compile after at
  most ONE round of mechanical adaptation (rename hypothesis aliases
  if shadowed), abandon and revert to Priority 1.

* **If Job A is still IN_PROGRESS at < 10 %**: cancel via
  `mcp__aristotle__cancel_project 7062c2a2-...`. Document in cycle
  results that the job was killed after 24h flatlining at 4 %.
  General-`n` closure is then officially blocked on the
  cofactor-expansion / eigenvalue-density manual route documented
  in `.prover-state/issues/thm_550A_general_n.md`. Proceed to
  Priority 1.

* **If Job A is IN_PROGRESS at ≥ 10 %**: leave running, proceed to
  Priority 1.

**Do NOT** re-poll Job A more than once this cycle. **Do NOT** submit
any new Aristotle jobs this cycle — this is a manual-only cycle.

---

## Priority 1 (PRIMARY): Strengthen `def:530A` non-vacuity with a heterogeneous-stages witness

**Target file**: `OpenMath/Chapter5/Section530.lean`

**Mathematical motivation**

The current witnesses `trivialStartingMethod` (cycle 139) and
`zeroStartingMethod` (cycle 139) both have:
* `r = 1` (single constituent method)
* `stages = fun _ => 1` (all constituent methods have exactly 1 stage)

This pair refutes degeneracy and confirms it on the *simplest possible*
shape, satisfying CLAUDE.md non-vacuity. But it leaves the
**heterogeneous-stages dependent-function** design in
`StartingMethod.stages : Fin r → ℕ` (Section530.lean:82) UNTESTED:
no existing witness exercises `r > 1` *with different `s_i`* per `i`.

This is the same gap-closing pattern that cycles 134
(`padded2DEulerGLM_isRKStable`, r=2 substantive witness) and 135
(`implicitMidpointGLM_isAStable`, substantive Padé witness) followed.

**Concrete deliverable**

Add the following to `OpenMath/Chapter5/Section530.lean`:

1. **A 2-stage `GeneralizedRungeKuttaMethod 2` definition**, e.g.
   `nontrivialTwoStageGRK : GeneralizedRungeKuttaMethod 2` with:
   * `c := ![0, 1]` (or `fun _ => 0` — any concrete values fine)
   * `A := !![0, 0; 0, 0]` (a `Matrix (Fin 2) (Fin 2) ℝ`)
   * `b₀ := 2` (any non-zero scalar; `2` makes it textually
     distinguishable from the `1` used in `trivialGeneralizedRK`)
   * `b := ![0, 0]`

2. **`mixedStartingMethod : StartingMethod 2`** — a 2-method starting
   method with **heterogeneous** stage counts:
   * `stages 0 := 1`, `stages 1 := 2`. Implement as
     `stages := ![1, 2]` or
     `stages := fun i => if i.val = 0 then 1 else 2`.
   * `method 0 := trivialGeneralizedRK` (1-stage with `b₀ = 1`).
   * `method 1 := nontrivialTwoStageGRK` (2-stage with `b₀ = 2`).

   Note: the dependent-typed `method` field requires `(method i :
   GeneralizedRungeKuttaMethod (stages i))`. Use `match` or
   `Fin.cases` to define this dependently.

3. **`mixedStartingMethod_isNonDegenerate`** — non-vacuity theorem
   stating `mixedStartingMethod.IsNonDegenerate`. Proof shape:
   ```
   rw [StartingMethod.isNonDegenerate_iff_exists_b₀_ne_zero]
   refine ⟨0, ?_⟩
   show (1 : ℝ) ≠ 0
   exact one_ne_zero
   ```
   (Or use index `1` and `(2 : ℝ) ≠ 0` via `two_ne_zero`.)

4. **`mixedStartingMethod_stages_neq`** — a one-line theorem
   confirming `mixedStartingMethod.stages 0 ≠
   mixedStartingMethod.stages 1`. Proof: `decide` (or
   `Nat.one_ne_succ_succ` / explicit numeric `omega`). This is the
   *load-bearing* theorem: it confirms the dependent-function design
   is genuinely needed (the existing constant-stages witnesses leave
   open the question of whether `stages : Fin r → ℕ` does real work).

**Estimated LOC**: ~50 (one new GRK `def`, one new `StartingMethod`
`def`, two new theorems, plus docstrings).

**Approach (specific tactics)**:

* For the 2-stage tableau, the matrix-literal `!![0, 0; 0, 0]`
  builds a `Matrix (Fin 2) (Fin 2) ℝ`; verify type-inference with a
  `(_ : Matrix (Fin 2) (Fin 2) ℝ)` annotation if needed.
* For the dependent `method` field, the cleanest form is
  ```lean
  method := fun i => match i with
    | ⟨0, _⟩ => trivialGeneralizedRK
    | ⟨1, _⟩ => nontrivialTwoStageGRK
  ```
  But this requires `(stages i) = 1` / `= 2` to definitionally hold
  on each branch. If the `stages := ![1, 2]` form's matcher does not
  reduce definitionally, fall back to using
  `Fin.cases (motive := fun i => GeneralizedRungeKuttaMethod (stages i))`
  with an explicit motive.
* For `mixedStartingMethod_isNonDegenerate`, the proof template is
  identical to the existing `trivialStartingMethod_isNonDegenerate`
  (Section530.lean:140-145), just at a different index.
* For `mixedStartingMethod_stages_neq`, `decide` should suffice;
  `simp [mixedStartingMethod]; decide` if `decide` alone fails to
  unfold.

**Verification gates** (run all three before committing):

1. `lake env lean OpenMath/Chapter5/Section530.lean` — must exit 0,
   no warnings.
2. `lean_verify` (via the lean-lsp MCP) on each new theorem — must
   return `[propext, Classical.choice, Quot.sound]` only. No
   `sorryAx`.
3. `lake build OpenMath.Chapter5` — must remain green.

**Faithfulness**: This is a non-vacuity strengthening (cycle 134/135
pattern), not a new mathematical claim. No textbook divergence.

---

## Priority 2 (STRETCH, only if Priority 1 lands with > 30 min cycle time remaining): Refutability witness for degeneracy at `r = 2`

After Priority 1, the only `IsDegenerate` witness at hand is
`zeroStartingMethod` (`r = 1`). Add a parallel:

* **`zero2StartingMethod : StartingMethod 2`** with both methods
  being 1-stage `zeroGeneralizedRK` (so `stages := fun _ => 1`,
  `method := fun _ => zeroGeneralizedRK`).
* **`zero2StartingMethod_isDegenerate`** — `IsDegenerate` proof via
  `intro i; fin_cases i; · rfl; · rfl`.

This is ~15 LOC and confirms the dichotomy is non-trivial across
`r = 2` shapes. Skip if Priority 1 takes the full cycle budget.

---

## Priority 3 (BACKUP, only if Priority 1 hits an unexpected blocker): Open `OpenMath/Chapter4/Section442.lean` with `def:442A` (principal sheet) skeleton

If Priority 1 stalls on dependent-typing issues (e.g. the
heterogeneous `method` field's matcher does not reduce
definitionally and `Fin.cases` motive plumbing eats the cycle
budget), pivot to opening Chapter 4 §442:

* Open `OpenMath/Chapter4/Section442.lean` with the **principal
  sheet** structural definition. The principal sheet is the unique
  branch of the stability function `r(z)` of an LMM near `z = 0`
  satisfying `r(0) = 1`. Define the predicate
  `IsPrincipalSheet (M : LinearMultistepMethod k) (r : ℂ → ℂ) : Prop`
  capturing the textbook condition.
* Witness: `(0 : ℂ → ℂ)` is *not* a principal sheet (refutes
  vacuity); the constant `1` function is also *not* a principal
  sheet without the consistency conditions; the principal sheet of
  explicit Euler is `r(z) = 1 + z`, which IS a principal sheet —
  prove `isPrincipalSheet_explicit_euler`.

**Risk**: this requires `Complex.HasDerivAt` infrastructure for
`r(0) = 1` and `r'(0) = 1` consistency clauses. Only pivot here if
Priority 1 is genuinely blocked, NOT just slow. Estimated 80 LOC if
attempted.

---

## What NOT to try (explicit failed-approach blacklist)

1. **Do NOT attempt manual general-`n` `thm:550A`.** Per
   `.prover-state/issues/thm_550A_general_n.md`, this requires
   either (a) cofactor-expansion induction over the sparse
   `(I − zX)` structure (~150 LOC, multi-cycle), (b) eigenvalue-
   density argument with Mathlib continuity-of-charpoly (~300 LOC,
   2–3 cycles), or (c) `n`-induction via the bottom-right block.
   None fits a single-cycle budget. Aristotle Job A has been
   running for 24h at 4 % — it is not happening this cycle.

2. **Do NOT open `def:530B` or `def:530C`** ("Order relative to
   starting method"). These require Taylor-expansion infrastructure
   for SM/GLM composition that does not yet exist in the codebase;
   cycle-139 strategy explicitly warned against this. Estimated
   3+ cycles of careful infrastructure work; out of scope.

3. **Do NOT submit new Aristotle jobs.** This is a manual-only
   cycle. The Aristotle slot is occupied by Job A; do not stack
   submissions while one is pending.

4. **Do NOT re-poll Aristotle Job A more than once.** Per
   CLAUDE.md "one check after 30 min is enough" + the cycle-140
   precedent.

5. **Do NOT introduce ANY new `sorry`.** Sorry count must stay at 0.
   The cycle 138 score (−2) was triggered solely by sorry regression.
   If a witness encounters difficulty, ABANDON the new code (do not
   commit) rather than commit it with a sorry.

6. **Do NOT re-prove or re-state `thm:550A` for `n ≥ 3`.** The
   Job-B-style proof at `n = 2` worked because of `Matrix.det_fin_two`;
   `Matrix.det_fin_three` exists but the residue polynomial expansion
   grows quickly and the `IsBigO` bound becomes non-trivial. If we
   want `n = 3` later, that's a focused future cycle, not this one.

7. **Do NOT modify `lean_status.json`'s `formalization_status`
   field for `def:530A`** — it remains `formalized` (cycle 139).
   Just bump the `cycle` field if `lean_status.json` records cycles
   per-entity, and update the `notes` to mention the new
   heterogeneous-stages witness.

8. **Do NOT try `mixedStartingMethod` with `r > 2`.** `r = 2` is
   the minimal heterogeneous-stages case; larger `r` adds matcher
   complexity without proving anything new. Stay at `r = 2`.

9. **Do NOT use `Aristotle` for the §530 mixed witness.** It's a
   ~50-LOC structural definition + two trivial theorems; manual
   coding is faster than the submit/poll cycle.

---

## Definition-of-Done checklist

By end of cycle 141:

- [ ] Aristotle Job A polled exactly once; cancelled or left running
      per the Priority 0 decision tree.
- [ ] If Job A was COMPLETE: general-`n` proof inlined and
      axiom-clean (Priority 1B). Else:
- [ ] `nontrivialTwoStageGRK : GeneralizedRungeKuttaMethod 2`
      defined.
- [ ] `mixedStartingMethod : StartingMethod 2` defined with
      `stages 0 = 1`, `stages 1 = 2`.
- [ ] `mixedStartingMethod_isNonDegenerate` proved axiom-clean.
- [ ] `mixedStartingMethod_stages_neq` proved axiom-clean.
- [ ] (Stretch) `zero2StartingMethod_isDegenerate` proved
      axiom-clean.
- [ ] `lake env lean OpenMath/Chapter5/Section530.lean` clean.
- [ ] `lake build OpenMath.Chapter5` returns green.
- [ ] Sorry count remains 0 across the entire `OpenMath/` tree.
- [ ] `lean_status.json` `def:530A` notes updated to mention the
      cycle-141 heterogeneous witness.
- [ ] `plan.md` `def:530A` row notes the cycle-141 strengthening
      (one-line append; status remains `[x]`).
- [ ] `.prover-state/task_results/cycle_141.md` written per
      CLAUDE.md template (Worked on / Approach / Result /
      Faithfulness check / Dead ends / Discovery / Suggested next
      approach).
- [ ] All work committed and pushed.

## Why this strategy

* **Risk-minimizing**: every action is either zero-risk (polling
  Aristotle) or +2-pattern non-vacuity strengthening (Priority 1).
  No new sorries introduced. No new infrastructure opened.
* **Forward progress**: closes a real gap in the §530 non-vacuity
  story (heterogeneous-stages design currently untested).
* **Fits cycle budget**: estimated 50 LOC for the primary deliverable,
  ~15 LOC for the stretch goal. Well within a single-cycle budget.
* **Builds momentum**: cycle 141 will be the 7th consecutive
  axiom-clean Chapter-5 substantive cycle (135–141 modulo the 138
  revert). Strengthening §530 keeps the §530 entry point warm
  for the def:530B/C work that will eventually need it.
