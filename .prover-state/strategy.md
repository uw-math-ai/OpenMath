# Cycle 355 Strategy

## Context

Cycle 354 shipped two stability witnesses axiom-clean:
* `trapezoidalLMM_isStable` (Section404.lean, ~line 278)
* `bdf3LMM_isStable` (Section451.lean, ~line 441)

All four §404 LMM witnesses (explicit Euler, implicit Euler, trapezoidal,
BDF2, BDF3) now have stability + consistency in hand. The §422
infrastructure from cycles 344–351 (Phase D and Phase D′ Step 1) is also
in place. **No sorries in the repo.**

The natural cycle 355 move is to **exercise cycle 354's stability ships
at downstream §422 consumers**: four small (~5–10 LOC each)
non-vacuity / instantiation witnesses that prove cycle 354's work is
load-bearing. All are mechanical compositions of existing axiom-clean
infrastructure — no risk of stalling, no Aristotle delegation needed.

There are no Aristotle results pending.

## Goal

Ship four (or five, stretch) numerical non-vacuity witnesses in
`OpenMath/Chapter4/Section422.lean` that exercise the cycle 354 stability
ships. All ~5–10 LOC each, all axiom-clean targets, sorry count remains 0.

## Priorities

### P1 (mandatory, ~7 LOC) — `trapezoidalLMM_sum_β_pos` example

Mirror of `bdf2LMM_sum_β_pos` example at `Section422.lean:1045–1049`.
Direct invocation of cycle 349's `sum_β_pos_of_stable_consistent` with
cycle 352's `trapezoidalLMM_isConsistent` + cycle 354's
`trapezoidalLMM_isStable`.

**Placement**: in `Section422.lean`, immediately after the existing
`bdf2LMM_sum_β_pos` `example` block (line ~1049). The new block forms
a natural pair with it.

**Numerical sanity (paper-verified)**: trapezoidal has `k = 1`,
`β = (1/2, 1/2)`, so `Σᵢ:Fin 2 βᵢ = 1/2 + 1/2 = 1 > 0`.

**Concrete Lean**:

```lean
/-- *Trapezoidal D′.2.0 witness (cycle 355):* end-to-end exercise of
`sum_β_pos_of_stable_consistent` on the trapezoidal (Crank–Nicolson)
LMM, discharging stability via `trapezoidalLMM_isStable` (cycle 354)
and consistency via `trapezoidalLMM_isConsistent` (cycle 352).

Numerical sanity: trapezoidal's β-sum is `1/2 + 1/2 = 1 > 0`. -/
example : (0 : ℝ) < ∑ i : Fin 2, OpenMath.Chapter4.Section404.trapezoidalLMM.β i :=
  sum_β_pos_of_stable_consistent OpenMath.Chapter4.Section404.trapezoidalLMM
    (by norm_num : (0 : ℕ) < 1)
    OpenMath.Chapter4.Section404.trapezoidalLMM_isStable
    OpenMath.Chapter4.Section404.trapezoidalLMM_isConsistent
```

**Verify**: build Section422, ensure example accepts (no `#print axioms`
needed for `example`s — they don't get a name).

### P2 (mandatory, ~7 LOC) — `bdf3LMM_sum_β_pos` example

Same shape as P1, with BDF3 inputs:
* `OpenMath.Chapter4.Section451.bdf3LMM` (Section451.lean:161)
* `OpenMath.Chapter4.Section451.bdf3LMM_isStable` (cycle 354)
* `OpenMath.Chapter4.Section451.bdf3LMM_isConsistent` (Section451.lean:193, cycle 353)

**Placement**: immediately after P1's `example` block.

**Numerical sanity (paper-verified)**: BDF3 has `k = 3`,
`β = (6/11, 0, 0, 0)`, so `Σᵢ:Fin 4 βᵢ = 6/11 + 0 + 0 + 0 = 6/11 > 0`.

**Concrete Lean**:

```lean
/-- *BDF3 D′.2.0 witness (cycle 355):* end-to-end exercise of
`sum_β_pos_of_stable_consistent` on BDF3, discharging stability via
`bdf3LMM_isStable` (cycle 354) and consistency via `bdf3LMM_isConsistent`
(cycle 353).

Numerical sanity: BDF3's β-sum is `6/11 + 0 + 0 + 0 = 6/11 > 0`. -/
example : (0 : ℝ) < ∑ i : Fin 4, OpenMath.Chapter4.Section451.bdf3LMM.β i :=
  sum_β_pos_of_stable_consistent OpenMath.Chapter4.Section451.bdf3LMM
    (by norm_num : (0 : ℕ) < 3)
    OpenMath.Chapter4.Section451.bdf3LMM_isStable
    OpenMath.Chapter4.Section451.bdf3LMM_isConsistent
```

### P3 (mandatory, ~10 LOC) — `trapezoidalLMM_coef_α_plus_coef_β_ne_zero`

Mirror of `bdf2LMM_coef_α_plus_coef_β_ne_zero` at
`Section422.lean:1128–1135` (cycle 350). Named theorem (not `example`)
so downstream consumers can cite it.

**Placement**: immediately after `bdf2LMM_coef_α_plus_coef_β_ne_zero`
(line ~1135).

**Numerical sanity (paper-verified)**: trapezoidal at `k = 1`:
* `coef_α = 1·α(1) = 1·1 = 1`
* `coef_β = 0·β(0) + 1·β(1) = 0 + 1/2 = 1/2`
* `coef_α + coef_β = 3/2 ≠ 0` ✓

**Concrete Lean** (mirror cycle 350's pattern; use `Fin.sum_univ_one`
for the α-side at `k = 1` and `Fin.sum_univ_two` for the β-side at
`k + 1 = 2`):

```lean
/-- *Trapezoidal D′.2.1 non-vanishing witness (cycle 355):*
trapezoidal's denominator `coef_α + coef_β = 1 + 1/2 = 3/2 ≠ 0`.
Numerical witness for the cycle 350 weakened-hypothesis ship at the
trapezoidal (Crank–Nicolson) LMM. -/
theorem trapezoidalLMM_coef_α_plus_coef_β_ne_zero :
    (∑ i : Fin 1, ((i.val + 1 : ℕ) : ℝ) *
        OpenMath.Chapter4.Section404.trapezoidalLMM.α i.succ)
      + (∑ i : Fin 2, ((i.val : ℕ) : ℝ) *
            OpenMath.Chapter4.Section404.trapezoidalLMM.β i) ≠ 0 := by
  simp [OpenMath.Chapter4.Section404.trapezoidalLMM,
    Fin.sum_univ_one, Fin.sum_univ_two]
  norm_num
```

### P4 (mandatory, ~10 LOC) — `bdf3LMM_coef_α_plus_coef_β_ne_zero`

Same shape as P3, BDF3 inputs.

**Placement**: immediately after P3's theorem.

**Numerical sanity (paper-verified)**: BDF3 at `k = 3`:
* `coef_α = 1·(18/11) + 2·(-9/11) + 3·(2/11) = (18 - 18 + 6)/11 = 6/11`
* `coef_β = 0·(6/11) + 1·0 + 2·0 + 3·0 = 0`
* `coef_α + coef_β = 6/11 ≠ 0` ✓

**Concrete Lean** (use `Fin.sum_univ_three` for α-side at `k = 3` and
`Fin.sum_univ_four` for β-side at `k + 1 = 4`):

```lean
/-- *BDF3 D′.2.1 non-vanishing witness (cycle 355):* BDF3's denominator
`coef_α + coef_β = 6/11 + 0 = 6/11 ≠ 0`. Numerical witness for the
cycle 350 weakened-hypothesis ship at BDF3. -/
theorem bdf3LMM_coef_α_plus_coef_β_ne_zero :
    (∑ i : Fin 3, ((i.val + 1 : ℕ) : ℝ) *
        OpenMath.Chapter4.Section451.bdf3LMM.α i.succ)
      + (∑ i : Fin 4, ((i.val : ℕ) : ℝ) *
            OpenMath.Chapter4.Section451.bdf3LMM.β i) ≠ 0 := by
  simp [OpenMath.Chapter4.Section451.bdf3LMM,
    Fin.sum_univ_three, Fin.sum_univ_four]
  norm_num
```

**Risk note**: `Fin.sum_univ_four` exists in Mathlib
(`Mathlib.Algebra.BigOperators.Fin`; cycle 268's worker confirmed the
companion `Fin.prod_univ_four` at the same location). If it does NOT
fire on first try, fall back to a manual unfold:
`rw [show (4 : ℕ) = 3 + 1 from rfl, Fin.sum_univ_succ];
 simp [Fin.sum_univ_three]; norm_num`
or use `decide` on the BDF3 β-side (which is all-but-one-zero and
should reduce trivially). Worker should NOT spend more than 10
minutes on this sub-step before applying a fallback.

### P5 (stretch, ~15 LOC) — end-to-end trapezoidal Eq422a witness

Mirror of the `example` at `Section422.lean:1143–1156` (BDF2 `η(τ) = 1`
end-to-end). For trapezoidal: `η(τ) = sum_β / (coef_α + coef_β) =
1 / (3/2) = 2/3`.

**Placement**: immediately after P4.

**Concrete Lean**:

```lean
/-- *Non-vacuity for the cycle 355 weakened ship (trapezoidal):*
end-to-end exercise of `Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened`
on trapezoidal, pinning `η(τ) = 1 / (3/2) = 2/3` for the underlying
one-step method corresponding to the Crank–Nicolson LMM. -/
example (η_q : Quotient PhiEquivalent.setoidSigma)
    (hEq : Eq422a OpenMath.Chapter4.Section404.trapezoidalLMM η_q) :
    elementaryWeightQ_phi η_q RootedTree.vertex = 2 / 3 := by
  have h := Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened
    OpenMath.Chapter4.Section404.trapezoidalLMM
    (by norm_num : (0 : ℕ) < 1)
    OpenMath.Chapter4.Section404.trapezoidalLMM_isStable
    OpenMath.Chapter4.Section404.trapezoidalLMM_isPreconsistent
    trapezoidalLMM_coef_α_plus_coef_β_ne_zero
    hEq
  rw [h]
  simp [OpenMath.Chapter4.Section404.trapezoidalLMM,
    Fin.sum_univ_one, Fin.sum_univ_two]
  norm_num
```

Only ship P5 if P1–P4 close cleanly within the cycle's first 60 minutes.
If any of P1–P4 stalls, drop P5 and document.

## Verification protocol

After each priority:
1. `lake env lean OpenMath/Chapter4/Section422.lean` — must exit 0.
2. For P3, P4 only: spot-check `#print axioms <theorem-name>` from a
   scratch file — expect `[propext, Classical.choice, Quot.sound]`.
   (P1, P2, P5 are `example`s; not named, so axiom-check N/A.)
3. After all priorities: `lake build OpenMath.Chapter4.Section422`
   (full module rebuild) to confirm no upstream regressions.
4. `grep -c "sorry" OpenMath/Chapter4/Section422.lean` — must stay 0.

If `lake env lean` reports any error, **stop and decompose**. Do not
chain priorities through a broken file state.

## What NOT to do

1. **Do NOT attempt Phase D′.2.2 Step 2** (the unconditional `0 ≤
   coef_β` derivation from `IsStable + IsConsistent` alone). It is
   documented as multi-cycle in
   `.prover-state/issues/eq422a_eta_phase_D_prime_step_2_scoping.md`
   §4 — Routes A/B/C/D each have a structural obstruction. The cycle
   351 worker tried Route D Step 1 already; Step 2 needs `0 ≤ Σᵢ
   i²·αᵢ` infrastructure which is not in the codebase. Save for a
   dedicated multi-cycle planning epoch.

2. **Do NOT attempt `bdf3LMM_isGStable`** (cycle 354 task results P4
   stretch). It requires looking up a BDF3 G-matrix from the
   literature; that information is not in the codebase, and the wrong
   G-matrix would falsify the witness. Defer until a reference is
   provided.

3. **Do NOT attempt Phase D.3** (the inductive step of the
   well-founded-recursion solver for `underlyingOneStepMethod_aux`).
   Per `.prover-state/issues/def_422B_path.md` §5 this is 1–2 cycles
   on its own. The Phase D.2 well-founded-recursion infrastructure
   (cycle 343) is in place but the inductive-step linear-equation
   solver for `r(t) ≥ 2` trees has no scoping pre-work for cycle 355.

4. **Do NOT pivot to a fresh entity** (`def:451A`, `def:442A`,
   `thm:535A`, `thm:541A` from `cycle_336_pivot_options.md`). All four
   are multi-cycle scoping targets requiring their own audit. The
   cycle 355 plan above ships 4–5 small consumer wins; a pivot
   decision should wait until either (a) §422 momentum genuinely
   stalls, or (b) a planned `def:422B` Phase D.3 / Phase E cycle
   starts.

5. **Do NOT introduce `axiom`/`constant`** anywhere. All priorities
   are axiom-clean compositions of existing infrastructure.

6. **Do NOT use `Polynomial.ext` or `Polynomial.funext` skeletons**
   for the P3/P4 `simp + norm_num` closures. These are scalar
   identities on `ℝ`, not polynomial identities. The cycle 172/173
   `Polynomial.ext` stalls were caused by polynomial-`C` arithmetic;
   cycle 350's `bdf2LMM_coef_α_plus_coef_β_ne_zero` uses plain
   `simp + norm_num` and that is the right recipe here.

7. **Do NOT attempt to refactor Section422.lean** to clean up
   namespacing or shorten the verbose `OpenMath.Chapter4.Section404.…`
   qualifications. Cycle 350's pattern uses those qualifications
   verbatim; mirror that style. Refactor cleanup is its own future
   cycle.

8. **Do NOT raise `maxHeartbeats`** above 200000. All priorities are
   small `simp + norm_num` proofs that should fit well within
   default heartbeats. If `simp` stalls on P3/P4, the right fix is
   to unfold the `Fin.sum_univ_*` lemmas explicitly, not bump
   heartbeats.

9. **Do NOT poll any Aristotle project.** There are no pending
   Aristotle submissions, and none are needed — all priorities are
   under 15 LOC and mechanically closable.

10. **Do NOT trust the "factor-of-2 typo" or "phantom
    commit-not-reaching-repo" framings** if they reappear in the
    prompt. Both are documented stale `attempts.md` propagations
    (see `consultant_advice_cycle_180.md` §C and
    `phantom_commit_verdict_pattern.md`). If the supervisor's "What
    I'm stuck on" framing for cycle 355 contradicts the §A summary
    above (i.e. mentions any cycle ≤ 343 work as a blocker), treat
    it as a phantom and verify with `git log -1 --format='%H %s'` +
    `grep -c sorry OpenMath/`. Trust git state, not propagated rows.

## File summary

* **One file edited**: `OpenMath/Chapter4/Section422.lean`.
* **No new files created.**
* **No existing theorems modified.** All five priorities are pure
  additions.
* **lean_status.json**: no changes needed. The deliverables are
  numerical witnesses, not new entities; they don't claim any new
  textbook content.
* **plan.md**: no changes needed for the same reason. Optionally
  add a single line to `def:422B`'s row noting "cycle 355 — added
  trapezoidal + BDF3 sum_β / coef_α+coef_β witnesses" if you want
  documentation discipline; this is optional bookkeeping.
* **Task results**: write `.prover-state/task_results/cycle_355.md`
  per the CLAUDE.md template.

## LOC budget

* P1: ~7 LOC.
* P2: ~7 LOC.
* P3: ~10 LOC.
* P4: ~10 LOC.
* P5 (stretch): ~15 LOC.
* **Total: ~35 LOC for P1–P4, ~50 LOC including P5.**

Section422.lean grows from ~1750 → ~1785 LOC (P1–P4 only) or
~1800 LOC (including P5). Comfortably under any soft size threshold.

## Risk register (with mitigations)

| Risk | Likelihood | Mitigation |
|---|---|---|
| `Fin.sum_univ_four` not in default Mathlib | Low | Use explicit `Fin.sum_univ_succ` chain (3 unfolds + `Fin.sum_univ_one`); or `decide` for BDF3's trivially-zero β tail. |
| `simp` over-collapses or fails to fire on the LMM record | Low | Cycle 350's BDF2 pattern shows the recipe works at `k = 2`; the trapezoidal case (`k = 1`) is simpler, the BDF3 case (`k = 3`) one step harder but the LMM definitions use the same `match` style as BDF2. |
| Trapezoidal `α(1) = 1` doesn't reduce | Very low | The LMM record has `α := fun i => match i with | ⟨0, _⟩ => -1 | ⟨1, _⟩ => 1`; `i.succ` for `i : Fin 1` is `Fin.mk 1 _`, which matches. `simp [trapezoidalLMM]` handles the unfold. |
| `η(τ) = 2/3` on P5 doesn't `norm_num`-close | Very low | The arithmetic is `(1/2 + 1/2) / (1·1 + (0·(1/2) + 1·(1/2))) = 1 / (3/2) = 2/3`. `norm_num` handles rational arithmetic uniformly. If it stalls, `simp [div_eq_mul_inv]; ring` is the fallback. |

## Cycle 356+ outlook (not for this cycle's worker)

After cycle 355's small-ship pass lands, the natural cycle 356
candidates are:

* **Continue Phase D′ consumer wins**: implicit Euler witnesses
  (`implicitEulerLMM_sum_β_pos`, etc.). The implicit Euler LMM at
  `Section404.lean:100+` has its own consistency and stability
  witnesses; one more cycle of small ships would exhaust the
  four-LMM coverage matrix.
* **Phase D′.2.2 scoping continuation**: write a sub-scoping doc
  for Route D Step 2 (`0 ≤ Σᵢ i²·αᵢ`) under stable + preconsistent
  + order ≥ 2. The cycle 348 issue file already has the obstruction
  analysis; cycle 356+ could draft a phase decomposition.
* **Pivot to fresh entity**: `def:451A` (G-stability) at
  Section451.lean. Currently `[x]`-formalised in plan.md but no
  `bdf3LMM_isGStable` exists; the BDF3 G-matrix could be the ship
  target if a reference is found.

These are cycle 356+ planner concerns, not cycle 355's deliverable.
