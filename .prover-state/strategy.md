# Cycle 356 Strategy — Phase D′ consumer coverage: Implicit Euler + Explicit Euler witnesses

## A. State at cycle start

* HEAD: `cfdfa57 Cycle 355 — §422 trapezoidal + BDF3 D′.2.0/D′.2.1
  consumer witnesses` — clean, sorry count 0.
* Cycle 355 scored +2: shipped 5 axiom-clean witnesses for
  trapezoidal and BDF3 at the cycle-349/350 §422 consumer surface.
* No Aristotle results pending. No open blockers in
  `attempts.md` (cycle 355 had no D-state zombies / no GPFS
  pathology).
* Pending tail from cycle 355 §"Suggested next approach":
  1. Continue Phase D′ consumer wins at remaining §404 LMM
     witnesses (implicit Euler) — single-cycle, mechanical.
  2. Phase D.3 scoping for `def:422B` underlying-one-step-method
     inductive step — multi-cycle, scoping-only.
  3. Phase D′.2.2 Step 2 (unconditional `0 ≤ coef_β` derivation) —
     multi-cycle, blocked per cycle 348 scoping doc.

**Cycle 356 picks option (1)** plus a stretch extension to
explicit Euler — completes the **five-LMM consumer-witness
coverage matrix** (explicit Euler + implicit Euler + trapezoidal
+ BDF2 + BDF3) for cycles 349/350's `sum_β_pos_of_stable_consistent`
and `Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened`
ships. Highest-confidence single-cycle deliverable; no risk of
streak-burnout because every ship is a mechanical clone of the
cycle 355 P1–P5 recipe.

## B. Mandatory deliverables (P1–P4) — Implicit Euler witnesses

All five primary ships live in `OpenMath/Chapter4/Section422.lean`,
inserted after the existing `bdf3LMM_coef_α_plus_coef_β_ne_zero`
theorem (currently at line ~1177 — verify before insertion via
`grep -n bdf3LMM_coef_α_plus_coef_β_ne_zero` if uncertain).

Implicit Euler coefficients (`OpenMath/Chapter4/Section404.lean:100`):
* `α := fun i => if i = 0 then -1 else 1` (i.e. `α 0 = -1, α 1 = 1`).
* `β := fun i => if i = 0 then 1 else 0` (i.e. `β 0 = 1, β 1 = 0`).

Pre-flight arithmetic (paper-verify before writing Lean):
* `coef_α(implicitEulerLMM) = Σᵢ:Fin 1, (i+1)·α(i.succ) = 1·α 1 = 1`.
* `coef_β(implicitEulerLMM) = Σᵢ:Fin 2, i·β(i) = 0·1 + 1·0 = 0`.
* `sum_β(implicitEulerLMM) = Σᵢ:Fin 2, β(i) = 1 + 0 = 1`.
* `coef_α + coef_β = 1 + 0 = 1 ≠ 0`. ✓
* `η(τ) = sum_β / (coef_α + coef_β) = 1 / 1 = 1`. ✓

### P1 — `implicitEulerLMM_sum_β_pos` (anonymous example, ~7 LOC)

Mechanical clone of cycle 355's P1/P2. **Verify** with
`grep` first that `implicitEulerLMM_isStable` and
`implicitEulerLMM_isConsistent` exist in Section404.lean
(they do — line 262 and 161 respectively).

```lean
/-- *Phase D′.2.0 implicit Euler non-vacuity (cycle 356):* the cycle
349 `sum_β_pos_of_stable_consistent` fires on implicit Euler; the
β-sum equals `1 + 0 = 1 > 0`. -/
example : 0 < ∑ i : Fin 2,
    OpenMath.Chapter4.Section404.implicitEulerLMM.β i :=
  sum_β_pos_of_stable_consistent
    OpenMath.Chapter4.Section404.implicitEulerLMM
    (by norm_num : (0 : ℕ) < 1)
    OpenMath.Chapter4.Section404.implicitEulerLMM_isStable
    OpenMath.Chapter4.Section404.implicitEulerLMM_isConsistent
```

### P2 — `implicitEulerLMM_coef_α_plus_coef_β_ne_zero` (named theorem, ~10 LOC)

Mechanical clone of cycle 355's `trapezoidalLMM_coef_α_plus_coef_β_ne_zero`
template at lines 1163–1173 (since trapezoidal is also `k = 1`).

```lean
/-- *Implicit Euler D′.2.1 non-vanishing witness (cycle 356):*
implicit Euler's denominator `coef_α + coef_β = 1 + 0 = 1 ≠ 0`.
Numerical witness for the cycle 350 weakened-hypothesis ship at
the implicit Euler LMM. -/
theorem implicitEulerLMM_coef_α_plus_coef_β_ne_zero :
    (∑ i : Fin 1, ((i.val + 1 : ℕ) : ℝ) *
        OpenMath.Chapter4.Section404.implicitEulerLMM.α i.succ)
      + (∑ i : Fin 2, ((i.val : ℕ) : ℝ) *
            OpenMath.Chapter4.Section404.implicitEulerLMM.β i) ≠ 0 := by
  simp [OpenMath.Chapter4.Section404.implicitEulerLMM,
    Fin.sum_univ_two]
  norm_num
```

**Linter note**: `Fin.sum_univ_one` is NOT needed here (per cycle
355 P3's task results — the `Fin 1` α-side reduces via the
`Fin.sum_univ_two` β-side cascade plus `Fin.sum_univ_succ`).
If the `unusedSimpArgs` linter flags anything, drop it; do **not**
add `Fin.sum_univ_one`.

### P3 — End-to-end implicit Euler η witness (anonymous example, ~15 LOC)

Mechanical clone of cycle 355 P5 (trapezoidal) with `2/3` swapped
to `1`. Mirror the cycle 350 BDF2 example at lines 1209–1223 (which
also concludes `η(τ) = 1`).

```lean
/-- *Non-vacuity for the cycle 356 implicit Euler ship:* end-to-end
exercise of `Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened`
on implicit Euler, discharging the weakened non-vanishing hypothesis
via `implicitEulerLMM_coef_α_plus_coef_β_ne_zero`. The
underlying-one-step-method `η ∈ G₁` corresponding to implicit Euler
pins `η(τ) = 1` (same numerical conclusion as BDF2 and cycle 346's
witness). -/
example (η_q : Quotient PhiEquivalent.setoidSigma)
    (hEq : Eq422a OpenMath.Chapter4.Section404.implicitEulerLMM η_q) :
    elementaryWeightQ_phi η_q RootedTree.vertex = 1 := by
  have h := Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened
    OpenMath.Chapter4.Section404.implicitEulerLMM
    (by norm_num : (0 : ℕ) < 1)
    OpenMath.Chapter4.Section404.implicitEulerLMM_isStable
    OpenMath.Chapter4.Section404.implicitEulerLMM_isPreconsistent
    implicitEulerLMM_coef_α_plus_coef_β_ne_zero
    hEq
  rw [h]
  simp [OpenMath.Chapter4.Section404.implicitEulerLMM,
    Fin.sum_univ_two]
  norm_num
```

### P4 — Explicit Euler companion ships (stretch primary, ~30 LOC total)

Explicit Euler is the original 1-step LMM and the symmetric partner
to implicit Euler — its absence from the §422 consumer matrix is the
biggest remaining coverage hole. Ship P4a + P4b + P4c following the
P1+P2+P3 pattern.

Pre-flight arithmetic (paper-verify):
* `coef_α(explicitEulerLMM) = 1·α 1 = 1`.
* `coef_β(explicitEulerLMM) = 0·β 0 + 1·β 1 = 0 + 1 = 1`.
* `sum_β = β 0 + β 1 = 0 + 1 = 1`.
* `coef_α + coef_β = 1 + 1 = 2 ≠ 0`. ✓
* `η(τ) = 1 / 2`. ✓

**P4a** — `explicitEulerLMM_sum_β_pos` example (~7 LOC):

```lean
example : 0 < ∑ i : Fin 2,
    OpenMath.Chapter4.Section404.explicitEulerLMM.β i :=
  sum_β_pos_of_stable_consistent
    OpenMath.Chapter4.Section404.explicitEulerLMM
    (by norm_num : (0 : ℕ) < 1)
    OpenMath.Chapter4.Section404.explicitEulerLMM_isStable
    OpenMath.Chapter4.Section404.explicitEulerLMM_isConsistent
```

**P4b** — `explicitEulerLMM_coef_α_plus_coef_β_ne_zero` theorem
(~10 LOC):

```lean
theorem explicitEulerLMM_coef_α_plus_coef_β_ne_zero :
    (∑ i : Fin 1, ((i.val + 1 : ℕ) : ℝ) *
        OpenMath.Chapter4.Section404.explicitEulerLMM.α i.succ)
      + (∑ i : Fin 2, ((i.val : ℕ) : ℝ) *
            OpenMath.Chapter4.Section404.explicitEulerLMM.β i) ≠ 0 := by
  simp [OpenMath.Chapter4.Section404.explicitEulerLMM,
    Fin.sum_univ_two]
  norm_num
```

**P4c** — End-to-end explicit Euler η witness, pinning `η(τ) = 1/2`
(~15 LOC):

```lean
example (η_q : Quotient PhiEquivalent.setoidSigma)
    (hEq : Eq422a OpenMath.Chapter4.Section404.explicitEulerLMM η_q) :
    elementaryWeightQ_phi η_q RootedTree.vertex = 1 / 2 := by
  have h := Eq422a_at_vertex_eta_eq_of_stable_preconsistent_weakened
    OpenMath.Chapter4.Section404.explicitEulerLMM
    (by norm_num : (0 : ℕ) < 1)
    OpenMath.Chapter4.Section404.explicitEulerLMM_isStable
    OpenMath.Chapter4.Section404.explicitEulerLMM_isPreconsistent
    explicitEulerLMM_coef_α_plus_coef_β_ne_zero
    hEq
  rw [h]
  simp [OpenMath.Chapter4.Section404.explicitEulerLMM,
    Fin.sum_univ_two]
  norm_num
```

P4 satisfies CLAUDE.md non-vacuity at maximum density: the *single
oldest* canonical 1-step LMM `explicitEulerLMM` is now wired all the
way into the cycle 350 underlying-one-step-method machinery.

## C. Order of operations

1. **Pre-flight** (5 min): `grep -n implicitEulerLMM_isConsistent
   OpenMath/Chapter4/Section404.lean` (must return line 161),
   `grep -n bdf3LMM_coef_α_plus_coef_β_ne_zero
   OpenMath/Chapter4/Section422.lean` (insertion-point anchor),
   paper-verify the four arithmetic claims in §B above.
2. **Ship P1** (5 min): append example after the cycle 355
   `bdf3_sum_β_pos` example (line ~1070 area).
3. **Ship P2** (5 min): append theorem after
   `bdf3LMM_coef_α_plus_coef_β_ne_zero` (line ~1177–1185).
4. **Ship P3** (10 min): append end-to-end example after the
   cycle 355 trapezoidal end-to-end example (line ~1203).
5. **Ship P4a–P4c** (15 min): append in parallel blocks after the
   implicit Euler trio.
6. **Verify** (5 min): `lake env lean OpenMath/Chapter4/Section422.lean`
   passes clean; `#print axioms` on P2 and P4b returns
   `[propext, Classical.choice, Quot.sound]`.
7. **Housekeeping** (5 min): `attempts.md` row, `task_results/cycle_356.md`,
   no `lean_status.json` change (no entity status changes — these are
   all non-vacuity witnesses), no `plan.md` change.

Total: ~50 min of focused work, ~70 LOC added.

## D. What NOT to do

* **Do NOT** attempt to drop the cycle 350 weakened-hypothesis form
  in favor of the unconditional `Eq422a_at_vertex_eta_eq_of_stable_consistent`
  bottom-line corollary. The unconditional form (cycle 350 P3
  stretch ship) requires showing
  `Σᵢ (i+1) · βᵢ ≠ 0` from `IsStable + IsConsistent` alone, which
  is exactly the Phase D′.2.2 Step 2 multi-cycle blocker per
  `.prover-state/issues/eq422a_eta_phase_D_prime_step_2_scoping.md`.
  All cycle 356 witnesses must route through the *weakened*
  `_weakened` form.
* **Do NOT** introduce any new `def` or `class`/`structure`.
  Everything is named-`theorem` or anonymous `example`. No
  faithfulness audit ambiguity.
* **Do NOT** open new `sorry`s, even temporarily. The cycle 200/201
  rollback precedent is in force; sorry-first scaffolds for
  multi-cycle work are forbidden.
* **Do NOT** introduce `axiom`/`constant` declarations.
* **Do NOT** raise `maxHeartbeats`. The recipe is `simp + norm_num`
  on tiny `Fin 2` sums — no heartbeats blow-up risk.
* **Do NOT** add `Fin.sum_univ_one` to any simp set per cycle 355's
  task-results §"Discovery" linter note. At `k = 1` LMMs, the α-side
  reduces via the β-side cascade.
* **Do NOT** rewrite, refactor, or rename any existing trapezoidal /
  BDF2 / BDF3 witnesses. Cycle 355's ships are stable.
* **Do NOT** pivot to Phase D.3 scoping in this cycle. Phase D.3 is
  the next-cycle (357+) candidate after the consumer matrix is full.
* **Do NOT** touch `OpenMath/Chapter4/Section441.lean`. The 43+
  consecutive GPFS timeout pathology
  (`.prover-state/issues/cycle_182_gpfs_slowness.md`) is still in
  force; even read-only smoke tests on §441 cost the cycle budget.
  Cycle 356's deliverables are entirely in `Section404.lean` /
  `Section422.lean` (warm-rebuild healthy throughout cycles 336–355).
* **Do NOT** edit `scripts/autonomous_loop.py`. The cycle 248 / 263
  empty-stuck-on phantom recommendation is loop-maintainer territory.

## E. Failure modes / fallbacks

* **F1**: `simp` fails to reduce `if i = 0` discriminant on the
  implicit-Euler / explicit-Euler β-side. Mitigation: change
  `simp [implicitEulerLMM, Fin.sum_univ_two]` to `simp only
  [implicitEulerLMM, Fin.sum_univ_two, Fin.isValue]; decide` or
  add `show ...` reframing to lift the `Fin` indices to literals.
  *Probability: very low* — cycle 355 P3/P5 used the identical
  pattern at trapezoidal (also `α = (-1, 1)` with `if i = 0`) and
  closed cleanly.
* **F2**: P4 (explicit Euler) is in scope but cycle drift would
  push beyond budget. Mitigation: P4 is a strict superset of the
  P1–P3 deliverable; if P4 stalls, ship P1+P2+P3 only and leave
  explicit Euler for cycle 357. Both partial and full ships
  satisfy CLAUDE.md non-vacuity.
* **F3**: Aristotle returns an unexpected result mid-cycle (none
  pending at cycle start). Mitigation: no Aristotle dependency in
  cycle 356 deliverables. Any returned result is processed via
  the standard incorporate-or-defer flow without affecting the
  P1–P4 plan.
* **F4**: A linter false-positive flags one of the `simp` arguments
  as unused. Mitigation: drop the flagged argument and re-verify;
  do **not** add new arguments to silence the linter.

## F. Cycle-completion checklist

* [ ] P1 implicit Euler `sum_β_pos` example shipped.
* [ ] P2 implicit Euler `_coef_α_plus_coef_β_ne_zero` theorem shipped.
* [ ] P3 implicit Euler end-to-end η = 1 example shipped.
* [ ] P4a explicit Euler `sum_β_pos` example shipped (stretch).
* [ ] P4b explicit Euler `_coef_α_plus_coef_β_ne_zero` theorem
      shipped (stretch).
* [ ] P4c explicit Euler end-to-end η = 1/2 example shipped (stretch).
* [ ] `lake env lean OpenMath/Chapter4/Section422.lean` clean.
* [ ] `grep -c sorry OpenMath/Chapter4/Section422.lean` returns 0.
* [ ] `#print axioms` on P2 and P4b returns
      `[propext, Classical.choice, Quot.sound]`.
* [ ] No tautology-scanner false positives:
      `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$'
      OpenMath/Chapter4/Section422.lean` returns no hits.
* [ ] `task_results/cycle_356.md` records all ships, axioms,
      non-vacuity discharge, faithfulness check (P2 and P4b only
      since they are the named theorems; the four `example`s have
      no entity IDs).
* [ ] `attempts.md` cycle 356 row reflects clean ship.
* [ ] No `lean_status.json` / `plan.md` changes (no entity status
      transitions).

## G. Cycle 357+ outlook

After this cycle fills the consumer matrix, the natural priorities
are (in recommendation order):

1. **Phase D.3 scoping** (multi-cycle prep): write a dedicated
   `.prover-state/issues/def_422B_phase_D_inductive_step_plan.md`
   document for the `underlyingOneStepMethod_aux` inductive step
   (per `def_422B_path.md` §5 Phase D.3 — 1–2 cycle estimate). The
   scoping doc should pin the linear-equation-solver structure for
   `r(t) ≥ 2` trees, identify Mathlib hooks for the `RootedTree`
   well-founded recursion (already shipped cycle 343), and decide
   between Shape (i) constructive vs Shape (ii) `Classical.choose`
   per `def_422B_path.md` §2. This is the highest-leverage next
   cycle if the planner wants to keep moving toward sealing
   `def:422B`.
2. **Pivot to fresh entity**: with 20+ consecutive §422 cycles
   (336–356), a fresh-entity pivot may be warranted. Candidates per
   `cycle_336_pivot_options.md`: `def:451A` (G-stability witnesses),
   `thm:535A` (one-step underlying method for GLMs), `thm:541A`
   (DIMSIM types). All low-risk single-cycle ships.
3. **Continue Phase D′ refinement** (low-priority, marginal):
   `Eq422a_at_vertex_eta_eq_of_stable_consistent` (unconditional
   form, blocked on Phase D′.2.2 Step 2 per
   `eq422a_eta_phase_D_prime_step_2_scoping.md`). This is the
   *blocked* unconditional form; would require Route A/B/C/D
   resolution per that scoping doc. Multi-cycle — not single-cycle.

Cycle 357's planner should consult the cycle-356 task results
before committing.
