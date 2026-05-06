# Cycle 161 Strategy

## Status snapshot

* **Sorry count: 0** — clean.
* Cycle 160 (just landed, score 1): refactored the cycle 153 / 156 /
  159 inline T1+T2 closure body at p = 0 into a private helper
  `taylor_lipschitz_explicitEuler_orderZero_diff_isBigO`, mirroring
  cycle 158's p = 1 helper extraction. Net −83 LOC; all thirteen
  affected theorems re-verified axiom-clean.
* `def:530B`/`def:530C` Path A non-vacuity grid stands at
  r ∈ {1, 2, 3} × p ∈ {0, 1} — saturated through r = 3.
* Path B (implicit, fixed-point) remains deferred per
  `.prover-state/issues/def_530B_scaffold_strategy.md`.
* No pending Aristotle results.
* No active blockers escalated by the previous cycle.

## What I considered

| Candidate | Verdict |
|---|---|
| **Option 1** — `r`-parametric `paddedRDEulerGLM (r : ℕ)` family (cycle 160 worker's #1, recommended). | Genuinely multi-cycle: the existing `padded{2,3}DEulerGLM` use literal `!![…]` matrices (Section520.lean:1286–1303), so generalising to `Matrix.of (fun i j => …)` plus per-row case analysis is a structural rewrite, not a port. Phase A (definitions + IsExplicit) alone is ~150 LOC; phase B (order witnesses by induction on r) needs new induction infrastructure because each `r` is a distinct GLM type. Sorry-first scaffolding is ruled out by the cycle 138/149 rollback precedent. Single-cycle delivery would land foundation only (score ≤ 1, risk of stall). Defer to cycle 162+ once the r = 4 data point validates the pattern. |
| **Option 2 — r = 4 mechanical lift (Backup A from cycle 160 strategy).** | Mechanical port of cycle 159's r = 3 work. ≈8 axiom-clean theorems; ≈300 LOC. Cycles 158 + 160 helpers reduce both i = 0 channels (p = 0 and p = 1) to one-liners. Validates both helpers at a fourth call site, strengthening the case for option 1 in cycle 162. Known-tractable single-cycle deliverable. **Selected.** |
| Option 3 — p = 2 witness via second-order GLM (RK2 / midpoint). | Explicit Euler is genuinely first-order: `SM − ES` for explicit Euler is `O(h²)` not `O(h³)`. A p = 2 witness needs a higher-order GLM, which means: a new GLM definition, a new `c`-coefficients-matched starting method, a Taylor-degree-3 helper sibling of cycles 158/160. Multi-cycle. |
| Option 4 — Path B (implicit method via `ContractingWith`). | Multi-cycle infrastructure deferred per the standing issue. |
| Pivot to fresh entity (cycle 160 strategy's table re-checked: `def:451A`, `def:422B`, `thm:381G`, `thm:521B`). | All flagged multi-cycle by cycle 160's planner; revisiting them this cycle without scouting is high-variance. |

## Cycle 161 target — r = 4 mechanical lift (Backup A)

**Goal**: lift cycles 156/157/159's r ∈ {2, 3} non-vacuity grid for
`def:530B`/`def:530C` Path A to r = 4 by mirroring cycle 159's r = 3
deliverables. This produces 8 axiom-clean theorems with sorry count
held at 0, validates cycles 158 + 160 helpers at a fourth call site
each, and provides the four-data-point evidence base that cycle 162
will need to commit to the r-parametric refactor.

**Note on duplication**: yes, this adds ≈300 LOC of duplication that
the eventual cycle 162+ r-parametric refactor will eliminate. That is
acceptable single-cycle cost — option 1's multi-cycle scope is the
larger risk, and r = 4 is the lowest-effort way to confirm cycles
158/160 helpers continue to apply mechanically before committing to
a parametric rewrite.

## Concrete steps

### Step 1 — Confirm context (5 min)

Use `lean_file_outline` on `OpenMath/Chapter5/Section520.lean` and
`OpenMath/Chapter5/Section530.lean`. Locate:
* `padded3DEulerGLM` definition (Section520, ≈line 1299).
* `padded3DEulerGLM_isExplicit`, `padded3DEulerGLM_isIRKStable` /
  related theorems (Section520, after the definition).
* `pad3CompatMethod`, `pad3CompatStartingMethod`, the four
  `pad3CompatStartingMethod_*` helpers, and the two
  `padded3DEulerGLM_hasOrder{Zero,One}_pad3CompatStarting` witnesses
  + `padded3DEulerGLM_hasOrder{Zero,One}` def:530C wrappers
  (Section530).
* The two cycle-158/160 helpers
  `taylor_lipschitz_explicitEuler_orderZero_diff_isBigO` and
  `taylor_lipschitz_explicitEuler_orderOne_diff_isBigO` (Section530).
* The cycle-156 private helper `zeroGeneralizedRK_explicitApply`
  (Section530, near `padCompatStartingMethod_applyExplicit`) — this
  must be reused at r = 4, NOT re-introduced.

Do NOT use bare `Read` on these files (each is >1500 LOC). Use
`lean_file_outline` for skeletons + targeted `Read` with `offset`
+ `limit`.

### Step 2 — Add `padded4DEulerGLM` to Section520

Place immediately after `padded3DEulerGLM` (≈line 1303). The
4×4 V matrix follows the same pattern as r = 3: row 0 is `[1, 0, 0, 0]`
(the active channel); rows 1, 2, 3 are zero rows.

```lean
/-- A 4-padded explicit-Euler GLM `(s, r) = (1, 4)` (cycle 161):
row 0 carries the genuine explicit-Euler step (`U[0,0] = 1`,
`B[0,0] = 1`); rows 1, 2, 3 are passively decoupled zero channels
(`B[i][·] = 0`, `V[i][·] = 0` for `i ≥ 1`). Lifts cycle 159's
`padded3DEulerGLM` from r = 3 to r = 4. Used by Section 530 to
land the `r = 4` non-vacuity witnesses for `def:530B` and
`def:530C`. -/
def padded4DEulerGLM : GeneralLinearMethod 1 4 where
  A := !![0]
  U := !![1, 0, 0, 0]
  B := !![1; 0; 0; 0]
  V := !![1, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
```

**Out of scope for cycle 161**: the analogous `IsRKStable`,
`IsIRKStable`, `IsAStable` (negative), `IsLStable` (negative)
witnesses for `padded4DEulerGLM` that cycles 133/134/146 produced
for `padded2DEulerGLM`. Cycle 159 deliberately left them out for
`padded3DEulerGLM` ("No new Section520 corollaries (...) added —
out of scope this cycle"). Follow the cycle 159 precedent.

### Step 3 — Add `pad4CompatMethod`, `pad4CompatStartingMethod`, support helpers to Section530

Place immediately after `pad3CompatStartingMethod_applyExplicit`'s
closing block (search for `end pad3CompatStartingMethod_applyExplicit`
or the tail of cycle 159's helpers). Mirror the cycle 159 layout
exactly:

```lean
/-- Per-row constituent generalized-RK methods compatible with
`padded4DEulerGLM` (cycle 161). Index 0 is the active explicit-Euler
channel via `trivialGeneralizedRK`; indices 1, 2, 3 are zero
channels via `zeroGeneralizedRK`. -/
def pad4CompatMethod : Fin 4 → GeneralizedRungeKuttaMethod 1
  | ⟨0, _⟩ => trivialGeneralizedRK
  | ⟨1, _⟩ => zeroGeneralizedRK
  | ⟨2, _⟩ => zeroGeneralizedRK
  | ⟨3, _⟩ => zeroGeneralizedRK

/-- Cycle 161 starting method paired with `padded4DEulerGLM`:
row 0 active (`b₀ = 1`), rows 1, 2, 3 inactive (`b₀ = 0`). -/
noncomputable def pad4CompatStartingMethod : StartingMethod 4 :=
  ⟨fun _ => 1, pad4CompatMethod⟩

theorem pad4CompatStartingMethod_isNonDegenerate :
    pad4CompatStartingMethod.IsNonDegenerate := by
  rw [StartingMethod.isNonDegenerate_iff_exists_b₀_ne_zero]
  refine ⟨⟨0, by omega⟩, ?_⟩
  simp [pad4CompatStartingMethod, pad4CompatMethod, trivialGeneralizedRK]

theorem pad4CompatStartingMethod_constituents_isExplicit :
    ∀ i, ((pad4CompatStartingMethod.method i)).IsExplicit := by
  intro i
  fin_cases i
  · exact trivialGeneralizedRK_isExplicit
  · intro a b _; fin_cases a; fin_cases b; rfl
  · intro a b _; fin_cases a; fin_cases b; rfl
  · intro a b _; fin_cases a; fin_cases b; rfl

theorem padded4DEulerGLM_isExplicit : padded4DEulerGLM.IsExplicit := by
  intro i j _; fin_cases i; fin_cases j; rfl

theorem pad4CompatStartingMethod_applyExplicit
    (f : ℝ → ℝ) (y₀ h : ℝ) :
    pad4CompatStartingMethod.applyExplicit
        pad4CompatStartingMethod_constituents_isExplicit f y₀ h
      = ![y₀ + h * f y₀, 0, 0, 0] := by
  funext i
  fin_cases i
  · -- Index 0: active trivialGeneralizedRK
    exact trivialGeneralizedRK_explicitApply f y₀ h
  · -- Index 1: zero channel
    exact zeroGeneralizedRK_explicitApply f y₀ h
  · exact zeroGeneralizedRK_explicitApply f y₀ h
  · exact zeroGeneralizedRK_explicitApply f y₀ h
```

The exact `trivialGeneralizedRK_explicitApply` /
`zeroGeneralizedRK_explicitApply` invocations should be lifted
verbatim from `pad3CompatStartingMethod_applyExplicit` (cycle 159).
If the function-extensionality + `fin_cases` shape needs adjustment
(e.g. `Fin.cases` vs `Matrix.cons`), use `lean_multi_attempt` with
the cycle 159 closure as a template.

### Step 4 — Add the two `HasOrderRelativeTo_explicit` witnesses to Section530

Place immediately after `padded3DEulerGLM_hasOrderOne_pad3CompatStarting`.
Use the cycle 159 r = 3 witnesses as templates; the only
substantive difference is r = 4 has four `fin_cases` arms instead
of three.

#### Step 4a — `padded4DEulerGLM_hasOrderZero_pad4CompatStarting` (p = 0)

Structure (mirrors cycle 159's p = 0 witness):

```lean
theorem padded4DEulerGLM_hasOrderZero_pad4CompatStarting
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_deriv_x₀ : HasDerivAt yex (f y₀) x₀) :
    HasOrderRelativeTo_explicit padded4DEulerGLM pad4CompatStartingMethod
      pad4CompatStartingMethod_constituents_isExplicit
      padded4DEulerGLM_isExplicit
      0 f yex x₀ y₀ := by
  intro i
  fin_cases i
  · -- i = 0: active channel — apply cycle-160 helper as one-liner
    -- Closed-form rewrites for SM[0] and ES[0] follow cycle 159's
    -- i = 0 closure verbatim, then the cycle-160 helper closes.
    sorry  -- replace with the i = 0 closure body (≈30 LOC, port from cycle 159)
  · -- i = 1: zero channel — `Asymptotics.isBigO_zero`
    sorry  -- replace with cycle 159's i = 1 zero-collapse (≈10 LOC)
  · -- i = 2: zero channel — same
    sorry
  · -- i = 3: zero channel — same
    sorry
```

For the i = 0 channel: copy verbatim the cycle 159 i = 0 channel body
of `padded3DEulerGLM_hasOrderZero_pad3CompatStarting`. The `applyExplicit`
component values may differ in shape (Matrix.cons depth at index 0
on a `Fin 4` matrix vs a `Fin 3` matrix), so be prepared for a
`Matrix.cons_val_zero` / `Matrix.cons_val_succ` simp invocation in
the closed-form rewrites.

For the i ≥ 1 channels: the body should be a textually-identical
copy of cycle 159's i = 1 (or i = 2) zero-collapse, since those
cases differ only in the `Fin r` index value.

#### Step 4b — `padded4DEulerGLM_hasOrderOne_pad4CompatStarting` (p = 1)

Mirror cycle 159's p = 1 witness. The i = 0 channel is again
discharged by a one-line invocation of the cycle-158 helper
`taylor_lipschitz_explicitEuler_orderOne_diff_isBigO` after the
SM[0]/ES[0] closed-form rewrites and an `h^(1+1) = h^2` collapse.
The i = 1, 2, 3 channels are zero-collapses with exponent `h^(1+1)`.

### Step 5 — Add the two def:530C wrappers to Section530

Place immediately after the cycle 159 def:530C wrappers. Pure
existential closure citing the two witnesses from Step 4:

```lean
theorem padded4DEulerGLM_hasOrderZero
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_deriv_x₀ : HasDerivAt yex (f y₀) x₀) :
    HasOrder_explicit padded4DEulerGLM padded4DEulerGLM_isExplicit
      0 f yex x₀ y₀ := by
  refine ⟨pad4CompatStartingMethod,
          pad4CompatStartingMethod_constituents_isExplicit, ?_, ?_⟩
  · exact pad4CompatStartingMethod_isNonDegenerate
  · exact padded4DEulerGLM_hasOrderZero_pad4CompatStarting hf_lip hyex_x₀ hyex_deriv_x₀
```

Likewise for `padded4DEulerGLM_hasOrderOne`. Match the cycle 159
wrappers' hypothesis lists exactly (the p = 1 wrapper takes a
stronger hypothesis package: `ContDiff ℝ 2 yex` plus the genuine
ODE relation `∀ x, HasDerivAt yex (f (yex x)) x`).

### Step 6 — Verification

1. `lake env lean OpenMath/Chapter5/Section520.lean` exits 0.
2. `lake env lean OpenMath/Chapter5/Section530.lean` exits 0.
3. `lake env lean OpenMath/Chapter5.lean` exits 0.
4. `grep -c sorry OpenMath/Chapter5/Section520.lean` → 0.
5. `grep -c sorry OpenMath/Chapter5/Section530.lean` → 0.
6. `lean_verify` axiom-clean check on each new declaration:
   - `OpenMath.Chapter5.Section520.padded4DEulerGLM` (definition,
     should report no axioms)
   - `OpenMath.Chapter5.Section530.pad4CompatStartingMethod_isNonDegenerate`
   - `OpenMath.Chapter5.Section530.pad4CompatStartingMethod_constituents_isExplicit`
   - `OpenMath.Chapter5.Section530.padded4DEulerGLM_isExplicit`
   - `OpenMath.Chapter5.Section530.pad4CompatStartingMethod_applyExplicit`
   - `OpenMath.Chapter5.Section530.padded4DEulerGLM_hasOrderZero_pad4CompatStarting`
   - `OpenMath.Chapter5.Section530.padded4DEulerGLM_hasOrderOne_pad4CompatStarting`
   - `OpenMath.Chapter5.Section530.padded4DEulerGLM_hasOrderZero`
   - `OpenMath.Chapter5.Section530.padded4DEulerGLM_hasOrderOne`

   Expected for each theorem:
   `[propext, Classical.choice, Quot.sound]`.

7. Tautology-scanner regex
   `:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$` clean on
   both files.

### Step 7 — Bookkeeping

* Update `extraction/formalization_data/lean_status.json` row for
  `def:530B` and `def:530C`: bump `cycle` field from 160 to 161;
  status remains `partial` (Path B still deferred).
* Update the cycle row in `plan.md` for `def:530B` and `def:530C`
  to mention the cycle 161 r = 4 lift.
* Update `.prover-state/issues/def_530B_scaffold_strategy.md` with
  a new "Cycle 161 update" subsection describing the r = 4
  deliverables (mirror the cycle-159 update format).
* Write `.prover-state/task_results/cycle_161.md` per the standard
  format.

## What NOT to try

* Do **NOT** attempt the r-parametric refactor (option 1) this
  cycle. It is multi-cycle work; this cycle's brief is r = 4 lift
  only. The four-data-point baseline (r ∈ {1, 2, 3, 4}) created by
  this cycle is the prerequisite for cycle 162's parametric
  attempt.
* Do **NOT** attempt p = 2 witness — explicit Euler's SM−ES is
  genuinely `O(h²)`, so p = 2 needs a higher-order GLM. Out of
  scope.
* Do **NOT** add the analogous `IsRKStable`, `IsIRKStable`,
  `IsAStable` (negative), `IsLStable` (negative) witnesses for
  `padded4DEulerGLM`. Cycle 159 deliberately omitted these for
  `padded3DEulerGLM` and the same scope discipline applies here.
* Do **NOT** re-introduce `zeroGeneralizedRK_explicitApply` or
  `trivialGeneralizedRK_explicitApply` — both are already defined
  (former in cycle 156, latter in cycle 152) and reused by the
  cycle 159 r = 3 closures.
* Do **NOT** sorry-first scaffold the whole r = 4 grid. Cycles
  138 / 149 rolled back sorry-first scaffolds with score −2; the
  cycle 159 precedent is to land each axiom-clean as you go. If
  Step 4a's i = 0 channel stalls, fall back to delivering only the
  Step 2/3 infrastructure plus Step 4a's i ≥ 1 zero-collapses (no
  net sorry change), and write the rest as deferred to cycle 162.
* Do **NOT** modify `scripts/autonomous_loop.py` — the
  tautology-scanner rename workaround is established (cycle 121's
  precedent and `tautology_scanner_false_positives.md`). If Lean
  hypothesis names trigger the regex, rename `h_<name>` →
  `h<name>` at the four touch-points.
* Do **NOT** raise `maxHeartbeats` above 200000.
* Do **NOT** start a new Aristotle batch. r = 4 lift is mechanical
  port territory; Aristotle adds no value here.
* Do **NOT** poll any prior Aristotle projects (`2c4630b2-…` for
  thm:550A, `9643742d-…` etc.). They are either cancelled or
  deprioritized; not on this cycle's path.

## Backup plans

### Backup A — Step 4a's i = 0 channel stalls

If the SM[0]/ES[0] closed-form rewrites in
`padded4DEulerGLM_hasOrderZero_pad4CompatStarting` fail to reduce
to the cycle-160 helper's input shape after one round of
`lean_multi_attempt` debugging:

* Land Steps 2, 3, and 4b (p = 1) only. The p = 1 witness's i = 0
  channel uses the cycle-158 helper, which has been validated at
  three call sites (cycles 154/157/159) so should port mechanically.
* Skip Step 4a entirely (do not commit a sorry'd version). Document
  the deferral in `cycle_161.md` and update the
  `def_530B_scaffold_strategy.md` issue file accordingly.
* Net deliverable: 7 axiom-clean theorems instead of 9 (Section520
  definition + 4 Section530 helpers + p = 1 witness + p = 1
  wrapper). Sorry count remains 0.

### Backup B — Section520 definition or Section530 helpers stall

Highly unlikely (cycle 159 r = 3 used the same template), but if a
Lean tactic fails:

* Submit the failing fragment as a fire-and-forget Aristotle job
  (single submission, not five). Do NOT poll until cycle 162.
* In the meantime, strip the cycle to whatever has compiled
  axiom-clean. As long as ≥1 new axiom-clean theorem lands and
  sorry count holds at 0, the cycle has positive net progress.

### Backup C — Pivot to r-parametric refactor (option 1) Phase A

If Step 2/3 lands smoothly but reveals a structural simplification
that makes option 1 more tractable than estimated, consider
abandoning Step 4 and instead:

* Define `paddedRDEulerGLM (r : ℕ) (hr : 0 < r) : GeneralLinearMethod 1 r`
  using `Matrix.of (fun i j => if i = 0 ∧ j = 0 then 1 else 0)`-style
  parametric construction.
* Prove `paddedRDEulerGLM_isExplicit` for general `r`.
* Define `padRCompatStartingMethod (r : ℕ) (hr : 0 < r) : StartingMethod r`
  parametrically and prove
  `padRCompatStartingMethod_isNonDegenerate`.
* Show definitional / propositional equality with the existing
  `padded2DEulerGLM`, `padded3DEulerGLM`, `padded4DEulerGLM` (if
  Step 2 landed), `pad{2,3,4}CompatStartingMethod` instances.

This is **not the recommended path** — only invoke it if Steps 2/3
produce evidence that the parametric construction is materially
simpler than estimated. Default behavior is to complete Step 4
mechanically.

## Faithfulness check reminders

Per CLAUDE.md, run for every new `def` or `theorem` introduced
this cycle. The r = 4 lift introduces zero new mathematical
content — it is a parametric extension of cycles 156/159's r ∈
{2, 3} non-vacuity grid for `def:530B` (Order relative to
starting method, Path A) and `def:530C` (Order, Path A
existential). The faithfulness check is a no-op (no textbook
divergence introduced); document this in `cycle_161.md` per the
cycle 159 precedent.

In particular:
* No new textbook-named concepts (the relevant entities are
  `def:530B`/`def:530C`, already introduced in cycles 151–155).
* No new `class`/`structure` declarations.
* No tautology-pattern violations expected.
* Hypothesis-strength check: the witness signatures should match
  cycle 159's r = 3 witnesses verbatim. If a hypothesis is added
  or strengthened, that is a deviation requiring justification —
  flag it explicitly.

## Bottom line

Cycle 161 = mechanical r = 4 port of cycle 159's r = 3
deliverables. Target: 8–9 axiom-clean theorems in Section520 +
Section530, sorry count held at 0, cycles 158/160 helpers
validated at fourth call sites. Estimated 60–90 minutes worker
time. Score expectation: 2 (substantive non-vacuity additions per
the 156/157/159 precedent).
