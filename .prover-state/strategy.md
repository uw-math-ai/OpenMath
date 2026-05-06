# Cycle 157 Strategy — `def:530B`/`def:530C` Path A: r=2 × p=1 non-vacuity witness

## Context (current state at HEAD `bab500d`)

* Sorry count: **0**. Hold this invariant.
* `def:530B`/`def:530C` Path A coverage so far:
  | shape           | p=0                  | p=1                  |
  |-----------------|----------------------|----------------------|
  | (s,r)=(1,1)     | ✓ axiom-clean (153)  | ✓ axiom-clean (154)  |
  | (s,r)=(1,2)     | ✓ axiom-clean (156)  | **MISSING**          |
* Cycle 156 went +307 LOC (above its strategy ceiling). Cycle 157 is
  one more closure on a **mechanical port** of cycle 154 to the r=2
  setting; budget +210–260 LOC.
* No pending Aristotle results.
* No new blocker issues. `def_530B_scaffold_strategy.md` still records
  Path A is the only branch in scope; Path B (implicit) remains
  out-of-scope.

## Deliverable for cycle 157

Add **two** axiom-clean theorems to `OpenMath/Chapter5/Section530.lean`:

1. `padded2DEulerGLM_hasOrderOne_padCompatStarting` — the
   `HasOrderRelativeTo_explicit` statement at `(s, r) = (1, 2)`,
   `p = 1`, for `padded2DEulerGLM × padCompatStartingMethod` under
   the cycle-154 hypothesis pack
   (`LipschitzWith L f`, `ContDiff ℝ 2 yex`,
   `∀ x, HasDerivAt yex (f (yex x)) x`, `yex x₀ = y₀`).
2. `padded2DEulerGLM_hasOrderOne` — the existential closure for
   def:530C, exhibiting `padCompatStartingMethod` as the witness.
   One-line `refine ⟨..., ?_⟩` followed by `exact` of (1).

This saturates the four-corner Path A non-vacuity grid
(r=1/r=2 × p=0/p=1) and sets up the planner to pivot to
`thm:532A` or another textbook entity in cycle 158+ with a
clean baseline.

## Approach — verbatim port of cycle 154 + cycle 156 i=1 channel

### Step 1 — Add the witness theorem

Place it immediately after the existing
`padded2DEulerGLM_hasOrderZero_padCompatStarting` (currently ends
at `Section530.lean:1335`). Insert before
`padded2DEulerGLM_hasOrderZero` (line 1345).

Signature (copy cycle 154's `explicitEulerGLM_hasOrderOne_trivialStarting`,
swap `explicitEulerGLM` → `padded2DEulerGLM` and `trivialStartingMethod`
→ `padCompatStartingMethod`, and the `_isExplicit` witnesses
accordingly):

```lean
theorem padded2DEulerGLM_hasOrderOne_padCompatStarting
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C2 : ContDiff ℝ 2 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    HasOrderRelativeTo_explicit padded2DEulerGLM padCompatStartingMethod
      padCompatStartingMethod_constituents_isExplicit
      padded2DEulerGLM_isExplicit
      1 f yex x₀ y₀ := by
  intro i
  fin_cases i
  · -- i = 0 case: identical algebraic shape to cycle 154's p=1 closure.
    -- (paste cycle 154 lines 918–1086 verbatim, with three name swaps)
    sorry  -- placeholder; see Step 1a
  · -- i = 1 case: SM[1] = ES[1] = 0; identical to cycle 156's i=1 channel.
    sorry  -- placeholder; see Step 1b
```

### Step 1a — i=0 channel (mechanical port of cycle 154)

Source: `Section530.lean:918–1086` — the body of
`explicitEulerGLM_hasOrderOne_trivialStarting`. **Copy verbatim**
with exactly these textual replacements:

* `explicitEulerGLM` → `padded2DEulerGLM`
* `trivialStartingMethod` → `padCompatStartingMethod`
* The `_isExplicit` proof argument
  `(fun i => by fin_cases i; exact trivialGeneralizedRK_isExplicit)`
  → `padCompatStartingMethod_constituents_isExplicit`
* `explicitEulerGLM_isExplicit` → `padded2DEulerGLM_isExplicit`
* The hES sub-proof should mirror cycle 156's i=0 hES at
  `Section530.lean:1202–1211` (i.e. invoke
  `padCompatStartingMethod_applyExplicit` and finish with `rfl`),
  *not* cycle 154's hES which uses
  `trivialStartingMethod_applyExactThenStarting_explicit` — there is
  no padCompat-side analog of that lemma, but the closed form is the
  same and the manual `show … = …` + `rw` + `rfl` pattern from
  cycle 156 works.

For the SM[0] closed-form sub-proof (cycle 154 lines 927–942), the
inner `simp [explicitEulerGLM, ...]` becomes
`simp [padded2DEulerGLM, ...]`. Mirror **cycle 156's i=0 hSM**
(Section530.lean:1185–1200) for the exact `show` shape that switches
on the GLM index `0 : Fin 2`. Concrete shape:

```lean
have hSM : ∀ h : ℝ,
    applyStartingThenStep_explicit padded2DEulerGLM padCompatStartingMethod
        padCompatStartingMethod_constituents_isExplicit
        padded2DEulerGLM_isExplicit f y₀ h 0
      = (y₀ + h * f y₀) + h * f (y₀ + h * f y₀) := by
  intro h
  show (h * ∑ i : Fin 1,
      padded2DEulerGLM.B 0 i
        * f (padded2DEulerGLM.explicitStageValue f
                (padCompatStartingMethod.applyExplicit f y₀ h) h i))
      + (padded2DEulerGLM.V *ᵥ padCompatStartingMethod.applyExplicit f y₀ h) 0
      = _
  rw [padCompatStartingMethod_applyExplicit]
  unfold OpenMath.Chapter5.Section510.GeneralLinearMethod.explicitStageValue
  simp [padded2DEulerGLM, Matrix.mulVec, dotProduct]
  ring
```

The hcongr, hpow, hT1 (Taylor + iteratedDeriv), hT2 (Lipschitz +
|h|≤1), and the final `exact hT1.add hT2` blocks all transfer
**verbatim** from cycle 154 — these sub-proofs depend only on the
closed forms `(y₀ + h·f y₀) + h·f(y₀ + h·f y₀)` and
`yex(x₀+h) + h·f(yex(x₀+h))`, both of which match exactly between
cycle 154's setup and the new r=2 setup.

### Step 1b — i=1 channel (mechanical port of cycle 156's zero channel)

Source: `Section530.lean:1296–1335` — the i=1 channel of
`padded2DEulerGLM_hasOrderZero_padCompatStarting`. **Copy verbatim**
with one replacement:

* The `change` clause's exponent `h ^ (0 + 1)` → `h ^ (1 + 1)`.
* No other change. The hSM1 / hES1 / hcongr / `Asymptotics.isBigO_zero`
  closure works for any non-negative exponent, since the LHS is
  identically zero.

### Step 2 — Add the existential wrapper for def:530C

Place it immediately after `padded2DEulerGLM_hasOrderZero` (currently
ends at `Section530.lean:1357`). Mirror that theorem's shape:

```lean
/-- **Non-vacuity of `HasOrder_explicit` at `r = 2`, `p = 1` (cycle 157).**
Refines `padded2DEulerGLM_hasOrderZero` to `p = 1` under the cycle-154
hypothesis pack (`LipschitzWith L f`, `ContDiff ℝ 2 yex`, full ODE
relation, `yex x₀ = y₀`). The starting method is
`padCompatStartingMethod`; the `HasOrderRelativeTo_explicit` component
is supplied by `padded2DEulerGLM_hasOrderOne_padCompatStarting`. -/
theorem padded2DEulerGLM_hasOrderOne
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_C2 : ContDiff ℝ 2 yex)
    (hyex_ode : ∀ x, HasDerivAt yex (f (yex x)) x) :
    HasOrder_explicit padded2DEulerGLM padded2DEulerGLM_isExplicit
      1 f yex x₀ y₀ := by
  refine ⟨padCompatStartingMethod,
          padCompatStartingMethod_constituents_isExplicit,
          padCompatStartingMethod_isNonDegenerate,
          ?_⟩
  exact padded2DEulerGLM_hasOrderOne_padCompatStarting
          hf_lip hyex_x₀ hyex_C2 hyex_ode
```

### Step 3 — Verify

Run, in order:

1. `lake env lean OpenMath/Chapter5/Section530.lean` — must exit 0.
2. `grep -c sorry OpenMath/Chapter5/Section530.lean` — must print 0.
3. `lean_verify
   OpenMath.Chapter5.Section530.padded2DEulerGLM_hasOrderOne_padCompatStarting`
   — must return `[propext, Classical.choice, Quot.sound]`.
4. `lean_verify
   OpenMath.Chapter5.Section530.padded2DEulerGLM_hasOrderOne`
   — same.
5. `lean_verify
   OpenMath.Chapter5.Section530.padded2DEulerGLM_hasOrderZero_padCompatStarting`
   — must remain `[propext, Classical.choice, Quot.sound]` (cycle 156
   regression check).
6. `lake env lean OpenMath/Chapter5.lean` — exit 0 (no downstream
   regressions).
7. Updates to `extraction/formalization_data/lean_status.json`:
   bump `def:530B` and `def:530C` rows' `cycle` field to 157;
   leave `lean_status` as `partial` (Path B implicit branch still
   deferred).
8. Update `plan.md`'s `[~] def:530B` and `[~] def:530C` annotations
   to mention the cycle-157 r=2 × p=1 witness.

### Step 4 — Write `task_results/cycle_157.md`

Include:

* Worked on: `def:530B` Path A r=2 × p=1 witness +
  `def:530C` Path A r=2 × p=1 existential closure.
* Approach: verbatim port of cycle 154 to cycle 156's r=2 setting
  per this strategy.
* Result: SUCCESS / axiom-clean.
* Faithfulness check entries for the two new theorems.
* LOC delta (expected ~210–260 LOC).
* Suggested next: pivot to `thm:532A` (Algebraic analysis of order)
  or to the i=0 T1/T2 closure parameterization refactor across
  cycles 153/154/156/157 (would recover ~140 LOC).

## What NOT to try

* **Do NOT attempt `thm:532A` in cycle 157.** It needs
  multi-cycle infrastructure (rooted-tree elementary differentials
  from §31x or a polynomial test-function reformulation). A
  sorry-first scaffold would regress sorry count 0 → N and would
  be rolled back per the cycle-138/139 / cycle-149/150 precedent.
* **Do NOT refactor cycle 153/154/156's i=0 T1/T2 closures into a
  shared helper this cycle.** That refactor is appealing
  (~140 LOC reduction) but is orthogonal to delivering the
  witness; combining the two risks both. Defer to a dedicated
  refactoring cycle (158+).
* **Do NOT modify `HasOrderRelativeTo_explicit` or `HasOrder_explicit`
  predicates.** They are stable from cycles 153/155.
* **Do NOT extend Path A to implicit methods.** Path B remains
  out-of-scope per `def_530B_scaffold_strategy.md`.
* **Do NOT raise `maxHeartbeats`.** Cycle 154's proof closed under
  default heartbeats; cycle 157 is structurally identical, so the
  port should also fit.
* **Do NOT add `import OpenMath.Chapter5.Section520`** — it is
  already in the imports as of cycle 156.
* **Do NOT introduce new helper definitions.** `padCompatMethod`,
  `padCompatStartingMethod`, `padded2DEulerGLM`, etc. all exist from
  cycles 133/156. Reuse only.
* **Do NOT submit Aristotle jobs this cycle.** The proof is
  mechanical; manual closure beats Aristotle on this kind of
  port (cf. cycle 154 closing while Aristotle was IN_PROGRESS).
* **Do NOT touch `scripts/autonomous_loop.py`** — see standing
  `tautology_scanner_false_positives.md`.
* **Avoid the `h_<name>` / `:= h_*` / `exact h_*` idiom** in any
  new sub-proofs. The supervisor's tautology scanner false-positives
  on those (issues D1+D2 in
  `tautology_scanner_false_positives.md`). Use `hname` (no
  underscore) consistently — cycle 154's proof already does this.
  If a `h_inner`-style identifier slips in via a copy-paste from a
  Mathlib idiom, rename it before committing.

## LOC budget and ceiling

* **Target**: +210–260 LOC. The i=0 closure ports cycle 154 at ~180
  LOC; the i=1 closure adds ~40 LOC; the def:530C wrapper adds ~17
  LOC; docstrings ~25 LOC. Cycle 156's overrun was driven by the
  novel r=2 algebra; cycle 157 is a pure name-swap port, so it
  should land closer to the bottom of the range.
* **Hard ceiling**: 320 LOC. If you exceed this without closing the
  proof, abort the cycle and revert. Do not push partial work.
* If the i=0 channel takes longer than 60 minutes of debugging,
  re-read the cycle 156 i=0 closure (`Section530.lean:1175–1295`)
  to confirm you have the right `show` / `unfold` / `simp` shape;
  the difference between p=0 and p=1 is purely in the T1/T2 bounds
  (Taylor degree-2 vs first-order derivative), not in the closed-form
  algebra of `hSM` / `hES`.

## Why this delivers value

* Saturates the Path A four-corner non-vacuity grid (r∈{1,2}, p∈{0,1}).
  Future cycles know `HasOrderRelativeTo_explicit` and
  `HasOrder_explicit` are well-defined non-vacuous predicates at
  multiple sizes, both small (`p = 0`) and standard (`p = 1`,
  matching Butcher's textbook order classification of explicit Euler
  as order 1).
* Confirms the cycle-154 Taylor-based closure pattern generalizes
  cleanly to multi-channel GLMs, which is reassuring for any future
  thm:532A work that proves order properties for Runge–Kutta-type
  GLMs at higher orders.
* Mechanical execution; minimal risk of regression. Maintains the
  cycle 156 axiom-clean, sorry-zero baseline.
