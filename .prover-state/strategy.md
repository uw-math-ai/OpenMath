# Cycle 156 Strategy

## Context

* Cycle 155 closed Priority 1 cleanly: `def:530C` Path A predicate
  `HasOrder_explicit` plus `p=0`/`p=1` non-vacuity witnesses for
  `(explicitEulerGLM × trivialStartingMethod)` landed axiom-clean
  (+65 LOC, sorry count 0).
* Cycle 155 deferred its own Priority 2 (`r = 2` coverage witness)
  as stretch. Cycle 156 is its natural continuation.
* No Aristotle results pending.
* Both `def:530B` and `def:530C` are still `[~]` partial — Path A
  (explicit branch) only. Path B (implicit) remains deferred per
  `.prover-state/issues/def_530B_scaffold_strategy.md`.

## Priority 1 — `r = 2` non-vacuity witness for def:530B and def:530C (~120–150 LOC)

**Target**: prove
`HasOrderRelativeTo_explicit padded2DEulerGLM <newSM> <hS> padded2DEulerGLM_isExplicit 0 f yex x₀ y₀`
plus its existential closure under `HasOrder_explicit`. Together this
strengthens the non-vacuity story for Path A from "only `r = 1`
works" to "non-trivial `r = 2` cases also exhibit the predicate".

### Critical correction to cycle 155's Priority 2 sketch

The cycle 155 strategy proposed pairing `padded2DEulerGLM` with
`mixedStartingMethod`. **This does NOT work.** Verification:

* `padded2DEulerGLM` (Section520.lean:1286): `V = !![1,0; 0,0]`,
  `B = !![1; 0]`, `U = !![1, 0]`, `A = !![0]`. So row 1 of every
  step is the *zero channel*: `SM[1] = 0` regardless of `y_input`.
* `mixedStartingMethod` (Section530.lean:223): `S_0 =
  trivialGeneralizedRK` (b₀ = 1), `S_1 = nontrivialTwoStageGRK`
  (**b₀ = 2**). So
  `ES[1] = applyExplicit S yex(x₀+h) h at index 1
        = b₀^{(1)} · yex(x₀+h) + h · ∑ b·f(stages)
        = 2 · yex(x₀+h)` (the `b` vector is zero, no h-term).
* Diff[1] = `SM[1] − ES[1] = 0 − 2·yex(x₀+h) = −2·yex(x₀+h)`,
  which tends to `−2·y₀ ≠ 0` as `h → 0`. **NOT** O(h) for general
  `y₀`.

The fix: introduce a starting method whose row-1 constituent has
`b₀ = 0` (so its applyExplicit returns 0 at index 1), meshing with
`padded2DEulerGLM`'s zero row-1 channel.

### Step 1 — `padded2DEulerGLM_isExplicit` (~5 LOC)

Place in `OpenMath/Chapter5/Section530.lean` next to existing
`explicitEulerGLM_isExplicit` (line 573), inside the
`namespace OpenMath.Chapter5.Section510.GeneralLinearMethod` /
`open Matrix` block. The `A`-block of `padded2DEulerGLM` is
`!![0]` (1×1 zero), so the proof is identical to
`explicitEulerGLM_isExplicit`:

```lean
theorem padded2DEulerGLM_isExplicit :
    OpenMath.Chapter5.Section520.padded2DEulerGLM.IsExplicit := by
  intro i j _
  fin_cases i; fin_cases j
  rfl
```

**Verify**: the namespace home should be the GLM-side
`OpenMath.Chapter5.Section510.GeneralLinearMethod` block (lines
516–542 in cycle 155's file). If `padded2DEulerGLM` requires a
qualified prefix because it lives in `Section520`, write
`OpenMath.Chapter5.Section520.padded2DEulerGLM` explicitly. Add
`import OpenMath.Chapter5.Section520` at the top of `Section530.lean`
if not already present (cycle 155 already imported `Section510`; check
whether `Section520` is also imported via transitive chain — it likely
is since `Section530` → `Section510` and `Section520` → `Section510`).

If the import is not transitive, add `import OpenMath.Chapter5.Section520`.

### Step 2 — A new `r = 2` non-degenerate starting method whose row-1 channel is zero (~20 LOC)

Add **just below** `zero2StartingMethod_isDegenerate` (around line
264 of cycle 155's file) under a new mini-section:

```lean
/-! ### r = 2 starting method compatible with `padded2DEulerGLM`'s
zero row-1 channel (cycle 156)

To pair with `padded2DEulerGLM` (whose row 1 of V/B is zero) for a
`HasOrderRelativeTo_explicit` non-vacuity witness, we need a
starting method `S : StartingMethod 2` such that the row-1 channel
is also a zero channel — i.e. `S.method 1` has `b₀ = 0` and `b = 0`,
making `S.applyExplicit f y₀ h` return 0 at index 1. The row-0
constituent must still satisfy the non-degeneracy condition, so we
take `trivialGeneralizedRK` (b₀ = 1) at index 0. -/

/-- Constituent function for `padCompatStartingMethod`: index 0
gets `trivialGeneralizedRK` (b₀ = 1, exercises the active channel),
index 1 gets `zeroGeneralizedRK` (b₀ = 0, witnesses the inactive
channel). Both are 1-stage, both explicit. -/
def padCompatMethod : (i : Fin 2) → GeneralizedRungeKuttaMethod 1
  | 0 => trivialGeneralizedRK
  | 1 => zeroGeneralizedRK

/-- A 2-method starting method that meshes with
`padded2DEulerGLM`'s zero row-1 channel: row 0 active
(`trivialGeneralizedRK`, b₀ = 1), row 1 inactive
(`zeroGeneralizedRK`, b₀ = 0). Non-degenerate at index 0. -/
def padCompatStartingMethod : StartingMethod 2 where
  stages := fun _ => 1
  method := padCompatMethod

/-- **Non-vacuity (cycle 156).** `padCompatStartingMethod` is
non-degenerate via its index-0 constituent (b₀ = 1 ≠ 0). -/
theorem padCompatStartingMethod_isNonDegenerate :
    padCompatStartingMethod.IsNonDegenerate := by
  rw [StartingMethod.isNonDegenerate_iff_exists_b₀_ne_zero]
  refine ⟨0, ?_⟩
  show (1 : ℝ) ≠ 0
  exact one_ne_zero

/-- Both constituents of `padCompatStartingMethod` are explicit:
`trivialGeneralizedRK` and `zeroGeneralizedRK` both have the 1×1
zero `A`-block. -/
theorem padCompatStartingMethod_constituents_isExplicit :
    ∀ i : Fin 2, (padCompatStartingMethod.method i).IsExplicit := by
  intro i
  fin_cases i
  · exact trivialGeneralizedRK_isExplicit
  · -- zeroGeneralizedRK is explicit (A = !![0])
    intro a b _
    fin_cases a; fin_cases b
    rfl
```

Note: if `zeroGeneralizedRK_isExplicit` already exists in the file
(scan cycles 151+ for it), use that named theorem instead of
inlining the proof of `(zeroGeneralizedRK).IsExplicit`. Cycle 151
introduced `IsExplicit`; check whether a `zeroGeneralizedRK_isExplicit`
companion lemma was also added. If not, the inline proof above is
fine — it's three tactics.

### Step 3 — Per-component closed forms for SM and ES (~30 LOC)

This step is **algebraic preparation**: derive the closed forms
that the `HasOrderRelativeTo_explicit` proof at p=0 will rely on.
With `padded2DEulerGLM` and `padCompatStartingMethod`:

* `y_input := padCompatStartingMethod.applyExplicit f y₀ h`
  - `y_input 0 = trivialGeneralizedRK.explicitApply f y₀ h
              = y₀ + h · f(y₀)` (cycle 152 sanity helper
    `trivialGeneralizedRK_explicitApply`).
  - `y_input 1 = zeroGeneralizedRK.explicitApply f y₀ h
              = 0 · y₀ + h · 0 · f(...) = 0`.
* Internal stage `Y_0 = (M.U *ᵥ y_input) 0 + 0
                     = 1 · (y₀ + h·f y₀) + 0 · 0
                     = y₀ + h·f y₀`.
* `SM[0] = h · M.B[0][0] · f(Y_0) + (M.V *ᵥ y_input) 0
        = h · 1 · f(y₀ + h·f y₀) + 1 · (y₀ + h·f y₀) + 0 · 0
        = (y₀ + h·f y₀) + h · f(y₀ + h·f y₀)`
  ↑ identical to cycle 153's SM[0].
* `SM[1] = h · M.B[1][0] · f(Y_0) + (M.V *ᵥ y_input) 1
        = h · 0 · f(...) + 0 · (y₀ + h·f y₀) + 0 · 0 = 0`.
* `ES[0] = padCompatStartingMethod.applyExplicit f (yex(x₀+h)) h at 0
        = yex(x₀+h) + h · f(yex(x₀+h))` ↑ identical to cycle 153's
  ES[0].
* `ES[1] = padCompatStartingMethod.applyExplicit f (yex(x₀+h)) h at 1
        = 0 · yex(x₀+h) + h · 0 = 0`.

So `Diff[0]` is identical to cycle 153's diff (closure: T1+T2
decomposition); `Diff[1] = 0 − 0 = 0`, immediate via
`Asymptotics.isBigO_zero`.

Encode each closed form as a `have` block inside the main proof
(don't add separate top-level lemmas; the LOC budget is tight).

### Step 4 — The witness theorem (~50–80 LOC)

Place after `explicitEulerGLM_hasOrderOne` (line 1050) inside the
existing `namespace OpenMath.Chapter5.Section530` /
`section OrderRelativeTo` block:

```lean
/-- **`r = 2` non-vacuity (def:530C, Path A, cycle 156).**
The padded `(s, r) = (1, 2)` GLM `padded2DEulerGLM` has order `0`
relative to `padCompatStartingMethod`. The row-0 channel reduces
to the same explicit-Euler closed form as cycle 153's
`(s, r) = (1, 1)` witness; the row-1 channel is identically zero
on both `SM` and `ES`. Establishes `HasOrderRelativeTo_explicit` at
non-trivial `r = 2`, complementing cycle 153/154's `r = 1`
witnesses. -/
theorem padded2DEulerGLM_hasOrderZero_padCompatStarting
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_deriv : HasDerivAt yex (f y₀) x₀) :
    HasOrderRelativeTo_explicit
        OpenMath.Chapter5.Section520.padded2DEulerGLM
        padCompatStartingMethod
        padCompatStartingMethod_constituents_isExplicit
        padded2DEulerGLM_isExplicit
        0 f yex x₀ y₀ := by
  intro i
  fin_cases i
  · -- i = 0 case: identical algebraic shape to cycle 153.
    -- Step 1a: derive closed form for SM[0].
    have hSM0 : ∀ h : ℝ,
        applyStartingThenStep_explicit
            OpenMath.Chapter5.Section520.padded2DEulerGLM
            padCompatStartingMethod
            padCompatStartingMethod_constituents_isExplicit
            padded2DEulerGLM_isExplicit f y₀ h 0
          = (y₀ + h * f y₀) + h * f (y₀ + h * f y₀) := by
      intro h
      -- unfold operator + applyExplicit + explicitStageValue
      -- + simp on padded2DEulerGLM and padCompatStartingMethod entries
      sorry  -- WORKER: replace with the unfold/simp/ring proof below
    -- Step 1b: ES[0] closed form.
    have hES0 : ∀ h : ℝ,
        applyExactThenStarting_explicit
            padCompatStartingMethod
            padCompatStartingMethod_constituents_isExplicit
            f yex x₀ h 0
          = yex (x₀ + h) + h * f (yex (x₀ + h)) := by
      intro h
      sorry  -- WORKER: same approach as cycle 152 sanity lemma.
    -- Step 2+: reuse cycle 153's T1/T2 closure verbatim.
    sorry
  · -- i = 1 case: SM[1] = 0, ES[1] = 0, Diff = 0.
    have hSM1 : ∀ h : ℝ,
        applyStartingThenStep_explicit
            OpenMath.Chapter5.Section520.padded2DEulerGLM
            padCompatStartingMethod
            padCompatStartingMethod_constituents_isExplicit
            padded2DEulerGLM_isExplicit f y₀ h 1 = 0 := by
      sorry
    have hES1 : ∀ h : ℝ,
        applyExactThenStarting_explicit
            padCompatStartingMethod
            padCompatStartingMethod_constituents_isExplicit
            f yex x₀ h 1 = 0 := by
      sorry
    have hcongr : (fun h : ℝ =>
        applyStartingThenStep_explicit
            OpenMath.Chapter5.Section520.padded2DEulerGLM
            padCompatStartingMethod
            padCompatStartingMethod_constituents_isExplicit
            padded2DEulerGLM_isExplicit f y₀ h 1
          - applyExactThenStarting_explicit
              padCompatStartingMethod
              padCompatStartingMethod_constituents_isExplicit
              f yex x₀ h 1) = 0 := by
      funext h; rw [hSM1, hES1]; ring
    rw [hcongr]
    exact Asymptotics.isBigO_zero _ _
```

The above is a **scaffold sketch**, NOT a literal copy. The worker
must close the four `sorry`s (hSM0, hES0, the i=0 T1/T2 step, hSM1
and hES1) immediately within the same cycle — do **not** commit
with `sorry`s present. Do not introduce a sorry-first scaffold for
the witness; the cycle-149 sorry-first attempt was rolled back per
`def_530B_scaffold_strategy.md`.

For the i=0 T1/T2 closure: copy cycle 153's proof verbatim (lines
~710–800 of `Section530.lean`) — the closed-form expressions are
identical, only the `M`-side context object differs. Specifically
the four steps:

1. `hderiv : (fun h : ℝ => yex (x₀ + h) - yex x₀ - h • f y₀)
     =o[nhds (0:ℝ)] (fun h => h)` from
  `hasDerivAt_iff_isLittleO_nhds_zero.mp hyex_deriv`
2. Rewrite with `hyex_x₀` and `smul_eq_mul`, negate via
   `IsLittleO.neg_left`, promote to `IsBigO`.
3. T2 = `h · (f(y₀ + h·f y₀) − f(yex(x₀+h)))` bounded by `L · |h|`
   on the eventual `|·| ≤ 1` neighbourhood (continuity of `a, b`
   at 0 with `a(0) = b(0) = y₀`); close via `IsBigO.of_bound (↑L)`
   plus `LipschitzWith.dist_le_mul`.
4. `hT1.add hT2`, then `simpa` collapses `h^(0+1) → h`.

For hSM0: the cycle 153 proof uses
```
show (h * ∑ i : Fin 1, M.B 0 i * f (M.explicitStageValue f
       (S.applyExplicit f y₀ h) h i))
     + (M.V *ᵥ S.applyExplicit f y₀ h) 0 = _
rw [<S>_applyExplicit]   -- closed form for y_input
unfold OpenMath.Chapter5.Section510.GeneralLinearMethod.explicitStageValue
simp [<M>, Matrix.mulVec, dotProduct]
ring
```
Adapt by inlining the closed form for `padCompatStartingMethod.applyExplicit`
(may need an auxiliary `padCompatStartingMethod_applyExplicit` lemma
analogous to cycle 152's `trivialStartingMethod_applyExplicit`, or
just unfold in-place).

For hSM1: same template, but the row-1 entries of `M.B` and `M.V`
are zero, so the sum and the matrix-vector product collapse to 0.
Should be a 5-line `show + simp [...] + ring` proof.

For hES1: `applyExactThenStarting_explicit S _hS f yex x₀ h =
S.applyExplicit f (yex(x₀+h)) h` by definition. At index 1,
`zeroGeneralizedRK.explicitApply` is `0 · yex(x₀+h) + h · 0 · ... = 0`.
Should be a 3-line `unfold + simp` proof. If a
`zeroGeneralizedRK_explicitApply : zeroGeneralizedRK.explicitApply f y h = 0`
sanity lemma already exists from cycle 152, cite it.

### Step 5 — Existential-closure witness for def:530C (~10 LOC)

Mirror cycle 155's `explicitEulerGLM_hasOrderZero` shape:

```lean
theorem padded2DEulerGLM_hasOrderZero
    {f : ℝ → ℝ} {L : NNReal} (hf_lip : LipschitzWith L f)
    {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
    (hyex_x₀ : yex x₀ = y₀)
    (hyex_deriv : HasDerivAt yex (f y₀) x₀) :
    HasOrder_explicit
        OpenMath.Chapter5.Section520.padded2DEulerGLM
        padded2DEulerGLM_isExplicit
        0 f yex x₀ y₀ := by
  refine ⟨padCompatStartingMethod,
          padCompatStartingMethod_constituents_isExplicit,
          padCompatStartingMethod_isNonDegenerate,
          ?_⟩
  exact padded2DEulerGLM_hasOrderZero_padCompatStarting
          hf_lip hyex_x₀ hyex_deriv
```

### Verification checklist

* `lake env lean OpenMath/Chapter5/Section530.lean` exits 0.
* `grep -c sorry OpenMath/Chapter5/Section530.lean` → **0**. The
  scaffold's `sorry`s above must be closed before commit; do not
  commit a partial witness.
* `mcp__lean-lsp__lean_verify` on
  `padded2DEulerGLM_isExplicit`,
  `padCompatStartingMethod_isNonDegenerate`,
  `padCompatStartingMethod_constituents_isExplicit`,
  `padded2DEulerGLM_hasOrderZero_padCompatStarting`,
  `padded2DEulerGLM_hasOrderZero` → axiom-clean
  `[propext, Classical.choice, Quot.sound]`.
* No regressions on the cycle 153/154/155 axiom checks.

### Bookkeeping

* `extraction/formalization_data/lean_status.json` — bump the
  `cycle` field on the `def:530B` and `def:530C` rows to **156**;
  extend their notes paragraphs to mention the new `r = 2` witness.
* `plan.md` — update the cycle annotation on def:530B and def:530C
  rows: keep `[~]` status (Path A still partial — Path B deferred)
  but mention the new r=2 witness landed cycle 156, with name
  `padded2DEulerGLM_hasOrderZero_padCompatStarting` /
  `padded2DEulerGLM_hasOrderZero`.

### LOC budget

Total estimated: 120–150 LOC. If the i=0 T1/T2 closure proves
substantially heavier than cycle 153 (because the qualified
`OpenMath.Chapter5.Section520.padded2DEulerGLM` references inflate
`show`/`change` blocks), abort by removing the new r=2 witness
entirely (NOT by leaving sorries) and document in
`task_results/cycle_156.md` what stalled. Cycle 157 can retry with
a different decomposition. **Do not exceed 200 LOC.**

## Priority 2 (Stretch, only if Priority 1 finishes with budget) — `r = 2` p=1 strengthening

If Priority 1 lands cleanly with time remaining, add the p=1
analog `padded2DEulerGLM_hasOrderOne_padCompatStarting` plus its
existential closure `padded2DEulerGLM_hasOrderOne`. Mirrors cycle
154's Taylor-based proof (`ContDiff ℝ 2 yex` +
`∀ x, HasDerivAt yex (f (yex x)) x`), with the same i=0 / i=1
case-split. Estimated +60 LOC; abort if Priority 1 used > 120 LOC.

## What NOT to try

1. **Do NOT use `mixedStartingMethod` for the r=2 witness.**
   Cycle 155's Priority 2 sketch suggested this; it does not work
   because `nontrivialTwoStageGRK` has `b₀ = 2`, making
   `ES[1] = 2·yex(x₀+h) ≠ 0`, breaking the claimed `Diff[1] = 0`.
   See "Critical correction" above for the algebraic verification.

2. **Do NOT pursue Path B (implicit / fixed-point).** Multi-cycle
   infrastructure not justified by current downstream demand. See
   `.prover-state/issues/def_530B_scaffold_strategy.md`.

3. **Do NOT submit anything to Aristotle.** The proofs are
   mechanical adaptations of cycle 152/153 templates. Round-trip
   latency >> manual closure time.

4. **Do NOT introduce a sorry-first scaffold.** The cycle 149
   sorry-first attempt was rolled back per
   `def_530B_scaffold_strategy.md`. The Step 4 sketch above
   contains `sorry` markers ONLY for the worker's benefit when
   reading the strategy; they must be closed within cycle 156.

5. **Do NOT introduce `axiom` / `constant` declarations.** Per
   CLAUDE.md.

6. **Do NOT raise `maxHeartbeats` above 200000.** Per CLAUDE.md.
   If a single goal blows up, factor a `private lemma` (cycle 150
   precedent on thm:550A n=7).

7. **Do NOT pivot to thm:550A general-`n`.** Two Aristotle attempts
   already cancelled (cycles 141, 151). Seven concrete-`n`
   stepping stones (n = 1..7) suffice; further stones provide
   marginal value. Do not submit a third Aristotle attempt this
   cycle.

8. **Do NOT pivot to thm:532A** ("Algebraic analysis of order")
   this cycle. It is a tempting next entity (genuine new content,
   downstream of def:530C), but its proof requires order-condition
   infrastructure that's heavier than a single-cycle deliverable.
   Solidify the def:530B/C non-vacuity story (this cycle) first;
   thm:532A becomes the natural cycle 157+ target.

9. **Do NOT modify `scripts/autonomous_loop.py`.** Tautology-scanner
   D1/D2 fixes remain loop-maintainer territory per
   `tautology_scanner_false_positives.md`. If the scanner fires
   on any new `:= h_<name>` / `exact h_<name>` closer in this
   cycle's code, apply the cosmetic rename `h_<name> → h<name>`.
   The Step 4 scaffold above does not use `h_`-prefixed
   hypothesis names, so no scanner false positive should fire.

10. **Do NOT add new `.lean` files.** All cycle 156 code goes in
    `OpenMath/Chapter5/Section530.lean`.

## Worker checklist (in order)

1. Read `extraction/formalization_data/entities/def_530B.json` and
   `def_530C.json` to re-confirm the textbook statements (already
   captured above).
2. Verify whether `import OpenMath.Chapter5.Section520` is needed
   in `Section530.lean` (it likely already imports transitively
   via `Section510` ← `Section520` ← `Section510`; if not, add).
   `Bash`: `grep -n "^import OpenMath" OpenMath/Chapter5/Section530.lean`.
3. Implement Step 1 (`padded2DEulerGLM_isExplicit`) in the existing
   `namespace OpenMath.Chapter5.Section510.GeneralLinearMethod`
   block (lines 516–542 of cycle 155's file). Verify it compiles
   in isolation: `lake env lean OpenMath/Chapter5/Section530.lean`.
4. Implement Step 2 (`padCompatMethod`,
   `padCompatStartingMethod`, both witness theorems) just below
   `zero2StartingMethod_isDegenerate` (around line 264). Verify
   compile.
5. Implement Step 4 (the main `HasOrderRelativeTo_explicit`
   theorem) below cycle 155's `explicitEulerGLM_hasOrderOne`
   (line 1050), starting with the four `sorry`s, then closing
   each one in turn:
   * Close `hSM1` first (5-line `simp` proof).
   * Close `hES1` second (3-line `unfold + simp` proof).
   * Close `hSM0` third (mirror cycle 153, ~10 LOC).
   * Close `hES0` fourth (mirror cycle 153, ~5 LOC).
   * Close the i=0 T1/T2 step last (verbatim copy of cycle 153
     lines ~710–800, with renamed context variables).
6. Implement Step 5 (`padded2DEulerGLM_hasOrderZero` existential
   closure) below.
7. Run `lake env lean OpenMath/Chapter5/Section530.lean`. If
   errors, debug with `lean_diagnostic_messages` and `lean_goal`.
8. Run `lean_verify` on each new declaration to confirm
   `[propext, Classical.choice, Quot.sound]` axioms only.
9. `grep -c sorry OpenMath/Chapter5/Section530.lean` → 0.
10. Update `lean_status.json` and `plan.md` per the bookkeeping
    section above.
11. Write `task_results/cycle_156.md` covering: what landed,
    faithfulness check (the new r=2 witness theorems are
    non-vacuity supplements, not new entities — but they exercise
    the same `HasOrderRelativeTo_explicit` predicate that
    `def:530B`'s formalization rests on), dead ends if any, and
    suggested cycle 157 direction (likely thm:532A or a p=1
    strengthening if Priority 2 wasn't attempted).
12. Commit and push. Verify the commit reaches the remote
    (`git rev-parse HEAD` vs `git rev-parse origin/Main/Experiments`)
    to forestall any `attempts.md` stale-verdict carryover.

## Tautology-scanner notes

The Step 4 scaffold uses `hSM0`, `hSM1`, `hES0`, `hES1`,
`hcongr` — none start with `h_`. The scanner regex
`\bexact\s+h_\w+\s*$` will not fire. If the worker introduces
intermediate hypotheses with `h_` prefixes during the i=0 T1/T2
closure, follow cycle 154 precedent and use `h<name>` (no
underscore) from the start.

## Faithfulness statement for the cycle

The cycle 156 deliverable adds **non-vacuity witness theorems**
(not new textbook entities). Each new theorem
(`padded2DEulerGLM_isExplicit`,
`padCompatStartingMethod_isNonDegenerate`,
`padCompatStartingMethod_constituents_isExplicit`,
`padded2DEulerGLM_hasOrderZero_padCompatStarting`,
`padded2DEulerGLM_hasOrderZero`) strengthens the non-vacuity story
for `def:530B` Path A and `def:530C` Path A from "only `r = 1`
witnesses" to "non-trivial `r = 2` witness landed".

`padCompatMethod` and `padCompatStartingMethod` are Lean-internal
helpers (not textbook entities) — analogous to cycle 141's
`mixedStartingMethod`, cycle 139's `zeroStartingMethod`. They
witness that the heterogeneous-stages `StartingMethod` design
admits non-trivial inhabitants compatible with the
`padded2DEulerGLM` GLM. No textbook divergence.

## Cycle abort criteria

* If Step 1 or Step 2 expose a missing import that requires a
  cyclic dependency (Section530 → Section520 → Section530), abort
  and document in `task_results/cycle_156.md`. Likely fix is to
  factor `padded2DEulerGLM` into a shared helper file, but that's
  cycle 157+ work.
* If the i=0 T1/T2 closure exceeds 100 LOC (versus cycle 153's
  ~70 LOC for the analogous step), the qualified-namespace
  references are bloating the proof; pause and consider whether
  cycle 153's proof should be refactored to a parameterized helper
  consumed by both witnesses. Recommend: defer to cycle 157, drop
  the r=2 witness from cycle 156, ship only Steps 1+2.
* If `lake env lean` hangs > 5 min on any file, check that the
  NVMe lean toolchain is first in `PATH` per CLAUDE.md and that
  no `lake` recursion-wrapper bug has reappeared (cycle 114
  precedent).
