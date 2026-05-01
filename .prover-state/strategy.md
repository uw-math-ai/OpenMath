# Cycle 060 Strategy — Expose explicit (a, b, c) functions for the §406D outer squeeze

## Status snapshot

* **Sole sorry**: `OpenMath/Chapter4/Section404.lean:3207` —
  `LinearMultistepMethod.stable_consistent_isConvergent` (the
  non-autonomous shape; closure deferred to cycle 064+ for the
  autonomous→non-autonomous lift).
* **Just landed (cycle 059)**: two generic outer-squeeze sub-lemmas
  `globalError_outer_squeeze_a_term` (line 2311) and
  `globalError_outer_squeeze_c_term` (line 2383). Both take generic
  `a, b, c : ℝ → ℝ` and produce `Tendsto … atTop (nhds 0)` for the
  two halves of the closed-form bound's RHS, *given* the
  corresponding `nhds 0`-Tendsto hypotheses.
* **The bridge that's missing**: the closed-form analytical core
  `globalError_closed_form_autonomous` (line 3154) returns an
  *existential* `∃ a b c : ℝ, …` (per fixed `h`). The cycle 059
  sub-squeezes need *functions* `a, b, c : ℝ → ℝ` whose limits as
  `h → 0` are visible. Without exposing the explicit formulas,
  cycle 062's outer-squeeze assembly cannot apply the cycle 059
  helpers.
* **Aristotle**: no pending results.
* **No phantom blockers**: if the prompt's "stuck on" framing
  surfaces stale `attempts.md` rows, ignore them. The single sorry
  at line 3207 is the sole real outstanding item; everything else
  in the cycle 058–059 chain is committed and compiles. Verify with
  `git rev-parse HEAD` / `git rev-parse origin/Main/Experiments`
  (should match `b0332b9` or descendant), and
  `lake env lean OpenMath/Chapter4/Section404.lean` (clean modulo
  the expected `sorry` warning at line 3207). The standing
  `tautology_scanner_false_positives.md` issue covers any
  scanner-false-positive hits at lines 1762/1950/2842.

## Cycle 060 deliverable: explicit-function refactor (preparing the outer squeeze)

**Goal**: Land an explicit-function closed-form lemma
`globalError_closed_form_autonomous_explicit` whose signature
exposes `a`, `b`, `c` as `noncomputable def`s with explicit formulas
in `(M, Θ, h, yex, Y, x₀)`. After cycle 060 lands, cycle 061 can
prove the three limit lemmas (`a → 0`, `b → bInf > 0`, `c → cInf`),
and cycle 062 can do the outer-squeeze assembly proper using
cycle 059's helpers.

This is a refactor cycle. The bound itself is already proven
(cycle 053's `globalError_closed_form_autonomous`); we are just
peeling out the existential into named functions.

### Concrete steps

**Step 1 — Audit the existing formulas.** In
`globalError_recurrence_form` (line 2704), the proof body uses `set`
for these expressions (lines 2731–2761):

```lean
Cbase := L * (|β 0| * (Σᵢ |α i.succ|) + Σᵢ |β i.succ|)
           / (1 - h * L * |β 0|)
Dbase := ((1/2) * Σᵢ ((i+1):ℝ)^2 * |α i.succ|
           + Σᵢ ((i+1):ℝ) * |β i.succ|)
           * L * M_bound / (1 - h * L * |β 0|)
y'sum := Σᵢ ∈ range k, |yPrime k α (fun j ↦ yex(x₀ + j·h) - Y j) i|
a     := (Θ + (Θ + 1) * Cbase * h * k + 1) * y'sum
b     := (Θ + 1) * Cbase + 1
c     := (Θ + 1) * Dbase
```

These are the formulas to expose. Quote them verbatim before
introducing the `*Of` definitions to avoid drift.

**Step 2 — Promote to top-level `noncomputable def`s.** Add six
new private definitions just above
`LinearMultistepMethod.globalError_closed_form_autonomous`
(around line 3140). Use the suffix `Of` so callers read as
`aOf M Θ L h yex Y x₀`, matching cycle 056/057's
`_tendsto_at_zero` style:

```lean
private noncomputable def CbaseOf {k : ℕ} (M : LinearMultistepMethod k)
    (L h : ℝ) : ℝ :=
  L * (|M.β 0| * (∑ i : Fin k, |M.α i.succ|)
        + ∑ i : Fin k, |M.β i.succ|)
    / (1 - h * L * |M.β 0|)

private noncomputable def DbaseOf {k : ℕ} (M : LinearMultistepMethod k)
    (L M_bound h : ℝ) : ℝ :=
  ((1/2) * (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
    + ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|)
  * L * M_bound / (1 - h * L * |M.β 0|)

private noncomputable def yPrimeSumOf {k : ℕ}
    (M : LinearMultistepMethod k)
    (yex : ℝ → ℝ) (Y : ℕ → ℝ) (x₀ h : ℝ) : ℝ :=
  ∑ i ∈ Finset.range k,
    |yPrime k (fun j : Fin k => M.α j.succ)
       (fun j : Fin k => yex (x₀ + (j.val : ℝ) * h) - Y j.val) i|

private noncomputable def aOf {k : ℕ} (M : LinearMultistepMethod k)
    (Θ L h : ℝ) (yex : ℝ → ℝ) (Y : ℕ → ℝ) (x₀ : ℝ) : ℝ :=
  (Θ + (Θ + 1) * CbaseOf M L h * h * (k : ℝ) + 1)
    * yPrimeSumOf M yex Y x₀ h

private noncomputable def bOf {k : ℕ} (M : LinearMultistepMethod k)
    (Θ L h : ℝ) : ℝ :=
  (Θ + 1) * CbaseOf M L h + 1

private noncomputable def cOf {k : ℕ} (M : LinearMultistepMethod k)
    (Θ L M_bound h : ℝ) : ℝ :=
  (Θ + 1) * DbaseOf M L M_bound h
```

Order matters: `CbaseOf` and `DbaseOf` must come before `bOf` /
`cOf`, and `yPrimeSumOf` before `aOf`.

**Step 3 — State the explicit closed-form lemma.** Add a new
top-level theorem immediately after
`LinearMultistepMethod.globalError_closed_form_autonomous`
(line 3183 area), before the line-3203 `stable_consistent_isConvergent`
stub:

```lean
theorem LinearMultistepMethod.globalError_closed_form_autonomous_explicit
    {k : ℕ} (hk : 0 < k) (M : LinearMultistepMethod k)
    (hcons : M.IsConsistent) (hstab : M.IsStable)
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {yex : ℝ → ℝ}
    (hyex_C1 : ContDiff ℝ 1 yex)
    (hyex_ode : ∀ t, deriv yex t = f (yex t))
    (hf_yex_bound : ∀ t, |f (yex t)| ≤ M_bound)
    {Y : ℕ → ℝ} {x₀ h : ℝ}
    (hh : 0 ≤ h)
    (hsmall : h * L * |M.β 0| < 1)
    (hY : M.IsLMMSolution h x₀ (fun _ y => f y) Y) :
    ∃ Θ : ℝ, 0 ≤ Θ ∧
      0 ≤ aOf M Θ L h yex Y x₀ ∧
      0 < bOf M Θ L h ∧
      0 ≤ cOf M Θ L M_bound h ∧
      ∀ n : ℕ,
        |yex (x₀ + (n : ℝ) * h) - Y n|
          ≤ Real.exp (bOf M Θ L h * (k : ℝ) * (n : ℝ) * h)
              * aOf M Θ L h yex Y x₀
            + (Real.exp (bOf M Θ L h * (k : ℝ) * (n : ℝ) * h) - 1)
                * (cOf M Θ L M_bound h * h
                    / (bOf M Θ L h * (k : ℝ))) := by
  sorry
```

`Θ` is existential (depends on `M, k, hstab` via
`theta_bounded_of_isStable`); the four positivity / bound conjuncts
are quantified over the existential `Θ`.

**Step 4 — Prove it.** The minimum-work path: replay the proof
body of `globalError_recurrence_form` with the `set` lines
replaced by `change` / `show` so the `*Of` defs become the local
identifiers, then re-run the existential-form
`globalError_closed_form_autonomous` proof (the `discrete_gronwall_exp_bound`
application). Concrete plan:

1. `obtain ⟨Θ, hΘ_nn, hΘ⟩ := theta_bounded_of_isStable hk M hstab`.
2. `refine ⟨Θ, hΘ_nn, ?_, ?_, ?_, ?_⟩`.
3. **Goal `0 ≤ aOf M Θ L h yex Y x₀`** — `unfold aOf yPrimeSumOf
   CbaseOf`, then replay the
   `globalError_recurrence_form` body's positivity proof for `a`
   (lines 2766–2768). Helper facts you'll need:
   * `h_denom_pos : 0 < 1 - h * L * |M.β 0|` from `hsmall`.
   * `hCbase_nn`, `hΘp1_nn`, `hCbase_h_k_nn` (lines 2737, 2764–2765).
4. **Goal `0 < bOf M Θ L h`** — `unfold bOf CbaseOf`, replay
   lines 2769–2771.
5. **Goal `0 ≤ cOf M Θ L M_bound h`** — `unfold cOf DbaseOf`,
   replay lines 2744–2752 + 2772.
6. **Goal `∀ n, |yex … - Y n| ≤ exp(bOf …) * aOf … + …`** — this
   is the bound. `unfold aOf bOf cOf`, then *cite*
   `globalError_closed_form_autonomous` with the same hypotheses;
   destructure its existential and discharge with `linarith` /
   `congr` after observing that the algebraic shapes match.

If step 6's `congr`-after-cite path is finicky (the cited lemma's
existential `a, b, c` are local `set` names and may not
syntactically match `aOf M Θ L h yex Y x₀` etc.), the alternative
is a **full replay**: copy the body of `globalError_recurrence_form`
+ the `discrete_gronwall_exp_bound` postlude from
`globalError_closed_form_autonomous`, with each `set name := …` line
replaced by a `have name_eq : aOf … = … := by unfold aOf …; rfl`
followed by `rw [← name_eq]` on the goal at the end. Either path
works; try the cite first (it's ~15 lines), fall back to full
replay (~120 lines) only if the cite fails.

**Pragmatic shortcut**: if step 6's cite is unstable, expose the
existential's witnesses directly. Replace the body with:

```lean
  obtain ⟨Θ, hΘ_nn, hΘ⟩ := theta_bounded_of_isStable hk M hstab
  obtain ⟨a, b, c, ha, hb, hc, hbound, hu0⟩ :=
    globalError_recurrence_form hk M hcons hstab hL hM hf_lip
      hyex_C1 hyex_ode hf_yex_bound hh hsmall hY
  -- Show aOf … = a, bOf … = b, cOf … = c by unfolding both sides.
  -- This requires the existential's a, b, c to literally match the *Of
  -- formulas — which they do, by construction.
```

But this only works if `globalError_recurrence_form`'s `obtain`
exposes the *exact* `set` witnesses, which it does NOT (the `set`s
are local, not part of the conclusion). So the cleanest path is
the full replay.

**Recommended order**: try cite (step 4, option 1) first with a 30-min
budget. If that hits algebraic-shape mismatch, switch to replay.

**Step 5 — Compile and axiom-check.** Run
`lake env lean OpenMath/Chapter4/Section404.lean`. Expected: clean
build modulo the same warnings as cycle 059 (three pre-existing
unused-variable warnings + the line-3207 `sorry` warning, now
shifted by ~+200 lines). Verify axioms via
`mcp__lean-lsp__lean_verify` with
`OpenMath.Chapter4.Section404.LinearMultistepMethod.globalError_closed_form_autonomous_explicit`;
expect `[propext, Classical.choice, Quot.sound]`.

### Things to NOT do this cycle

* **Do NOT delete `globalError_closed_form_autonomous`.** Keep both
  the existential and the explicit form. The existential is
  potentially used by other downstream consumers; cycle 062 will
  decide whether to retire it.
* **Do NOT touch `globalError_recurrence_form`.** It is internal
  infrastructure; the explicit-function exposure is *only* needed
  at the closed-form level (since the outer squeeze is built off
  the closed-form, not the recurrence). Adding parallel definitions
  inside `globalError_recurrence_form` would be wasted work.
* **Do NOT prove the limit lemmas `aOf → 0`, `bOf → bInf`,
  `cOf → cInf` this cycle.** Those are cycle 061. Specifically,
  `aOf → 0` requires the starting-method convergence hypothesis
  (`Tendsto (start · i) (nhds 0) (nhds y₀)`) which is currently
  threaded only through `IsConvergent`'s `start` function and is
  *not* part of the closed-form's hypothesis list. The cycle 061
  job will be to lift those hypotheses appropriately. Cycle 056's
  existing `b_tendsto_at_zero`, `c_tendsto_at_zero`,
  `Cbase_tendsto_at_zero`, `Dbase_tendsto_at_zero` (lines 1982,
  2025, 2114, 2138) already prove the right limits for the
  deterministic factors of `bOf` and `cOf` — only `aOf → 0` (via
  `yPrimeSumOf → 0`) is the new piece in cycle 061.
* **Do NOT attempt the outer-squeeze assembly proper this cycle.**
  That is cycle 062. Cycle 060's deliverable is *only* the
  explicit-function variant of the closed-form.
* **Do NOT touch the `sorry` at line 3207.** It is gated on the
  autonomous→non-autonomous lift (cycle 064+), which is far
  downstream of cycle 060. Closing it in cycle 060 is **not**
  expected; cycle 059's task results document this multi-cycle
  decomposition and cycle 060 sits one step into it.
* **Do NOT generalise the closed-form to vector-valued `y`.** Stay
  scalar; cycle 053's autonomous restriction stands.
* **Do NOT raise `maxHeartbeats`.** If the proof is slow, decompose
  into helper lemmas (one each for `aOf_pos_of_*`, `bOf_pos_of_*`,
  `cOf_pos_of_*`) — but try the direct `refine` first.
* **Do NOT mistake the cycle 059 outer-squeeze sub-lemmas
  (`globalError_outer_squeeze_a_term`,
  `globalError_outer_squeeze_c_term`) for the missing pieces.**
  They are correct and final; cycle 062 will instantiate them.
  Cycle 060's job is to produce the explicit `a, b, c` *that
  cycle 062 will plug in*.
* **Do NOT introduce `axiom`/`constant`** to bypass any positivity
  obligation. Per CLAUDE.md.
* **Do NOT modify `scripts/autonomous_loop.py`.** Per CLAUDE.md and
  cycle 015's strategy. The `tautology_scanner_false_positives.md`
  issue stands.

### Aristotle plan

* **Skip Aristotle this cycle.** This is a mechanical refactor,
  not a search problem. Aristotle is most useful for finding
  Mathlib lemmas to close goals; here every required step is
  already in the existing proof body of
  `globalError_closed_form_autonomous` /
  `globalError_recurrence_form`. The four positivity goals are
  identical to lines 2766–2772; the bound goal is the
  `discrete_gronwall_exp_bound` postlude.
* If the cite-then-congr path (step 4 option 1) fails for the
  bound goal *after* a 30-minute manual attempt, the worker may
  submit *that single sub-goal* to Aristotle as a one-shot. Do
  not submit the whole theorem statement, and do not poll more
  than once per CLAUDE.md.

### Faithfulness checklist (per CLAUDE.md)

* **No new `def` of a named mathematical concept.** `aOf`, `bOf`,
  `cOf`, `CbaseOf`, `DbaseOf`, `yPrimeSumOf` are *infrastructure*
  abbreviations for expressions that already appear inside
  cycle 052's proof. They do not name any Butcher-textbook concept.
  Document this in a one-line comment above each definition.
* **No new `class` or `structure`.**
* **For the new theorem
  `globalError_closed_form_autonomous_explicit`**:
  * Tautology check — conclusion is a five-fold `∧` of positivity
    + a `∀ n, |ε(n)| ≤ …` bound. None of the conjuncts equals any
    hypothesis.
  * Identity check — proof is replay or wrap, not `exact h`.
  * Hypothesis strength check — same hypothesis list as the
    existential `globalError_closed_form_autonomous`. No
    strengthening.
  * Absent theorem check — N/A (no comments promising other
    theorems in cycle 060).

### Stretch (only if Step 5 lands cleanly with > 30 min budget left)

Sketch (do not commit; just put as a comment block in the file)
the cycle 061 lemma signatures so the next planner has a head
start:

```lean
-- Cycle 061 targets (sketch):
-- private lemma CbaseOf_tendsto_at_zero
--     (M : LinearMultistepMethod k) (L : ℝ) :
--     Tendsto (CbaseOf M L) (nhds 0)
--       (nhds (L * (|M.β 0| * (Σᵢ |M.α i.succ|) + Σᵢ |M.β i.succ|))) :=
--   Cbase_tendsto_at_zero M L  -- already exists at line 1982
--
-- private lemma yPrimeSumOf_tendsto_at_zero
--     (M : LinearMultistepMethod k)
--     {yex : ℝ → ℝ} {x₀ y₀ : ℝ}
--     (hyex_x₀ : yex x₀ = y₀)
--     {start : ℝ → Fin k → ℝ}
--     (hstart : ∀ i : Fin k,
--       Tendsto (fun h : ℝ => start h i) (nhds 0) (nhds y₀))
--     (Y : ℝ → ℕ → ℝ)
--     (hYstart : ∀ h, ∀ i : Fin k, Y h i.val = start h i) :
--     Tendsto (fun h => yPrimeSumOf M yex (Y h) x₀ h) (nhds 0) (nhds 0)
--   := sorry  -- cycle 061 will close
```

The threading of "starting Y from start h" is the cycle 061 design
problem. Don't solve it now — just confirm the signature shape so
cycle 060's `aOf` has the right argument list.

### File-edit checklist for the worker

* [ ] Read `OpenMath/Chapter4/Section404.lean:2700–2900` to
      verify the formulas before introducing the `*Of` definitions
      (Cbase, Dbase, y'sum, a, b, c).
* [ ] Add the six `noncomputable def`s in a single block
      immediately above
      `LinearMultistepMethod.globalError_closed_form_autonomous`
      (line ~3140). Place them *inside* the `OpenMath.Chapter4.Section404`
      namespace. Mark them `private`. Add a one-line comment above
      each indicating it's an abbreviation for the
      cycle-052 / cycle-053 `set`-name from
      `globalError_recurrence_form`.
* [ ] Add `LinearMultistepMethod.globalError_closed_form_autonomous_explicit`
      immediately after
      `LinearMultistepMethod.globalError_closed_form_autonomous`
      (line ~3183) but *before* the `stable_consistent_isConvergent`
      stub at line 3203. Both should remain in the same namespace.
* [ ] Compile via `lake env lean OpenMath/Chapter4/Section404.lean`.
      Expected warnings: 3 pre-existing unused-variable +
      1 declaration-uses-`sorry` (line 3207, shifted to ~3400 by
      the new content).
* [ ] Verify axioms via `mcp__lean-lsp__lean_verify` with the
      fully-qualified theorem name
      `OpenMath.Chapter4.Section404.LinearMultistepMethod.globalError_closed_form_autonomous_explicit`.
      Expected: `[propext, Classical.choice, Quot.sound]`.
* [ ] Check the tautology scanner: only the standing
      `tautology_scanner_false_positives.md` hits should remain
      (lines around 1762, 1950, 2842 — drift expected). If a
      *new* hit appears in any of the new `*Of` definitions or
      the new theorem body, refactor before committing.
* [ ] Update `.prover-state/task_results/cycle_060.md` per
      CLAUDE.md task-results format. Include a faithfulness-check
      section.
* [ ] Commit with message
      `Cycle 060 — explicit (a, b, c) functions for thm:406D outer squeeze`.
* [ ] Push to `origin/Main/Experiments`. Verify
      `git rev-parse HEAD = git rev-parse origin/Main/Experiments`
      after the push.

### Suggested next-cycle pointer (for the cycle 061 planner)

Cycle 061: prove the three limit lemmas `aOf_tendsto_zero`,
`bOf_tendsto`, `cOf_tendsto` using cycles 055–057's helpers
(`b_tendsto_at_zero`, `c_tendsto_at_zero`, `Cbase_tendsto_at_zero`,
`Dbase_tendsto_at_zero`). The new piece is `yPrimeSumOf → 0`,
which requires lifting the starting-method convergence assumption.
Cycle 062 then assembles the outer squeeze using cycle 059's two
sub-squeeze helpers and cycle 060's explicit closed-form. Cycle 063
proves `stable_consistent_isConvergent_autonomous`. Cycle 064+
lifts to non-autonomous (closing line 3207's sorry).

This four-cycle decomposition (060 explicit-functions → 061 limit
lemmas → 062 outer-squeeze assembly → 063 autonomous Tendsto →
064+ non-autonomous lift) replaces cycle 059's "60–100 lines in
cycle 060" estimate, which underestimated the existential threading
work. Cycle 060 is the prerequisite that makes the rest tractable.
