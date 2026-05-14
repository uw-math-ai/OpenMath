# Cycle 216 strategy — Equivalent uniform-threshold refactor + close cycle 215 sorry

## §A — Context

Cycle 215 shipped `RKTableau.compose_equivalent_compose` as a
**sorry-scaffolded** signature (cycle 215 §H abort threshold). The
supervisor scored cycle 215 = −2 (REVERTED) for the sorry increase
(0 → 1). The cycle 215 strategy correctly identified the resolution
path: refactor `Equivalent` to uniform-threshold form
`∃ h₀, ∀ y₀, ...`. This refactor is **mechanical** (all concrete
instances already have y₀-uniform thresholds) and **single-cycle**
in scope (~55 LOC total). Closing it returns sorry count 1 → 0 AND
ships `thm:382A` (382g) form as the cycle's substantive deliverable.

Read these files before coding:
* `.prover-state/issues/compose_equivalent_compose_uniform_threshold.md`
  — the gap analysis, Option A recipe, and recommendation.
* `.prover-state/issues/thm_382A_path.md` (Cycle 215 update section)
  — proposed cycle 216 entry point with draft proof body for
  `compose_equivalent_compose`.
* `OpenMath/Chapter3/Section381.lean` lines 968–986 (`Equivalent`
  definition), 1795–1928 (refl/symm/trans/setoid/setoidSigma),
  2725–2731 (sorry-scaffolded `compose_equivalent_compose`).

Do **NOT** roll back cycle 215's scaffold and walk away. The strategy
is to **close the sorry** by enabling the proof recipe via the
refactor. This cycle's success criterion is sorry count 1 → 0 with
`thm:382A` (382g) form proved axiom-clean.

§441 Phase C.2: GPFS-blocked for 33+ consecutive cycles; skip per
the standing pattern.

## §B — Priority 1: refactor `Equivalent` definition (~5 LOC)

**Step B.1.** Edit `OpenMath/Chapter3/Section381.lean` at lines 980–985:

```lean
def Equivalent {s s' : ℕ} (M : RKTableau s) (M' : RKTableau s') : Prop :=
  ∀ {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [CompleteSpace N]
    (f : N → N) (L : ℝ≥0) (_hL : LipschitzWith L f),
    ∃ h₀ > (0 : ℝ), ∀ (y₀ : N), ∀ h, 0 < h → h ≤ h₀ →
      ∀ y₁ y₁', M.IsRKOneStep f y₀ h y₁ → M'.IsRKOneStep f y₀ h y₁' →
        y₁ = y₁'
```

The only change is **moving `(y₀ : N)` from before the `∃ h₀` to
just inside it** (after `∃ h₀ > (0 : ℝ),`). All four typeclass
binders on `N` and the `(f : N → N) (L : ℝ≥0) (_hL : ...)` binders
stay outside the existential.

Update the docstring (lines ~947–979) to reflect the uniform-threshold
form. Add a one-line note: "Cycle 216: tightened from y₀-pointwise
threshold `∀ y₀, ∃ h₀, ...` to uniform threshold `∃ h₀, ∀ y₀, ...`
per `.prover-state/issues/compose_equivalent_compose_uniform_threshold.md`.
Every concrete instance had a y₀-independent threshold; the refactor
exposes this uniformity, which `thm:382A` consumes."

## §C — Priority 2: port refl/symm/trans (~25 LOC churn)

### C.1 — `equivalent_self` (line 1795)

The current body has the structure:
```
intro N _ _ _ f L hL y₀                          -- introduces y₀ early
... set C; hC_nn; h_LCnn; h_denom_pos
refine ⟨1 / (2 * ((L : ℝ) * C + 1)), by positivity, ?_⟩
intro h hh_pos hh_le y₁ y₁' hY hY'
...
```

The threshold `1 / (2 * ((L : ℝ) * C + 1))` is **y₀-independent**.
Port by reordering binders:

```
intro N _ _ _ f L hL                             -- drop y₀ from outer intro
... set C; hC_nn; h_LCnn; h_denom_pos
refine ⟨1 / (2 * ((L : ℝ) * C + 1)), by positivity, ?_⟩
intro y₀ h hh_pos hh_le y₁ y₁' hY hY'            -- introduce y₀ here
...                                              -- body unchanged
```

Body lines 1805–1821 port verbatim (they use `y₀`, `Y`, `Y'`, etc. but
not the binder position).

### C.2 — `Equivalent.symm` (line 1828)

Port:
```
intro N _ _ _ f L hL
obtain ⟨h₀, h₀_pos, hUniq⟩ := hEq f L hL          -- no y₀ argument
refine ⟨h₀, h₀_pos, ?_⟩
intro y₀ hstep hstep_pos hstep_le y₁ y₁' hY hY'   -- introduce y₀ here
exact (hUniq y₀ hstep hstep_pos hstep_le y₁' y₁ hY' hY).symm
```

The only change beyond binder reorder is passing `y₀` as the first
argument to `hUniq` (since `hUniq` is now `∀ y₀, ∀ h, ...`).

### C.3 — `Equivalent.trans` (line 1863)

Port:
```
intro N _ _ _ f L hL                             -- drop y₀
obtain ⟨h₀₁, h₀₁_pos, hConcl₁⟩ := h₁ f L hL       -- no y₀ argument
obtain ⟨h₀₂, h₀₂_pos, hConcl₂⟩ := h₂ f L hL       -- no y₀ argument
set C_M' : ℝ := ∑ i : Fin s', ∑ j : Fin s', |M'.A i j| with hC_M'_def
... (hC_M'_nn, h_LCnn, h_denom_pos, h₀_M' definitions UNCHANGED — all y₀-independent)
refine ⟨min h₀₁ (min h₀₂ h₀_M'), lt_min h₀₁_pos (lt_min h₀₂_pos h₀_M'_pos), ?_⟩
intro y₀ h hh_pos hh_le y₁ y₃ hY₁ hY₃              -- introduce y₀ here
... (smallness derivations UNCHANGED)
obtain ⟨y₂, hY₂⟩ := M'.IsRKOneStep_exists h hL y₀ h_small_M'
calc y₁ = y₂ := hConcl₁ y₀ h hh_pos hh_le_₁ y₁ y₂ hY₁ hY₂     -- pass y₀ first
    _ = y₃ := hConcl₂ y₀ h hh_pos hh_le_₂ y₂ y₃ hY₂ hY₃        -- pass y₀ first
```

Threshold `C_M'`, `h₀_M'`, etc. are all y₀-independent — definitions
unchanged. Only `hConcl₁` / `hConcl₂` call sites need `y₀` prepended.

### C.4 — Verification after C.1–C.3

Run `lake env lean OpenMath/Chapter3/Section381.lean`. Expected:
* `equivalent_self`, `Equivalent.symm`, `Equivalent.trans` all
  compile.
* Compile time stays ≈ 5–7s warm (per cycles 210–214 baselines).
* If any of the three fails, **STOP** and abort to §G (Risk
  analysis) — do NOT continue to §D until refl/symm/trans are all
  axiom-clean.

Use `lean_verify` to confirm each is axiom-clean
(`[propext, Classical.choice, Quot.sound]`) before proceeding.

## §D — Priority 3: port downstream consumers (~15 LOC churn)

These consumers either PRODUCE an `Equivalent` (need y₀ binder
reorder) or CONSUME one (need to pass y₀ to `hConcl`-style hypotheses).
Port in the order listed; verify build after each.

### D.1 — `equivalent_explicitEuler_self` (line 1163)

Cycle 030 explicit-Euler witness. Port by the same recipe as
`equivalent_self`: `intro` block drops `y₀`, threshold introduction
unchanged, `intro y₀` at the body-introduction step.

### D.2 — `paddedEuler_equivalent_self` (line 2305)

Likely a one-line specialization of `equivalent_self paddedEuler`.
If it's `equivalent_self paddedEuler`, no change needed (the function
signature is unchanged at the value level; only the *body proof*
moved binders). Check whether it's a direct `exact equivalent_self _`
or destructures — adjust accordingly.

### D.3 — `pReduced_equivalent` (line 1944)

Per-step P-reduction preserves equivalence. The body (lines 1948+)
constructs a threshold and proves uniqueness via Banach. Port by
the same pattern as `equivalent_self`: drop `y₀` from outer
`intro`, introduce it after `refine ⟨..., ?_⟩`. The threshold is
y₀-independent (uses M's C, not y₀).

### D.4 — `zeroReduced_equivalent` (line 2013)

Per-step 0-reduction preserves equivalence. Same recipe as
`pReduced_equivalent`.

### D.5 — `PReducesTo.toEquivalent` (line 2154)

Induction composing `pReduced_equivalent` / `zeroReduced_equivalent`
with `Equivalent.trans`. The induction itself doesn't reference
the binder order — it dispatches to the per-step lemmas. **Likely
no body change needed** as long as those per-step lemmas have the
new signature. Verify.

### D.6 — `PEquivalent.toEquivalent` (line 2175)

Existential destructure + double `PReducesTo.toEquivalent` +
`Equivalent.trans` / `Equivalent.symm`. Again likely no body change.
Verify.

### D.7 — `paddedEuler_equivalent_pReduced`, `paddedEuler_equivalent_zeroReduced` (cycle 208)

Specializations of the per-step lemmas to `paddedEuler`. Likely
zero-change once D.3/D.4 port.

### D.8 — `PEquivalent.toEquivalent_and_toPhiEquivalent` (line 2190)

Cycle 208 umbrella. Zero-change.

### D.9 — `Equivalent.setoid` (line 1906)

Setoid instance. The `iseqv` field references `equivalent_self`,
`Equivalent.symm.{u}`, `Equivalent.trans.{u}`. **Zero-change** —
only their bodies moved.

### D.10 — `Equivalent.setoidSigma` (line 1922)

Σ-typed setoid. Same as D.9.

### D.11 — Cycle 211/212 non-vacuity examples

Setoid-refl and Quotient.mk examples (~line 2316+). Zero-change.

### D.12 — Verification after D.1–D.11

Run `lake env lean OpenMath/Chapter3/Section381.lean`. Expected
clean compile in ~7s. Run `lean_verify` on each of:
* `pReduced_equivalent`
* `zeroReduced_equivalent`
* `PReducesTo.toEquivalent`
* `PEquivalent.toEquivalent`
* `Equivalent.setoid`
* `Equivalent.setoidSigma`

All must remain axiom-clean.

## §E — Priority 4: close `compose_equivalent_compose` (~20 LOC body)

Replace the `:= sorry` body at line 2731 with the route B.1 recipe
from `.prover-state/issues/thm_382A_path.md` (Cycle 215 update,
Cycle 216 entry point section). Draft body:

```lean
theorem compose_equivalent_compose.{u}
    {s₁ s₂ : ℕ}
    (M₁ M₁' : RKTableau s₁) (M₂ M₂' : RKTableau s₂)
    (hEq₁ : @Equivalent.{u} s₁ s₁ M₁ M₁')
    (hEq₂ : @Equivalent.{u} s₂ s₂ M₂ M₂') :
    @Equivalent.{u} (s₁ + s₂) (s₁ + s₂) (M₁.compose M₂) (M₁'.compose M₂') := by
  intro N _ _ _ f L hL
  obtain ⟨H₁, hH₁_pos, hEq₁_app⟩ := hEq₁ f L hL
  obtain ⟨H₂, hH₂_pos, hEq₂_app⟩ := hEq₂ f L hL
  refine ⟨min H₁ H₂, lt_min hH₁_pos hH₂_pos, ?_⟩
  intro y₀ H hH_pos hH_le y_final y_final' h_step h_step'
  have hH_le_H₁ : H ≤ H₁ := le_trans hH_le (min_le_left _ _)
  have hH_le_H₂ : H ≤ H₂ := le_trans hH_le (min_le_right _ _)
  obtain ⟨y_mid, h_M₁_step, h_M₂_step⟩ :=
    (compose_isRKOneStep_iff M₁ M₂ f y₀ H y_final).mp h_step
  obtain ⟨y_mid', h_M₁'_step, h_M₂'_step⟩ :=
    (compose_isRKOneStep_iff M₁' M₂' f y₀ H y_final').mp h_step'
  have hmid_eq : y_mid = y_mid' :=
    hEq₁_app y₀ H hH_pos hH_le_H₁ y_mid y_mid' h_M₁_step h_M₁'_step
  rw [hmid_eq] at h_M₂_step
  exact hEq₂_app y_mid' H hH_pos hH_le_H₂ y_final y_final' h_M₂_step h_M₂'_step
```

**Key changes vs cycle 215's failed attempt:**
* `obtain` of `hEq₁`/`hEq₂` no longer passes `y₀` (refactor moved
  `y₀` *inside* the existential).
* `hEq₁_app` and `hEq₂_app` now take `y₀` as a leading argument
  (because they quantify over `y₀` inside the existential).
* The critical line: `hEq₂_app y₀_arg H hH_pos hH_le_H₂ y_final
  y_final' h_M₂_step h_M₂'_step` — the `y₀_arg` is **`y_mid'`**
  (not the outer `y₀`), which the refactored definition allows
  because `hEq₂_app` quantifies universally over y₀ inside the
  existential. The M₂ step in the composite fires from `y_mid'`,
  which matches the universal binding.

**Also drop the underscore prefixes** on `_hEq₁` / `_hEq₂` — the
body now consumes them, so they need their real names. Cycle 215
underscored them to satisfy the unused-variable linter on the
sorry body.

**Update the docstring** (lines 2643–2724): replace the long
"STATUS: scaffolded with `sorry` per cycle 215 abort threshold"
block with a concise "closed cycle 216 via the cycle 215 strategy's
route B.1 recipe under the refactored `Equivalent`" note. Keep the
faithfulness notes (382f vs 382g, fixed-stage restriction).

## §F — Priority 5: update status records (~10 LOC churn)

### F.1 — `extraction/formalization_data/lean_status.json`

Update `thm:382A` row:
* `status`: `"partial"` → `"formalized"`.
* `cycle`: 215 → 216.
* `note`: extend with "Cycle 216: closed via `Equivalent`
  uniform-threshold refactor (Option A from
  `compose_equivalent_compose_uniform_threshold.md`) — definition
  tightened to `∃ h₀, ∀ y₀, ...` form; all 9 downstream consumers
  ported verbatim (binder reorder only, no threshold changes);
  cycle 215 sorry-scaffold replaced with the route B.1 body
  (~20 LOC); axiom-clean."

### F.2 — `plan.md`

Update `thm:382A` row: `[~]` → `[x]`. Extend the line with the
cycle 216 closure note.

### F.3 — `.prover-state/issues/compose_equivalent_compose_uniform_threshold.md`

Add a "Cycle 216 update — CLOSED" section at the top documenting
the refactor and the final body.

### F.4 — `.prover-state/issues/thm_382A_path.md`

Update the "Recommended cycle plan" section to reflect that cycle
216 closed the (382g) form. The cycle 217+ outlook (heterogeneous
form, `composeQ` lift, group structure) remains valid.

### F.5 — `.prover-state/task_results/cycle_216.md`

Write the cycle results documenting:
* Worked on: cycle 215 sorry closure via `Equivalent` refactor.
* Approach: the §B–§E plan above.
* Result: SUCCESS — `thm:382A` (382g) form axiom-clean, sorry
  count 1 → 0.
* Faithfulness check: (382g) form is Butcher's own equivalent
  reformulation of (382f); fixed-stage is a deferred extension
  to cycle 217+.
* Dead ends: cycle 215 non-uniform threshold (now resolved by
  refactor).
* Discovery: confirm the issue file's mechanical-port estimate
  matches reality; record any unexpected sticking points.
* Suggested next approach: cycle 217 — heterogeneous-stage form
  of `compose_equivalent_compose`, OR pivot to a fresh entity if
  the planner deems §382 group structure work multi-cycle.

## §G — Risk analysis and abort thresholds

**Risk 1: a downstream consumer's body genuinely depends on
binder order.** Mitigation: §C.4 verification step catches this
before §D. If a consumer's body uses something more invasive than
`hConcl y₀` reordering — e.g. it pattern-matches on the existential
explicitly or has `y₀` inside its own `set`/`have` chain — flag
and report. The cycle 215 strategy verified all concrete instances
have y₀-uniform thresholds; if a consumer turns out to be non-uniform
internally, that's a new issue (file as a follow-up, don't try to
fix this cycle).

**Risk 2: `lean_verify` reports unexpected axioms.** Mitigation:
all ports are mechanical binder reorders that preserve the proof
content. If `sorryAx` appears anywhere in §C or §D output, that's
a bug — fix immediately. If `Classical.choice` appears in
`equivalent_self` (which currently doesn't use it), that signals
the refactor accidentally introduced a non-constructive step;
investigate.

**Risk 3: `compose_equivalent_compose` body still fails.** Mitigation:
the cycle 215 type error was specifically the y₀ vs y_mid' mismatch
on `hEq₂_app`. The refactor (universal binding of y₀ inside the
existential) directly addresses this. If a *different* error arises
(e.g. `compose_isRKOneStep_iff.mp` signature mismatch, or a Lean
4-version-specific elaboration issue), reproduce it and report.

**Risk 4: compile time explodes.** Section381.lean has been ≈4–7s
warm rebuild for cycles 210–215. If a port pushes it past 20s, that
suggests an elaboration regression (likely a `simp` set or
`obtain`-with-named-arg issue). Investigate before continuing.

**Abort threshold §H (mirrors cycle 215 §H):** if §B or §C cannot
land cleanly (i.e. refl/symm/trans all axiom-clean) by ~50% cycle
budget, **STOP the refactor, revert Section381.lean to HEAD, and
ship a pure rollback of cycle 215's `compose_equivalent_compose`
sorry-scaffold.** Pure rollback recipe:

* Delete lines 2622–2731 (cycle 215 docstring + theorem +
  `:= sorry`) and the associated cycle 215 example block.
* Restore `lean_status.json` `thm:382A` row: `partial` →
  `unformalized`, drop `lean_file`/`lean_symbol`, restore the
  cycle 213/214 heritage note.
* Restore `plan.md` `thm:382A` row: `[~]` → `[ ]`.
* Update `compose_equivalent_compose_uniform_threshold.md` with a
  "Cycle 216 update — rollback" section explaining the abort.

The rollback yields sorry count 1 → 0 cleanly, which is the minimum
viable cycle deliverable.

## §H — What NOT to try (explicit blocklist)

These were ruled out by the cycle 215 worker; do NOT re-attempt:

1. **Destructure `hEq₂` at `y_mid'`** (without the refactor):
   produces threshold `H₂(y_mid')` depending on `y_mid'`, which
   depends on `H` — circular. Only works AFTER the refactor.
2. **Global infimum** `inf_{y_mid'} H₂(y_mid')`: can be 0 without
   continuity guarantees. Don't pursue.
3. **`IsRKOneStep_exists` insertion to canonicalize `y_mid'`**:
   preserves the circular dependence on `H`. Don't pursue.
4. **Continuity argument on the extracted threshold function**:
   no continuity guarantee from the abstract `Equivalent` type.
   Don't pursue.
5. **`M̂` notation with combining circumflex**: Lean rejects
   combining marks in identifiers. Use prime notation
   (`M₁'`/`M₂'`) per the cycle 215 convention.
6. **Strengthen via uniform Lipschitz constant or compact-set
   hypothesis**: that's a different change with broader impact.
   The uniform-threshold refactor is sufficient.
7. **Adding a wholly new `EquivalentUniform` predicate alongside
   `Equivalent`**: creates dual definitions and a long-term
   maintenance burden. The textbook uses one notion, our Lean
   should too. Refactor the existing definition.

## §I — Verification commands

Run these in order:

1. After §B (definition only): `lake env lean
   OpenMath/Chapter3/Section381.lean` — expect many type errors
   in §C/§D targets (because their bodies haven't been ported
   yet). This is normal; the goal here is just to confirm the
   definition itself parses.
2. After §C: same compile + `lean_verify
   OpenMath.Chapter3.Section312.RKTableau.equivalent_self` /
   `.Equivalent.symm` / `.Equivalent.trans`. All three must be
   axiom-clean.
3. After §D: same compile + `lean_verify` on each downstream
   consumer (D.1–D.11). All axiom-clean.
4. After §E: same compile + `lean_verify
   OpenMath.Chapter3.Section312.RKTableau.compose_equivalent_compose`.
   Must be axiom-clean (`[propext, Classical.choice, Quot.sound]`,
   NO `sorryAx`).
5. Final sanity:
   * `grep -c sorry OpenMath/Chapter3/Section381.lean` — must
     output `0`.
   * Cycle 213's `compose_of_isRKOneStep` and cycle 214's
     `compose_isRKOneStep_iff` re-verify axiom-clean (regression
     check).

## §J — Aristotle

Do not submit Aristotle jobs this cycle. The refactor + close is
local, mechanical work; Aristotle would only add latency. Save the
job slot for tractable submissions later (e.g. when §441 Phase C.2
GPFS recovers).

## §K — Loop hygiene

* Do NOT edit `scripts/autonomous_loop.py`.
* Do NOT raise `maxHeartbeats`.
* Do NOT introduce `axiom` / `constant`.
* Commit only after all of §B–§F succeed; if abort §H fires,
  commit only the pure rollback.
* §441 Phase C.2: GPFS-blocked (34th consecutive). Skip per
  standing pattern. Cite `.prover-state/issues/cycle_182_gpfs_slowness.md`
  in cycle results if attempted.

## §L — Cycle deliverable bar

**Minimum viable**: sorry count 1 → 0 (either via successful refactor
+ close, OR via §H abort + cycle 215 rollback).

**Target**: cycle 215 sorry closed via the refactor; `thm:382A`
(382g) form axiom-clean; status records updated to `formalized`/`[x]`;
`thm:382A` row in `plan.md` records the cycle 216 closure with the
refactor context. Five test results axiom-clean: `equivalent_self`,
`Equivalent.symm`, `Equivalent.trans`, `compose_isRKOneStep_iff`
(cycle 214 regression check), `compose_equivalent_compose` (this
cycle's headline).

**Stretch (do NOT pursue if §B–§E take >70% budget)**: extend
`compose_equivalent_compose` from fixed-stage `M₁ M₁' : RKTableau s₁`
to heterogeneous-stages `M₁ : RKTableau s₁, M₁' : RKTableau s₁'`,
mirroring cycle 217's outlook in `thm_382A_path.md`. Body should
port directly (the proof works at the abstract space N, not the
stage count); risk is in the type signature compatibility with cycle
214's `compose_isRKOneStep_iff`. Skip if not trivially clean.
