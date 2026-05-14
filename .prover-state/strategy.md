# Cycle 214 Strategy

## §A — Skip the §441 Phase C.2 GPFS smoke test

Per the 31-cycle pathology recorded in
`.prover-state/issues/cycle_182_gpfs_slowness.md` (cycles 182–213 all
timed out at ~5 min wall with ≤0.5% CPU), do **NOT** spend cycle 214
on another smoke-test attempt at `OpenMath/Chapter4/Section441.lean`.
The pathology has not abated for 31 consecutive cycles; one more
attempt provides no signal. Skip Priority-0 entirely and proceed
straight to the §381 work below.

If you want to record the heartbeat, you may run a single
`time timeout 60 lake env lean OpenMath/Chapter4/Section441.lean &`
in the background and forget about it — but do not block on it, do
not wait for it, and do not let the 60-second timeout consume any
strategy budget. Strongly preferred: skip entirely.

## §B — Priority 1: ship `compose_isRKOneStep_iff` (forward direction + iff)

**Target**: in `OpenMath/Chapter3/Section381.lean`, immediately after
cycle 213's `compose_of_isRKOneStep` (currently ends at line ~2621,
just before `PReducesTo.toEquivalent_and_toPhiEquivalent` at line
2628), add the **full iff**:

```lean
/-- *Compose factors through `M₁`-then-`M₂` — full iff (Butcher §382 (382b–e)).*
One step of `M₁.compose M₂` at step size `H` from `y₀` to `y_final`
factors as sequential `M₁` then `M₂` steps at the *same* `H` (no
rescaling). Note: this is a *structural* identity that holds
unconditionally (no Lipschitz, no smallness, no `CompleteSpace`)
because both directions are purely algebraic — the composite stage
tuple decomposes into `Fin.append Y₁ Y₂` block-wise, exposing the
underlying `M₁`/`M₂` stages. Closes Gap A of the path to `thm:382A`
per `.prover-state/issues/compose_isRKOneStep_iff_scoping.md`. -/
theorem compose_isRKOneStep_iff {s₁ s₂ : ℕ}
    (M₁ : RKTableau s₁) (M₂ : RKTableau s₂)
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (f : N → N) (y₀ : N) (H : ℝ) (y_final : N) :
    (M₁.compose M₂).IsRKOneStep f y₀ H y_final ↔
      ∃ y_mid : N,
        M₁.IsRKOneStep f y₀ H y_mid ∧
        M₂.IsRKOneStep f y_mid H y_final
```

**Critical observation that overrides the scoping doc**: the scoping
doc (`compose_isRKOneStep_iff_scoping.md` §4.2) anticipated the
forward direction would need `IsRKOneStep_exists` (cycle 205) +
smallness + Lipschitz. **It does not.** Look at the unpacking pattern
that cycle 213 used for the reverse direction (lines 2600–2621): it
provided `Fin.append Y₁ Y₂` directly as the stage tuple, no Banach
required. The forward direction is the mirror image — project a
given composite stage tuple `Y_compose` onto `Y_top` and `Y_bot`,
define `y_mid` *algebraically* as `y₀ + H • ∑ i, M₁.b i • f (Y_top i)`,
and witness M₁/M₂'s `IsRKOneStep` via these projections. The
output-equation halves close by `rfl` (for M₁'s, by definition of
`y_mid`) and by the same `smul_add / ← add_assoc / ← hY₁_out`
3-step regroup-and-collapse idiom cycle 213 used (for M₂'s).

**No smallness, no Lipschitz, no `[CompleteSpace N]` is needed for
the iff itself.** Smallness only enters if/when you want
*uniqueness* of `y_mid`, which is not part of the iff.

## §C — Detailed proof recipe for the forward direction

The reverse direction is one line — invoke cycle 213:

```lean
theorem compose_isRKOneStep_iff … :
    (M₁.compose M₂).IsRKOneStep f y₀ H y_final ↔
      ∃ y_mid : N, … := by
  refine ⟨?_, ?_⟩
  · -- forward (the substantive direction, ~30 LOC, see §C.1 below)
    intro hC
    obtain ⟨Y_compose, hY_compose_stage, hY_compose_out⟩ := hC
    -- … build y_mid, Y_top, Y_bot as in §C.1 below
    sorry  -- placeholder while drafting; close as detailed
  · -- reverse: invoke cycle 213
    rintro ⟨y_mid, h₁, h₂⟩
    exact RKTableau.compose_of_isRKOneStep M₁ M₂ h₁ h₂
```

Do not commit with a `sorry`; the placeholder is for incremental
drafting only.

### §C.1 — Forward direction body (target ~30 LOC, mirror of cycle 213's body)

```lean
intro hC
obtain ⟨Y_compose, hY_compose_stage, hY_compose_out⟩ := hC
-- Project the composite stage tuple onto the two blocks (inline lambdas
-- are simpler than `set` here — see Risk 5 below).
refine ⟨y₀ + H • ∑ i, M₁.b i • f (Y_compose (Fin.castAdd s₂ i)), ?_, ?_⟩
· -- M₁.IsRKOneStep f y₀ H y_mid: witness with the top projection.
  refine ⟨fun i₁ => Y_compose (Fin.castAdd s₂ i₁), ?_, rfl⟩
  intro i₁
  -- Specialize the composite stage equation at the top-block index.
  have hstage := hY_compose_stage (Fin.castAdd s₂ i₁)
  rw [Fin.sum_univ_add] at hstage
  simp only [compose_A_topLeft, compose_A_topRight,
    zero_smul, Finset.sum_const_zero, add_zero] at hstage
  -- hstage now matches the M₁ stage equation on the top projection
  exact hstage
· -- M₂.IsRKOneStep f y_mid H y_final: witness with the bottom projection.
  refine ⟨fun i₂ => Y_compose (Fin.natAdd s₁ i₂), ?_, ?_⟩
  · -- Stage equation
    intro i₂
    have hstage := hY_compose_stage (Fin.natAdd s₁ i₂)
    rw [Fin.sum_univ_add] at hstage
    simp only [compose_A_botLeft, compose_A_botRight] at hstage
    -- hstage : Y_compose (Fin.natAdd s₁ i₂)
    --   = y₀ + H • (∑ j₁, M₁.b j₁ • f (Y_compose (Fin.castAdd s₂ j₁)) +
    --                ∑ j₂, M₂.A i₂ j₂ • f (Y_compose (Fin.natAdd s₁ j₂)))
    rw [smul_add, ← add_assoc] at hstage
    -- The first parenthesized term is exactly our y_mid (by def). Goal is:
    -- Y_compose (Fin.natAdd s₁ i₂)
    --   = (y₀ + H • ∑ i, M₁.b i • f (Y_compose (Fin.castAdd s₂ i)))
    --     + H • ∑ j, M₂.A i₂ j • f (Y_compose (Fin.natAdd s₁ j))
    exact hstage
  · -- Output equation: y_final = y_mid + H • ∑ i, M₂.b i • f (bottom proj)
    rw [Fin.sum_univ_add] at hY_compose_out
    simp only [compose_b_castAdd, compose_b_natAdd] at hY_compose_out
    rw [smul_add, ← add_assoc] at hY_compose_out
    exact hY_compose_out
```

### §C.2 — Why `rfl` works for M₁'s output equation

`y_mid := y₀ + H • ∑ i, M₁.b i • f (Y_compose (Fin.castAdd s₂ i))`
by definition (literally what's written in `refine ⟨_, ?_, ?_⟩`).
The output clause of `M₁.IsRKOneStep f y₀ H y_mid` requires
`y_mid = y₀ + H • ∑ i, M₁.b i • f (Y i)` where `Y` is the witness
tuple — here `Y = fun i₁ => Y_compose (Fin.castAdd s₂ i₁)`. Same
RHS by `rfl`. **DO NOT** try to invoke `hY_compose_out` here — that
is reserved for the M₂ output equation.

### §C.3 — `Fin.append_left` / `Fin.append_right` are NOT needed in the forward direction

These cycle-213 simp lemmas operate on the witness pattern
`Fin.append Y₁ Y₂ (Fin.castAdd _ _)` reducing it to `Y₁ _`. In the
**forward** direction we are *not* constructing a `Fin.append` —
we are projecting from an arbitrary `Y_compose`. Drop these from
the `simp only` set. The relevant lemmas in the forward direction
are exactly the `compose_A_*` / `compose_b_*` family plus the
cleanup lemmas `zero_smul`, `Finset.sum_const_zero`, `add_zero`.
See **Risk 2** below for diagnostic backup.

### §C.4 — Closure idiom recap (worth reusing verbatim)

The 3-step `rw [smul_add, ← add_assoc]` idiom that cycle 213 used
(plus a `← hY₁_out` step that closed by rewriting against M₁'s
output formula) reduces here to just `rw [smul_add, ← add_assoc]`
— no `← hY₁_out` step. The M₂ stage/output equations close once
the `(y₀ + H • Σ M₁.b · f (Y_top))` block is left-grouped, because
by definition that block *is* `y_mid`. Lean accepts this by
definitional equality on the `exact`.

If Lean's elaborator does NOT accept the definitional collapse
(possible if `simp only` reshuffles the term in unexpected ways),
fall back to writing the goal explicitly: `show Y_compose
(Fin.natAdd s₁ i₂) = (y₀ + H • ∑ i, M₁.b i • f (Y_compose
(Fin.castAdd s₂ i))) + H • ∑ j, M₂.A i₂ j • f (Y_compose
(Fin.natAdd s₁ j))` before the `exact`, and use `change` if
needed to force the unfolding.

## §D — Anticipated risks (prevention recipes)

### Risk 1 — `simp only` does not close the M₁ stage goal exactly

If after `simp only [compose_A_topLeft, compose_A_topRight,
zero_smul, Finset.sum_const_zero, add_zero]` the hypothesis shape
is NOT what's expected, use `lean_goal` or `lean_term_goal` MCP at
the point of the `exact` to inspect the actual shape. Common
fix: insert `show … = …` between simp and exact to bridge a
syntactic gap, or add `Fin.castAdd_zero, Fin.natAdd_zero` to the
simp set if Lean is keeping the abstract `Fin.castAdd s₂ i₁`
unreduced.

### Risk 2 — Why no `Fin.append_*` in the forward direction

In cycle 213's reverse direction, the witness tuple was
`Fin.append Y₁ Y₂`, and the simp set used
`Fin.append_left, Fin.append_right` to drill through that name
into `Y₁ _` and `Y₂ _`. In cycle 214's forward direction, the
witness tuple is *the projection* of `Y_compose` — there is no
`Fin.append` to drill through. The composite-A and composite-b
simp lemmas (`compose_A_topLeft`, etc.) operate on the
**index-side** `Fin.castAdd` / `Fin.natAdd` patterns directly,
producing the right scalar entries without needing the
function-side `Fin.append` machinery. **Drop**
`Fin.append_left, Fin.append_right` from the forward simp set.

If they accidentally fire on an unrelated `Fin.append` somewhere
in `compose`'s definition expansion, you'll see "useless" goal
changes — diagnosis: use `lean_goal` before and after the simp to
spot the regression.

### Risk 3 — The `← add_assoc` rewrite doesn't match the parenthesisation

If the hypothesis after `smul_add` has shape `y₀ + (H • A + H • B)`
(right-leaning parenthesisation from `smul_add`'s natural form),
`← add_assoc` rewrites to `(y₀ + H • A) + H • B` (left-leaning).
If Lean's pretty-printer shows different parens than your mental
model, **use `lean_goal` MCP to inspect the actual term shape after
each rewrite; do not guess.** Once you see the actual shape, the
fix is either an additional `add_comm`-flavour rewrite or an
explicit `show` to match.

### Risk 4 — `IsRKOneStep` destructure shape mismatch

`IsRKOneStep := ∃ Y, (∀ i, …) ∧ y₁ = …` is anonymous, so the
pattern `⟨Y, hstage, hout⟩` works (the binary `∧` is flat against
the anonymous existential, matching the same shape cycle 213 used
successfully at line 2600). The worker MUST NOT try
`⟨Y, ⟨hstage, hout⟩⟩` — that would be valid syntax but slightly
less idiomatic; both work. The danger is using the wrong arity
(e.g. `⟨Y, hstage⟩` missing `hout`).

### Risk 5 — `set Y_top with hY_top` complications

`set` introduces a local definition but does NOT automatically
rewrite existing hypotheses unless you use `set ... with hY_top`
followed by manual `rw [← hY_top] at hstage`. **Recommended**:
skip `set` entirely; inline `Y_top` and `Y_bot` as anonymous `fun
i₁ => Y_compose (Fin.castAdd s₂ i₁)` lambdas (as the §C.1 recipe
above shows). The proof body shrinks to ~25 LOC and avoids any
`set` propagation issues.

### Risk 6 — Universe annotation `.{u}` needed?

**No.** `compose_isRKOneStep_iff` operates at the `IsRKOneStep`
level (one layer below `Equivalent`). `IsRKOneStep` is not
universe-polymorphic over the result type (it's parameterised on
`{N : Type*}` with normed-space classes; that's fine). Cycle 213
shipped `compose_of_isRKOneStep` without any `.{u}` annotation and
it is axiom-clean — same applies here. Cycle 204's universe
discipline is local to `Equivalent` and does not propagate down.

### Risk 7 — `compose_A_topRight`-generated `0 • f _` does not collapse

After `simp only [compose_A_topRight]`, the term `0 • f (Y_compose
(Fin.natAdd s₁ j₂))` appears inside an inner sum `∑ j₂, …`. To
collapse to 0, the simp set needs `zero_smul` followed by
`Finset.sum_const_zero` (or `Finset.sum_eq_zero` plus per-term
zero). The recommended simp set
`[compose_A_topLeft, compose_A_topRight, zero_smul,
Finset.sum_const_zero, add_zero]` covers this in one pass. If it
doesn't fire, the issue is term-order — add `mul_zero` or
`smul_zero` as backup.

## §E — Priority 2: non-vacuity example on `paddedEuler`

After the iff theorem, add an `example` immediately after the
existing cycle 213 paddedEuler example (which currently ends at
line 2694, in the `OpenMath.Chapter3.Section381` namespace
block). This exercises the **forward** direction (the `.mp`) on
the cycle-213 witness:

```lean
/-- *Non-vacuity for the forward direction of `compose_isRKOneStep_iff`
(cycle 214 P1).* Extracts the intermediate value `y_mid` from a
known composite output. The composite output `(y₀ + H • f y₀) + H
• f (y₀ + H • f y₀)` (cycle 213) factors as `paddedEuler` stepping
from `y₀` to `y₀ + H • f y₀`, then `paddedEuler` stepping from
`y₀ + H • f y₀` to the final value. -/
example {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (f : N → N) (y₀ : N) (H : ℝ) :
    ∃ y_mid : N,
      paddedEuler.IsRKOneStep f y₀ H y_mid ∧
      paddedEuler.IsRKOneStep f y_mid H
        ((y₀ + H • f y₀) + H • f (y₀ + H • f y₀)) :=
  (RKTableau.compose_isRKOneStep_iff paddedEuler paddedEuler f y₀ H _).mp
    (RKTableau.compose_of_isRKOneStep paddedEuler paddedEuler
      (paddedEuler_isRKOneStep f y₀ H)
      (paddedEuler_isRKOneStep f (y₀ + H • f y₀) H))
```

This composes cycle 213's reverse-direction witness with cycle 214's
forward direction — a round-trip through the iff. Useful both as
non-vacuity and as a sanity check that the forward direction
correctly retrieves a `y_mid` value (specifically, `y_mid = y₀ + H
• f y₀` algebraically, though the example only states existence).

## §F — Priority 3 (stretch, only if §B and §E ship cleanly with budget remaining): scoping for `thm:382A`

If `compose_isRKOneStep_iff` + the non-vacuity example land within
the first ~60 minutes of the cycle, write a **scoping document**
(not Lean code) at `.prover-state/issues/thm_382A_via_382g_scoping.md`
that sketches the proof of `thm:382A` directly via the (382g)
reformulation:

```
m₁ ≡ m̂₁ ∧ m₂ ≡ m̂₂ → m₁.compose m₂ ≡ m̂₁.compose m̂₂
```

Per `.prover-state/issues/thm_382A_path.md` §"(382g) reformulation",
this form avoids Gap B (the Σ-typed quotient packaging) and uses
only Gap A (closed via cycles 213 + 214). The scoping doc should
cover:

1. **Smallness threshold construction**: how to take the *minimum*
   of the two equivalences' (cycle 206 trans-recipe) thresholds
   plus a third `H₀ := 1/(2*(L*(C₁+C₂)+1))` term (`C₁`, `C₂`
   being the compose-row sums of `m₁` and `m₂`).
2. **Proof sketch**: unpack `hEq₁ : m₁.Equivalent m̂₁` and
   `hEq₂ : m₂.Equivalent m̂₂`; pick a small `H`; apply
   `compose_isRKOneStep_iff.mp` to a putative
   `(m₁.compose m₂).IsRKOneStep f y₀ H y_final` to extract the
   intermediate `y_mid`; apply `hEq₁` at the M₁ step (which
   requires `m₁` and `m̂₁` to land at the *same* `y_mid`; this is
   where smallness + Banach uniqueness via cycle 204's
   `RKStageMap_fixedPoint_unique` enters); apply `hEq₂` at the M₂
   step to swap the final output; re-pack via
   `compose_of_isRKOneStep` (cycle 213) into
   `m̂₁.compose m̂₂`'s output.
3. **Key obstacle**: the `hEq₁` swap fires only when `m₁` and
   `m̂₁` both produce *the same* `y_mid` on the *same* `(f, y₀, H)`.
   `Equivalent` asserts uniqueness of one-step output, so this is
   exactly the hypothesis needed — but the threshold construction
   needs care.
4. **LOC estimate** and **proof challenges**: estimate 60–100 LOC
   in cycle 215, ideally with a P1 split of "prove the algebraic
   half" and "wire up smallness".

Do **NOT** attempt to ship `thm:382A` in cycle 214 — the scoping is
the stretch deliverable; the proof itself is cycle 215+.

If the iff or non-vacuity stall, **drop P3 entirely**.

## §G — What NOT to do

1. **DO NOT introduce `[CompleteSpace N]` on the iff's signature.**
   The iff is purely structural and does not require completeness.
   Including it would make the theorem strictly weaker than
   necessary and would diverge from cycle 213's
   `compose_of_isRKOneStep` (which also omits `CompleteSpace`).

2. **DO NOT add smallness or Lipschitz hypotheses to the iff.**
   Same reason as above — purely algebraic identity. Both
   directions close without any analytic hypotheses.

3. **DO NOT invoke `IsRKOneStep_exists` (cycle 205) or
   `RKStageMap_fixedPoint_unique` (cycle 204).** The scoping doc
   anticipated these would be needed; they are not. The forward
   direction works by *projection*, not by Banach existence.

4. **DO NOT use the `set Y_top with hY_top; rw [← hY_top] at …`
   pattern unless necessary.** If your first attempt with `set`
   produces goals that don't match cleanly, immediately fall back
   to inlining the projection lambda (as §C.1 shows). Save your
   time budget.

5. **DO NOT bump sorry count by adding an iff scaffold with a
   sorry'd forward direction "to be filled later".** Either ship
   the iff complete (both directions), or skip the iff packaging
   and ship only a separate `compose_to_isRKOneStep` forward
   theorem (analogous to cycle 213's `compose_of_isRKOneStep` for
   the reverse). Avoid the cycle-200 supervisor-scoring incident:
   sorry count must remain at 0.

6. **DO NOT spend time on the §441 Phase C.2 smoke test.** Per §A,
   the GPFS pathology has reproduced 31 consecutive times; no
   signal in attempt 32.

7. **DO NOT attempt `thm:382A` proper in cycle 214.** It is the
   §F stretch *scoping* deliverable only. The proof itself is
   multi-cycle work.

8. **DO NOT edit `scripts/autonomous_loop.py` or any supervisor
   infrastructure.** That is loop-maintainer territory per CLAUDE.md.

9. **DO NOT use `lean_run_code` or `lean_build` for verification
   unless absolutely necessary** — they are slow. Prefer
   `lake env lean OpenMath/Chapter3/Section381.lean` for compile
   checks (Section381 has been warm at ~5–7s for the past 30
   cycles per the heartbeat).

10. **DO NOT use universe annotations `.{u}`** on
    `compose_isRKOneStep_iff` or anywhere else in cycle 214.
    Cycle 213's `compose_of_isRKOneStep` ships axiom-clean
    without them. They are only needed for `Equivalent`-level
    work (cycles 204/211/212).

## §H — Verification

After the worker writes the iff + non-vacuity example:

1. `lake env lean OpenMath/Chapter3/Section381.lean` — must exit 0.
2. `grep -c sorry OpenMath/Chapter3/Section381.lean` — must return 0.
3. `lean_verify
   OpenMath.Chapter3.Section312.RKTableau.compose_isRKOneStep_iff`
   — must return `[propext, Classical.choice, Quot.sound]` only.
4. Spot-check via `lean_verify` on cycle 213's
   `OpenMath.Chapter3.Section312.RKTableau.compose_of_isRKOneStep`
   and cycle 212's
   `OpenMath.Chapter3.Section312.RKTableau.Equivalent.setoidSigma`
   to confirm no regressions.

If any of (1)–(3) fail, **do not commit**. Debug, fix, re-verify.
If a fix requires more than 20 minutes of tactic exploration,
roll back to a smaller deliverable (e.g. ship `compose_to_isRKOneStep`
as a separate forward theorem, without the iff packaging) rather
than committing broken work.

## §I — Faithfulness

The iff is infrastructure for `thm:382A`, not a textbook entity
itself — no `extraction/formalization_data/entities/*.json` row to
consult. Document in the docstring that:

- The structural identity is Butcher §382 equations (382b–e), p. 285.
- It holds *unconditionally* (no smallness/Lipschitz/completeness)
  because both directions are algebraic.
- It closes **Gap A** of the path to `thm:382A` per
  `.prover-state/issues/compose_isRKOneStep_iff_scoping.md` and
  `.prover-state/issues/thm_382A_path.md`.

After landing, append a "**Cycle 214 update**" section to
`.prover-state/issues/compose_isRKOneStep_iff_scoping.md` recording:
- Forward direction shipped axiom-clean.
- Critical observation: no Banach/smallness/Lipschitz needed
  (overrides the scoping doc's anticipation).
- Iff packaging complete.
- Recommended next entry point: `thm:382A` via the (382g) form
  (cycle 215, scoped per §F if you took the stretch).

Update the def:381A row of `plan.md` to mention the iff closure
(brief, one-sentence appendix to the existing cycle 213 paragraph).
**Do not** update `lean_status.json` for `thm:382A` — that remains
`unformalized` until cycle 215+ ships the actual theorem. But DO
update the cycle reference for def:381A's row in `lean_status.json`
to 214 to record the iff infrastructure landing.

## §J — Time budget

| Step | Target time |
| --- | --- |
| Read this strategy + grep cycle 213 lines for reference | 5 min |
| Write iff statement + reverse direction (1-line) | 5 min |
| Write forward direction body (P1) | 25 min |
| Debug + close any tactic stalls | 15 min |
| Non-vacuity example (§E, P2) | 10 min |
| Verification (`lake env lean`, `lean_verify`) | 5 min |
| Faithfulness notes + plan.md + issue update | 10 min |
| **§F stretch (if budget allows)** | 30 min |
| Task results + commit | 15 min |
| **Total without stretch** | **~90 min** |
| **Total with stretch** | **~120 min** |

If you exceed 90 minutes without §F, skip the stretch entirely and
commit the iff + non-vacuity. If you exceed 120 minutes with §F
incomplete, commit what you have minus the stretch doc.

## §K — One-line summary for the worker

**Ship `compose_isRKOneStep_iff` (forward direction algebraic, no
Banach/smallness/Lipschitz needed — mirror cycle 213's body shape
with projections instead of `Fin.append`), add a paddedEuler
non-vacuity example exercising the `.mp` direction, optionally
write a `thm:382A` scoping doc if time remains. Sorry count must
remain at 0.**
