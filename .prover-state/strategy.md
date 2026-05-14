# Cycle 212 Strategy

## Context

- **Cycle 211**: shipped `RKTableau.Equivalent.setoid.{u} (s : ℕ) : Setoid (RKTableau s)` (P1, fixed-stage setoid, axiom-clean), 2 non-vacuity examples (P2 — `Setoid.refl` + `Quotient.mk` well-formedness), and the thm:382A path scoping issue `.prover-state/issues/thm_382A_path.md` (P3, ~250 LOC of design doc, zero code). Warm rebuild 5.4s. Sorry count: 0.
- **Sorry count**: 0 repo-wide. **No pending Aristotle results.** No new blockers.
- **§441 Phase C.2**: 29th consecutive GPFS timeout (cycles 182–211). Loop-maintainer territory — SKIP local compile attempts per `cycle_182_gpfs_slowness.md`. The cycle 182 draft + cycle 184 namespace fix remain preserved at `.prover-state/cycle_182_draft_section441.lean`.

The cycle 211 worker delivered a thorough path document at `.prover-state/issues/thm_382A_path.md`. It identifies two prerequisite gaps for thm:382A (well-definedness of compose on equivalence classes per Butcher §382):

- **Gap A — Structural bridge `compose_isRKOneStep_iff`**: for sufficiently small `H` and Lipschitz `f`, a single RK step of `M₁.compose M₂` at step size `H` factors as an `M₁`-step followed by an `M₂`-step through an intermediate `y_mid`. Estimated 100-150 LOC, **may span 2 cycles** per the worker's analysis.
- **Gap B — Heterogeneous Σ-typed setoid**: Butcher's `[m₁·m₂]` quotient form lives on `Σ s : ℕ, RKTableau s` quotiented by heterogeneous `Equivalent`. The cycle 211 fixed-stage setoid only handles the homogeneous case.

The cycle 211 worker's task results section "Suggested next approach" gives two options:
1. **Primary**: Begin Gap A (riskier, multi-cycle).
2. **Alternative**: Ship Σ-typed setoid (Gap B partial — "clean ~30 LOC packaging").

**Cycle 212 commits to the Alternative (Σ-typed setoid)**. Rationale:
- Continues the single-cycle axiom-clean discipline of cycles 203-211.
- The Σ-typed setoid is mechanical packaging of cycles 203/204/206's refl/symm/trans, with no novel proof content. Low risk of stalling.
- Gap A's c-scaling investigation is multi-cycle work; rushing it produces stalled drafts (precedent: cycle 138/149 sorry-first rollbacks).
- The Σ-typed setoid unblocks `Quotient (Equivalent.setoidSigma)` for any future heterogeneous-stage quotient reasoning — needed by Butcher's §382 group construction.
- P3 stretch (Gap A code-only scoping subdoc) lets cycle 213 hit the ground running on Gap A with a precise lemma signature already pinned down.

## §0 PHANTOM ALERT (mandatory pre-flight)

Per the standing escalation pattern documented in `.prover-state/issues/phantom_commit_verdict_pattern.md` (9 confirmed false alarms across cycles 8, 35, 73, 170, 176-179, 196), **before treating any "commit-not-reaching-repo" / "stuck on X" verdict at face value, run**:

```bash
git log -1 --format='%H %s'
git show --stat HEAD -- OpenMath/Chapter3/Section381.lean
git rev-parse HEAD ; git rev-parse origin/butcher-experiments
```

If `HEAD == origin/butcher-experiments` and the Section381 diffstat is non-empty for the cited "missing" cycle, the verdict is a false alarm. **DO NOT re-derive already-shipped work in response.**

For cycle 212 specifically: cycle 211's commit `d305d10` is at HEAD. The Setoid instance at line 1906 of `OpenMath/Chapter3/Section381.lean` is in place. If a supervisor verdict says otherwise, it's a phantom.

## §A §441 Phase C.2 — SKIP (30th consecutive GPFS-blocked)

**Do not attempt** `lake env lean OpenMath/Chapter4/Section441.lean` (HEAD or draft). The pathology has reproduced on every attempt across 29 cycles. Loop-maintainer escalation in force.

## §B Priority 1 (P1) — Σ-typed heterogeneous setoid (~30-40 LOC)

**Deliverable**: `RKTableau.Equivalent.setoidSigma.{u} : Setoid (Σ s : ℕ, RKTableau s)` in `OpenMath/Chapter3/Section381.lean`, placed **immediately after** the cycle 211 `Equivalent.setoid.{u}` instance (after line 1908; before `pReduced_equivalent` at line 1924).

**Why this is the right deliverable**:

1. Provides the heterogeneous-stage analog of the cycle 211 fixed-stage setoid. The `Equivalent.{u}` predicate is itself heterogeneous (different `s, s'` indices), so the Σ-typed setoid is the natural ambient type for Butcher's §382 quotient `[m₁ · m₂]`.
2. All three components are axiom-clean and already in the file:
   - `equivalent_self` (cycle 203, line 1795) — homogeneous reflexivity.
   - `Equivalent.symm.{u}` (cycle 204, line 1828) — already heterogeneous.
   - `Equivalent.trans.{u}` (cycle 206, line 1863) — already heterogeneous.
3. The cycle 211 worker noted this is "clean ~30 LOC packaging" with no anticipated proof content beyond structural assembly.
4. Unblocks future thm:382A `[m₁·m₂] = [m̂₁·m̂₂]` form via `Quotient.mk` on the Σ-type once Gap A lands.

**Canonical recipe** (write verbatim, with the `.{u}` annotations from the outset — Risk 1 below explains why):

```lean
/-- *Heterogeneous Σ-typed setoid for `def:381A` `Equivalent`.*
Combines cycles 203 (reflexivity), 204 (symmetry), 206 (transitivity)
into a `Setoid` on `Σ s : ℕ, RKTableau s` — the natural ambient type
for Butcher's §382 quotient `[m₁ · m₂]`, where two methods with
*different* stage counts may live in the same equivalence class.

Companion to the fixed-stage `Equivalent.setoid.{u} s` (cycle 211):
the homogeneous setoid is useful for fixed-stage reasoning, while
this Σ-typed variant is needed for the thm:382A statement
`[m₁ · m₂] = [m̂₁ · m̂₂]` where stage counts of `m₁ · m₂` and
`m̂₁ · m̂₂` may differ (`s₁ + s₂` vs `ŝ₁ + ŝ₂`). See
`.prover-state/issues/thm_382A_path.md` (Gap B) for full context. -/
instance Equivalent.setoidSigma.{u} : Setoid (Σ s : ℕ, RKTableau s) where
  r p q := @Equivalent.{u} p.1 q.1 p.2 q.2
  iseqv :=
    ⟨fun p => @equivalent_self p.1 p.2,
     fun {p q} h => @Equivalent.symm.{u} p.1 q.1 p.2 q.2 h,
     fun {p q r} h₁ h₂ =>
       @Equivalent.trans.{u} p.1 q.1 r.1 p.2 q.2 r.2 h₁ h₂⟩
```

**Expected closure**: ~30 LOC including docstring. Axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

**Verification**:
1. `lake env lean OpenMath/Chapter3/Section381.lean` should compile (warm rebuild ≤10s expected — Section381 has compiled healthy at ~4-10s throughout cycles 184-211).
2. `lean_verify OpenMath.Chapter3.Section312.RKTableau.Equivalent.setoidSigma` should return the standard axiom triple.

## §C Priority 2 (P2) — Non-vacuity witnesses for the Σ-setoid (~15-25 LOC)

**Deliverable**: 2-3 axiom-clean witnesses exercising `Equivalent.setoidSigma` through the `Quotient.mk` API. Place in the `OpenMath.Chapter3.Section381` namespace (after the cycle 211 `Equivalent.setoid` examples at line 2305+, before `paddedEuler_equivalent_pReduced` at line 2313).

**Recipe** — three witnesses of increasing strength:

### W1 — Reflexivity at `paddedEuler` (homogeneous fallback case)

```lean
/-- *Non-vacuity for `Equivalent.setoidSigma`: homogeneous reflexivity.*
The Σ-typed setoid restricted to a fixed `⟨2, paddedEuler⟩` reproduces
the cycle 203 reflexivity witness. Confirms the setoid resolves
typeclass lookup on a Σ-packaged input. -/
example : @Setoid.r _ RKTableau.Equivalent.setoidSigma
    ⟨2, paddedEuler⟩ ⟨2, paddedEuler⟩ := by
  show paddedEuler.Equivalent paddedEuler
  exact paddedEuler.equivalent_self
```

### W2 — Heterogeneous-stage equivalence via cycle 207's `PReducesTo.toEquivalent`

```lean
/-- *Non-vacuity for `Equivalent.setoidSigma`: heterogeneous-stage
equivalence.* The Σ-typed setoid genuinely identifies methods at
*different* stage counts: `⟨2, paddedEuler⟩ ≈ ⟨1, paddedEuler.pReduced pairPartition⟩`
via cycle 208's `paddedEuler_equivalent_pReduced` (which routes
through cycle 207's `PReducesTo.toEquivalent` on cycle 186's
non-trivial 2 ↦ 1 P-reduction). Exercises the Σ-setoid in the
**actually-relevant heterogeneous case** that motivates its
existence. -/
example : @Setoid.r _ RKTableau.Equivalent.setoidSigma
    ⟨2, paddedEuler⟩ ⟨1, paddedEuler.pReduced pairPartition⟩ := by
  show paddedEuler.Equivalent (paddedEuler.pReduced pairPartition)
  exact paddedEuler_equivalent_pReduced
```

### W3 — `Quotient.mk` well-formedness at heterogeneous stages

```lean
/-- *Non-vacuity for `Equivalent.setoidSigma`: `Quotient.mk` API on
heterogeneous stages.* Two Σ-packaged tableaux that are
`Equivalent.setoidSigma`-related project to the **same** quotient
class via `Quot.sound`. Exercises the full quotient-formation
pipeline that Butcher's §382 group construction will consume:
takes `paddedEuler_equivalent_pReduced` (cycle 208) and lifts it to
`[⟨2, paddedEuler⟩] = [⟨1, paddedEuler.pReduced pairPartition⟩]` in
the Σ-typed quotient. -/
example :
    @Quotient.mk _ RKTableau.Equivalent.setoidSigma ⟨2, paddedEuler⟩
      = @Quotient.mk _ RKTableau.Equivalent.setoidSigma
        ⟨1, paddedEuler.pReduced pairPartition⟩ :=
  Quot.sound paddedEuler_equivalent_pReduced
```

**Note on W2 / W3**: these are the **payoff witnesses** for the Σ-typed setoid — they confirm it does what the homogeneous-stage setoid cannot (identify methods with different `s` values). W1 alone would be redundant with cycle 211's fixed-stage Setoid.refl example; W2 / W3 are the genuine non-vacuity.

**Total P2 budget**: ≤ 25 LOC across all three witnesses.

**Implicit-lambda trap mitigation** (from cycle 211 discovery, Risk 2 below): each witness uses `show <unfolded form>` before the witness term, bypassing Lean's implicit-lambda introduction on `Setoid.r`'s ∀-shaped unfold.

## §D Priority 3 (P3, STRETCH) — Gap A scoping subdoc (~150-300 lines of markdown, NO Lean code)

**Deliverable**: ONLY IF P1 and P2 both land cleanly with ample cycle budget remaining, create `.prover-state/issues/compose_isRKOneStep_iff_scoping.md`. This is the cycle 211 worker's recommended cycle 212 scoping investigation for Gap A.

**Content**:

1. **Quote the target statement** (from `thm_382A_path.md` §Gap A). Make precise:
   - Forward direction: if `(M₁.compose M₂).IsRKOneStep f y₀ H y_final`, then `∃ y_mid, M₁.IsRKOneStep f y₀ h₁ y_mid ∧ M₂.IsRKOneStep f y_mid h₂ y_final` for appropriate `h₁, h₂` related to `H` (the c-scaling question).
   - Reverse direction: composing one step of `M₁` with one step of `M₂` yields a step of `M₁.compose M₂`.

2. **C-scaling analysis** (the critical question per `thm_382A_path.md` §Gap A):
   - Read `OpenMath/Chapter3/Section381.lean::compose` at line 2422. Top-block c-values are `M₁.c i` (verbatim). Bottom-block c-values are `(∑ⱼ M₁.bⱼ) + M₂.cᵢ`.
   - Under `M₁.IsPreconsistent` (textbook standard), `∑ⱼ M₁.bⱼ = 1`. So bottom-block becomes `1 + M₂.cᵢ`.
   - **The question**: does a single compose step at size `H` represent (a) two sequential steps at size `h = H/2`, or (b) two sequential steps at size `h = H` (so `H = 2h`)? Resolve this by checking the textbook §382 definition (equation 382a, p. 285).
   - Once resolved, document the **precise step-size relationship** in the scoping doc.

3. **Proposed lemma signature** (write the Lean signature, NOT the body):

```lean
/-- *Compose factors through `M₁`-then-`M₂` on Lipschitz fields at
small step sizes.* For step size `H` small enough (precise threshold
TBD via the cycle 213+ proof), and `f` Lipschitz, every one-step
output of `M₁.compose M₂` factors through an intermediate point that
is a one-step output of `M₁`, with the final point a one-step output
of `M₂` from that intermediate. Conversely, composing sequential
`M₁`/`M₂` one-step outputs yields a one-step output of the composite.
This is the structural bridge needed for thm:382A (well-definedness
of `[·]` on equivalence classes per Butcher §382). -/
theorem compose_isRKOneStep_iff {s₁ s₂ : ℕ}
    (M₁ : RKTableau s₁) (M₂ : RKTableau s₂)
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [CompleteSpace N]
    (f : N → N) (L : NNReal) (hL : LipschitzWith L f) (y₀ : N) :
    ∃ H₀ > (0 : ℝ),
      ∀ H : ℝ, 0 < H → H ≤ H₀ → ∀ y_final : N,
        (M₁.compose M₂).IsRKOneStep f y₀ H y_final ↔
          ∃ y_mid : N,
            M₁.IsRKOneStep f y₀ H y_mid ∧
            M₂.IsRKOneStep f y_mid H y_final
```
(adjust the `H` ↔ `h` ↔ `H/2` scaling per the c-scaling resolution above; the worker can leave the precise relationship as an open question in the scoping doc if step 2 doesn't fully resolve it).

4. **Proof sketch** (markdown text, not Lean):
   - **Forward (compose → M₁-then-M₂)**: unfold compose's stage system; the top-block stages (indices `0..s₁-1`) satisfy `M₁`'s stage equation verbatim, so they form an `M₁` stage tuple. Use `IsRKOneStep_exists` (cycle 205) on `M₁` to confirm this is an `M₁` one-step output, calling the result `y_mid`. Then bottom-block stages satisfy `M₂`'s stage equation with `y_mid` as the initial value (because bottom-left block = `M₁.b j`, which makes the bottom row's `Σⱼ M₁.bⱼ • f(top-stage)` exactly the `M₁`-output formula).
   - **Reverse (M₁-then-M₂ → compose)**: given `M₁` stages `Y₁` and `M₂` stages `Y₂`, assemble a compose stage tuple via `Fin.append Y₁ Y₂` and verify the compose stage equation block-by-block (using cycle 209's `compose_A_*` simp lemmas).

5. **LOC estimate breakdown**:
   - Stage-block lemmas (`Fin.append`-shaped Σ manipulation): ~40 LOC.
   - Forward direction (unfold + extract `y_mid` + assemble `M₁`/`M₂` witnesses): ~50 LOC.
   - Reverse direction (assemble compose stage + output): ~40 LOC.
   - Threshold construction + housekeeping: ~20 LOC.
   - Total: ~150 LOC ± 30. **Possibly multi-cycle**.

6. **Cross-references** to cycle 205 (`IsRKOneStep_exists`), cycle 209 (`compose_A_topLeft` / `topRight` / `botLeft` / `botRight`), cycle 207's stage-equation manipulation patterns in `pReduced_equivalent` and `zeroReduced_equivalent`.

7. **Recommended cycle 213 entry point**: write the precise theorem statement in Lean (no body), then attempt the stage-block lemmas first as named sub-helpers (decomposition discipline per cycles 040 / 113 / 119 / 122).

**Do NOT** attempt any Lean code in P3. **Scoping document only**.

## Risk register

### Risk 1 — Universe-polymorphism with Σ-types

The cycle 204 / 211 discovery: `Equivalent.{u}` is universe-polymorphic; consumers that produce or consume two `Equivalent` instances must use explicit shared `.{u}` annotations. With Σ-types, the dependent-pair projection adds another layer where Lean may pick fresh universe variables for the inner `RKTableau` references.

**Mitigation (write the recipe in §B verbatim)**: the canonical recipe uses explicit `.{u}` on the instance head AND `@equivalent_self`, `@Equivalent.symm.{u}`, `@Equivalent.trans.{u}` in the `iseqv` fields with the Σ-projections `.1` and `.2` written out explicitly. This pins every universe occurrence to the shared `u`.

**Fallback 1** — if the canonical recipe fails with "universe metavariable" error, switch to `Setoid.mk` form with explicit `fun p => ...` lambdas:

```lean
instance Equivalent.setoidSigma.{u} : Setoid (Σ s : ℕ, RKTableau s) :=
  ⟨fun p q => @Equivalent.{u} p.1 q.1 p.2 q.2,
    ⟨fun p => @equivalent_self.{u} p.1 p.2,
     fun {p q} h => @Equivalent.symm.{u} p.1 q.1 p.2 q.2 h,
     fun {p q r} h₁ h₂ =>
       @Equivalent.trans.{u} p.1 q.1 r.1 p.2 q.2 r.2 h₁ h₂⟩⟩
```

The explicit lambdas force Lean to elaborate the universe at each call.

**Fallback 2** — if both still fail, try the `(p : Σ s, RKTableau s)` destructuring form:

```lean
instance Equivalent.setoidSigma.{u} : Setoid (Σ s : ℕ, RKTableau s) where
  r := fun ⟨s₁, M₁⟩ ⟨s₂, M₂⟩ => @Equivalent.{u} s₁ s₂ M₁ M₂
  iseqv := ⟨
    fun ⟨s, M⟩ => @equivalent_self.{u} s M,
    fun {⟨s₁, M₁⟩ ⟨s₂, M₂⟩} h => @Equivalent.symm.{u} s₁ s₂ M₁ M₂ h,
    fun {⟨s₁, M₁⟩ ⟨s₂, M₂⟩ ⟨s₃, M₃⟩} h₁ h₂ =>
      @Equivalent.trans.{u} s₁ s₂ s₃ M₁ M₂ M₃ h₁ h₂⟩
```

Note: Lean's anonymous-pattern syntax inside `fun {⟨..⟩} h => ...` for *implicit* binders may not work directly; if so, drop to the previous fallback's `.1 / .2` form.

If all three fallbacks fail (improbable — the structural identity is verbatim cycle 211's recipe lifted to Σ-types), **stop** and write a `.prover-state/issues/setoidSigma_universe_blocker.md` documenting the failure mode. Do NOT attempt to refactor `Equivalent.{u}` or its components.

### Risk 2 — Implicit-lambda trap in P2 examples

Cycle 211's W2-analog stalled because `Setoid.r` unfolds to `Equivalent`, which is `∀`-shaped (`∀ {N} [...] (f : N → N) ...`), and Lean's implicit-lambda feature auto-introduces those binders on the **goal**, leaving Lean unable to unify the witness term `paddedEuler.equivalent_self` (which has type `paddedEuler.Equivalent paddedEuler` at the bare `Equivalent` level).

**Mitigation (write all P2 examples with `show <bare predicate>`)**: each witness in §C uses the pattern:

```lean
example : @Setoid.r _ RKTableau.Equivalent.setoidSigma <args> := by
  show <bare Equivalent application>
  exact <cycle 203/207/208 witness>
```

The `show` reframes the goal at the raw `Equivalent` level BEFORE the implicit-lambda feature kicks in. **DO NOT** use `(Setoid.refl _)` or `(.symm h)` as a direct term — the goal-side ∀-introduction will block typeclass unification (verified failure mode in cycle 211).

### Risk 3 — `Quot.sound` for the W3 witness

`Quot.sound : ∀ {α : Sort u} {r : α → α → Prop}, r a b → Quot.mk r a = Quot.mk r b` lifts a relation witness into a `Quotient.mk` equality. With `r := (Equivalent.setoidSigma).r`, this should fire cleanly because `Quotient` over a `Setoid` is just `Quot` over the setoid's relation.

**Mitigation**: if `Quot.sound paddedEuler_equivalent_pReduced` fails on relation mismatch (Lean expecting `(Equivalent.setoidSigma).r` but receiving raw `Equivalent`), bridge with:

```lean
example : @Quotient.mk _ RKTableau.Equivalent.setoidSigma ⟨2, paddedEuler⟩
        = @Quotient.mk _ RKTableau.Equivalent.setoidSigma
          ⟨1, paddedEuler.pReduced pairPartition⟩ := by
  apply Quotient.sound
  show paddedEuler.Equivalent (paddedEuler.pReduced pairPartition)
  exact paddedEuler_equivalent_pReduced
```

`Quotient.sound` is the setoid-flavoured wrapper around `Quot.sound`; it expects `Setoid.r`-shape input, which `show` then reframes to raw `Equivalent`.

### Risk 4 — Section381 cold-cache rebuild

If a fresh shell is started, the initial compile may take 1m20s (cold mathlib olean fetch). Warm rebuilds after the cycle 211 commit should be ≤10s. **Mitigation**: budget for one cold compile up front, then all subsequent edits should incrementally recompile fast.

### Risk 5 — GPFS regression in Section381

Section381 has been compiling healthy for 28 cycles (since the cycle 184 GPFS recovery). If a cold compile times out at 5min for Section381 specifically, this is a regression worth flagging — but **do not** stop the cycle. Continue with the Σ-setoid work; the changes are small enough that incremental compile after the initial cold load will be fast.

## What NOT to try

1. **DO NOT attempt Gap A (`compose_isRKOneStep_iff` proof body) this cycle.** The cycle 211 worker explicitly flagged it as multi-cycle (100-150 LOC, possibly 2 cycles). Rushing it produces stalled drafts; precedent: cycle 138 / 149 / 200 sorry-first rollbacks.

2. **DO NOT attempt `compose_assoc`** — cycle 210 confirmed HEq plumbing exceeds the 30-LOC budget. See `.prover-state/issues/compose_assoc_HEq_plumbing.md`. The cycle 210 worker recommended Option D (defer to thm:382A direct closure via quotient encoding), which is precisely what cycle 212's Σ-setoid + future cycle 213+ Gap A is building toward.

3. **DO NOT attempt thm:382A directly this cycle.** It requires Gap A to even state the proof. Cycles 212-214 are scoped as: 212 = Σ-setoid (Gap B partial); 213 = Gap A (structural bridge); 214 = thm:382A direct via the (382g) form.

4. **DO NOT submit anything to Aristotle this cycle.** The Σ-setoid is structural typeclass packaging that Aristotle handles poorly (universe-polymorphic relation + dependent-pair shape); manual closure is faster and more reliable. Aristotle's track record on `Equivalent.{u}`-flavoured work in cycles 203-211: zero successful submissions, manual closure won every time.

5. **DO NOT raise `maxHeartbeats`** above 200000. The Σ-setoid instance + 3 non-vacuity examples should compile within default limits trivially (pure definitional packaging).

6. **DO NOT introduce `axiom`/`constant`** declarations. All three components (refl, symm, trans) are axiom-clean theorems already in the file.

7. **DO NOT modify `equivalent_self` / `Equivalent.symm` / `Equivalent.trans`** themselves — they are stable axiom-clean since cycles 203/204/206. The Σ-setoid instance consumes them as-is.

8. **DO NOT attempt the §441 Phase C.2 smoke test** — 29 consecutive GPFS timeouts establish this is not transient. Skip per `cycle_182_gpfs_slowness.md`.

9. **DO NOT ship P3 if P1/P2 don't land cleanly** — P3 is strict stretch. A cycle that delivers only P1 (axiom-clean Σ-setoid instance) is a successful cycle on its own.

10. **DO NOT use `≈` notation in the P2 examples.** `≈` requires a single ambient `Setoid` instance to be active; with both `Equivalent.setoid` and `Equivalent.setoidSigma` in scope, Lean cannot disambiguate. Use the explicit `@Setoid.r _ RKTableau.Equivalent.setoidSigma <args>` form throughout P2 (per Risk 2 cycle 211 precedent).

11. **DO NOT cherry-pick a different "easier" target** like `def:451A` or `def:422B`. P1 is genuinely useful infrastructure for the §382 group track we've been building since cycle 203 (10 consecutive cycles of §380 work). Pivoting away mid-track wastes the momentum.

12. **DO NOT scope-creep P3 into a Lean code attempt.** It is **markdown only** — a scoping subdoc with precise lemma signatures and proof sketches. The cycle 211 worker's `.prover-state/issues/thm_382A_path.md` is the model: 250 lines of design doc, zero code.

13. **DO NOT remove or modify** the cycle 211 `Equivalent.setoid.{u} (s : ℕ)` instance or its two non-vacuity examples. The Σ-typed variant is a **companion**, not a replacement. Cycle 211's homogeneous-stage setoid remains the natural choice for fixed-stage reasoning.

## Workflow

1. **Pre-flight (≤3 min)**:
   - Run §0 PHANTOM ALERT git verification commands. Confirm `d305d10` at HEAD.
   - Verify `lake env lean OpenMath/Chapter3/Section381.lean` compiles clean at HEAD (should be ≤10s warm).

2. **P1 implementation (~10 min)**:
   - Insert the Σ-typed setoid instance at line 1909+ (immediately after the cycle 211 fixed-stage setoid, before `pReduced_equivalent` at line 1924).
   - Try the canonical recipe first (§B). If universe error, apply Risk 1 mitigations in order: Fallback 1 (`Setoid.mk` form with `fun p => ...`), then Fallback 2 (destructured-pattern form), then issue file.
   - Save and recompile.

3. **P1 verification (~3 min)**:
   - Recompile via `lake env lean OpenMath/Chapter3/Section381.lean`.
   - Run `lean_verify OpenMath.Chapter3.Section312.RKTableau.Equivalent.setoidSigma` (or use `#print axioms` in a standalone test file).
   - Expected: `[propext, Classical.choice, Quot.sound]`.

4. **P2 implementation (~10 min)**:
   - Add the three witnesses W1, W2, W3 in the `OpenMath.Chapter3.Section381` namespace, after the cycle 211 `Equivalent.setoid` examples (at line 2305+), before `paddedEuler_equivalent_pReduced` (line 2313). Or alternatively, after `paddedEuler_equivalent_pReduced` — the precise placement doesn't matter as long as W2 / W3 come after their dependency `paddedEuler_equivalent_pReduced`.
   - Use `show <bare Equivalent>` per Risk 2 in every witness.
   - For W3, use `Quot.sound` (or `Quotient.sound` per Risk 3 fallback).

5. **P2 verification (~3 min)**:
   - Recompile.
   - Spot-check all three witnesses elaborate without error. They are `example`s (no axiom signatures), but they do exercise the typeclass — a failure would surface as a compile error.

6. **P3 (if budget allows, ~20-40 min)**:
   - Write `.prover-state/issues/compose_isRKOneStep_iff_scoping.md` with the seven sections outlined in §D above.
   - Cross-reference cycle 209 simp lemmas (`compose_A_topLeft`, `topRight`, `botLeft`, `botRight`, `compose_b_castAdd`, `b_natAdd`, `c_castAdd`, `c_natAdd`), cycle 205 (`IsRKOneStep_exists`), and cycle 207's `pReduced_equivalent` / `zeroReduced_equivalent` for stage-equation manipulation patterns.
   - Pure markdown. No Lean code.

7. **Faithfulness check (~3 min)**:
   - `Equivalent.setoidSigma`: instance, not a textbook entity. No textbook divergence; pure Lean infrastructure aligning with Mathlib idioms.
   - W1, W2, W3: not named theorems, no faithfulness check needed.
   - Tautology check on the setoid: `iseqv := ⟨...⟩` is structural packaging, NOT a tautology — components do real work (cycles 203/204/206 axiom-clean proofs).

8. **Write task results** to `.prover-state/task_results/cycle_212.md` per CLAUDE.md format.

9. **Update `plan.md` and `lean_status.json`**: No status changes expected this cycle (def:381A row stays as cycle 211's state; thm:382A remains `unformalized`). Optionally add a one-line cycle 212 note to the def:381A row of `plan.md` mentioning the Σ-typed setoid + P3 scoping doc.

10. **Commit and push** with format consistent with cycles 207/208/210/211.

## Cycle budget

- P1: ~15 minutes of work, ~30-40 LOC, axiom-clean expected.
- P2: ~15 minutes of work, ~15-25 LOC, axiom-clean expected (3 examples).
- P3 (stretch): ~30-40 minutes of writing, ~150-300 lines of markdown, no code.
- Total: well within a single cycle. No risk of overrun.

## Why this strategy is right

- **Aligned with the cycle 211 worker's explicit recommendation** (their "Alternative" was the Σ-typed setoid; primary was Gap A but they flagged it as multi-cycle).
- **Continues the §380 group-theoretic infrastructure track** built across cycles 203-211 (Equivalent refl/symm/trans, IsRKOneStep_exists, compose, IsExplicit, compose_isExplicit_iff, Equivalent.setoid, thm:382A path doc) — 10 consecutive cycles of consistent thematic progress.
- **Bounded LOC** — P1+P2 well under the 30-LOC body soft-cap that has produced reliable cycles. P3 is markdown only.
- **Axiom-clean expected** — pure typeclass packaging of three axiom-clean predecessors.
- **Enables thm:382A roadmap concretely** — Σ-typed setoid is the natural ambient type for the `[m₁·m₂]` quotient form. Cycle 213+ can pivot to Gap A's structural bridge with the scoping doc already written.
- **No GPFS exposure** — Section381 compiled healthy at ~4-10s throughout cycles 184-211 (28 cycles of stable health).
- **Low risk** — explicit fallbacks for the only nontrivial elaboration concern (universe polymorphism with Σ-types, Risk 1). Risks 2-5 are well-understood from cycle 211 precedent.
- **Single substantive deliverable per cycle** — matches the observed pattern of successful cycles (203/204/206/207/208/210/211 all shipped one focused axiom-clean deliverable with optional stretch).
- **P3 scoping doc pre-positions cycle 213** — the structural bridge `compose_isRKOneStep_iff` is the genuinely hard prerequisite for thm:382A. Writing a precise lemma signature + proof sketch this cycle means cycle 213's worker can start implementing immediately, with the c-scaling question pre-investigated.
