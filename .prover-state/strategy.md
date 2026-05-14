# Cycle 213 Strategy — §382 `compose_of_isRKOneStep` (Gap A reverse direction)

## §A. Standing state (read first)

- **Sorry count: 0** across the repo. HEAD is `bf4c80c` (cycle 212).
- **Cycle 212 shipped Gap B**: `Equivalent.setoidSigma.{u}` + 3 non-vacuity witnesses + ~280-line scoping doc `.prover-state/issues/compose_isRKOneStep_iff_scoping.md` for Gap A.
- **§441 Phase C.2 is GPFS-blocked**: 30 consecutive timeouts (cycles 182–212). **DO NOT attempt** a Section441 compile this cycle. The standing escalation in `cycle_182_gpfs_slowness.md` is unchanged — loop-maintainer territory.
- **Cycle 212 worker's "Suggested next approach"** is explicit and well-scoped: ship the **reverse direction** of `compose_isRKOneStep_iff` this cycle (cycle 213), then ship forward direction next cycle (214), then thm:382A in cycle 215 via the (382g) reformulation.

## §B. What to work on this cycle

### P1 (primary, ~40 LOC) — `RKTableau.compose_of_isRKOneStep`

**Target statement** (from scoping doc §3):

```lean
/-- *Reverse direction of `compose_isRKOneStep_iff` (algebraic, no
smallness).* Sequential `M₁`/`M₂` one-step outputs at step size `H`
assemble into a one-step output of `M₁.compose M₂` at the same `H`. -/
theorem compose_of_isRKOneStep {s₁ s₂ : ℕ}
    (M₁ : RKTableau s₁) (M₂ : RKTableau s₂)
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    {f : N → N} {y₀ : N} {H : ℝ} {y_mid y_final : N}
    (h₁ : M₁.IsRKOneStep f y₀ H y_mid)
    (h₂ : M₂.IsRKOneStep f y_mid H y_final) :
    (M₁.compose M₂).IsRKOneStep f y₀ H y_final
```

Place it in `OpenMath/Chapter3/Section381.lean` **immediately after `compose_isExplicit_iff`** (cycle 210, around line ~2570). This keeps the `compose`-cluster geographically tight.

### P2 (optional, ~5 LOC) — Sorry-first scaffold for the full iff

**Decision (default = SKIP)**: do NOT ship a sorry'd `compose_isRKOneStep_iff` scaffold this cycle. Going from sorry=0 to sorry=1 attracts supervisor scrutiny (cycle 200 was scored −2 for raising sorry 0→3). The reverse direction `compose_of_isRKOneStep` is itself a complete axiom-clean theorem; the iff packaging can land in cycle 214 alongside the forward direction in one clean ship.

Override and ship P2 only if P1 closes in well under the time budget AND you can articulate in the task results why a 0→1 sorry bump is worth it this cycle.

### P3 (stretch, ≤10 min) — `Fin.append` lemma audit for cycle 214

After P1 closes, spend ≤10 minutes verifying the exact Mathlib lemma names for `Fin.append`-related sum splitting. This directly de-risks cycle 214's forward direction (which needs the same machinery on the composite stage tuple).

Use `lean_local_search`, `lean_loogle`, or grep on `.lake/packages/mathlib/Mathlib/Data/Fin/Tuple/`. Candidates to check (in order of usefulness):

- `Fin.sum_univ_castAdd` / `Fin.sum_univ_natAdd` — for `∑ i : Fin (s₁ + s₂), …` split.
- `Fin.append_left` / `Fin.append_right` / `Fin.append_castAdd` / `Fin.append_natAdd` — for evaluating `Fin.append a b (castAdd s₂ i₁) = a i₁` etc.
- `Fin.sum_append` — likely does NOT exist as named; report finding.
- `Finset.sum_sigma`-style alternatives.

Record findings as a brief checklist in the cycle 213 task results under §Discovery.

## §C. Proof recipe for `compose_of_isRKOneStep` (~40 LOC)

The scoping doc §4.1 has the full sketch. Distilling:

**Step 1 — unpack hypotheses**:
```lean
obtain ⟨Y₁, hY₁_stage, hY₁_out⟩ := h₁
obtain ⟨Y₂, hY₂_stage, hY₂_out⟩ := h₂
```

(Verify the constructor field names by reading `IsRKOneStep` at `Section381.lean:923-928` — they may be `Y`, `stage`, `out` or named differently. Adjust the destructor accordingly.)

**Step 2 — define composite stage tuple**:
```lean
refine ⟨Fin.append Y₁ Y₂, ?_, ?_⟩
```

This produces two goals: stage equation and output equation.

**Step 3 — stage equation** (for all `i : Fin (s₁ + s₂)`):

Goal shape: `Fin.append Y₁ Y₂ i = y₀ + H • ∑ j, (M₁.compose M₂).A i j • f ((Fin.append Y₁ Y₂) j)`.

Case-split via `induction i using Fin.addCases` (or `Fin.addCases i`):

- **Top block** (`i = Fin.castAdd s₂ i₁`):
  - LHS: `Fin.append Y₁ Y₂ (castAdd s₂ i₁) = Y₁ i₁` via `Fin.append_left` (verify name with `lean_local_search`).
  - RHS sum splits into top-left + top-right halves. Cycle 209's `compose_A_topLeft` gives `(M₁.compose M₂).A (castAdd s₂ i₁) (castAdd s₂ j₁) = M₁.A i₁ j₁`; `compose_A_topRight = 0` makes top-right vanish.
  - Close with `hY₁_stage i₁`.

- **Bottom block** (`i = Fin.natAdd s₁ i₂`):
  - LHS: `Fin.append Y₁ Y₂ (natAdd s₁ i₂) = Y₂ i₂` via `Fin.append_right`.
  - RHS sum splits: cycle 209's `compose_A_botLeft = M₁.b j₁` and `compose_A_botRight = M₂.A i₂ j₂`.
  - Bot-left sum = `(y_mid - y₀) / H` via `hY₁_out`; bot-right sum = `(Y₂ i₂ - y_mid) / H` via `hY₂_stage i₂`.
  - Combine: `y₀ + H • (bot-left + bot-right) = y₀ + (y_mid - y₀) + (Y₂ i₂ - y_mid) = Y₂ i₂`. Close with `linear_combination` or explicit `ring`-style chain over `•`.

**Step 4 — output equation**:

Goal: `y_final = y₀ + H • ∑ i, (M₁.compose M₂).b i • f ((Fin.append Y₁ Y₂) i)`.

The composite `.b` field unfolds to `Fin.append M₁.b M₂.b` (cycle 209 — check via `compose_b_castAdd` / `compose_b_natAdd` simp lemmas, or unfold `RKTableau.compose` directly).

Split the sum into top + bottom via the `Fin.append`-sum lemma from P3 audit. Resulting:
```
y₀ + H • (∑ᵢ₁ M₁.b i₁ • f (Y₁ i₁) + ∑ᵢ₂ M₂.b i₂ • f (Y₂ i₂))
  = (y₀ + H • ∑ᵢ₁ M₁.b i₁ • f (Y₁ i₁)) + H • ∑ᵢ₂ M₂.b i₂ • f (Y₂ i₂)
  = y_mid + H • ∑ᵢ₂ M₂.b i₂ • f (Y₂ i₂)           -- by hY₁_out
  = y_final                                        -- by hY₂_out
```

Close with `rw [← hY₁_out]; exact hY₂_out.symm` (modulo `simp` plumbing to align the sum-split with the closed-forms).

## §D. Known risks (preemptive guidance)

### Risk 1 — `Fin.sum_univ_addCases` may not be its exact name

The Mathlib name could be `Fin.sum_univ_add`, `Fin.sum_univ_castAdd_add_natAdd`, or live as a `Finset.sum_sigma`-flavored variant. Likely candidates (try in order):

1. `Fin.sum_univ_add` — most plausible idiomatic name.
2. `Fin.sum_univ_castSucc` — wrong shape (handles `Fin (n+1)`, not `Fin (a+b)`); listed only to rule out.
3. Manual: `Fin.sum_univ_eq_sum_range` + index reindex — heavyweight fallback.

If all named lookups miss, fall back to **proving the split manually** as a private helper:
```lean
private theorem Fin.sum_univ_addCases {s₁ s₂ : ℕ} {α : Type*} [AddCommMonoid α]
    (g : Fin (s₁ + s₂) → α) :
    ∑ i, g i = (∑ i₁ : Fin s₁, g (Fin.castAdd s₂ i₁))
             + (∑ i₂ : Fin s₂, g (Fin.natAdd s₁ i₂)) := by
  sorry  -- ≤10 LOC via Finset.sum_disjoint + Finset.image_disjoint
```

If you have to ship this helper, mark it `private` and keep it in `Section381.lean` (do not start a new helper file mid-cycle).

### Risk 2 — `Fin.append` evaluation

`Fin.append Y₁ Y₂ (Fin.castAdd s₂ i₁)` should rewrite to `Y₁ i₁`. The Mathlib name to try first is `Fin.append_left`; alternatives: `Fin.append_castAdd`, `Fin.addCases_castAdd`. If all miss, `unfold Fin.append; simp` is the hammer fallback.

### Risk 3 — composite `.b` field unfolding

`(M₁.compose M₂).b = Fin.append M₁.b M₂.b` is *likely* `rfl` (compose is defined as a structure constructor in cycle 209), so a simple `rfl` rewrite or `show` reframing should work. If it doesn't, use the cycle 209 simp lemmas `compose_b_castAdd` / `compose_b_natAdd` (verify names by grepping Section381.lean).

### Risk 4 — `•` arithmetic vs `*` and `ring`

The `IsRKOneStep` definition uses `•` (SMul ℝ N), not `*`. At concrete `N = ℝ` this collapses to `*`, but the proof should work uniformly. **Use `linear_combination` over `smul_add` / `add_smul` / `smul_smul` rather than `ring`** — `ring` will fail on `H • x` goals because `•` is not a ring operation. If `linear_combination` doesn't fire, manually distribute `•` via the `smul_*` simp set and close residues with `module` or `noncomm_ring` tactics.

### Risk 5 — `IsRKOneStep` field names

Read the actual `IsRKOneStep` definition at `Section381.lean:923` before writing `obtain ⟨Y₁, hY₁_stage, hY₁_out⟩`. The field names may be different (e.g., `stages`, `stage_eq`, `output_eq`). Match exactly.

## §E. What NOT to try

- **Do NOT attempt the forward direction** of `compose_isRKOneStep_iff` this cycle. The scoping doc estimates ~70 LOC for the forward direction (requires cycle 205's `IsRKOneStep_exists` + cycle 204's `RKStageMap_fixedPoint_unique` + smallness threshold construction). Combining with the ~40 LOC reverse exceeds a single-cycle budget. Defer to cycle 214 per scoping doc §7.

- **Do NOT attempt Section441 Phase C.2** (Möbius bridge / αPoly complex roots). GPFS-blocked 30 consecutive cycles. The cycle 182 draft and cycle 184 namespace fix are preserved; resume only when GPFS recovers.

- **Do NOT attempt `compose_assoc`** (cycle 210 deferred, see `.prover-state/issues/compose_assoc_HEq_plumbing.md`). The HEq plumbing exceeds 30 LOC and is orthogonal to thm:382A's path (which uses the (382g) reformulation, not `compose_assoc`).

- **Do NOT add a Σ-typed `compose_assoc_at_setoid` reformulation**. The cycle 212 Σ-typed setoid was scoped for `[m₁ · m₂]` quotient classes, not associativity. Stay on the cycle 212 worker's recommended path.

- **Do NOT bump `maxHeartbeats`** above 200000. If the stage-equation case split blows up, decompose into named private helpers (one per block: `compose_stage_top_eq`, `compose_stage_bot_eq`).

- **Do NOT introduce `axiom`/`constant`** for any step. The reverse direction is purely algebraic — every step has a Mathlib name or a ≤10-LOC helper proof.

- **Do NOT use `ring` on `•` goals**. Use `linear_combination` or `smul_*` simp set + `module`.

- **Do NOT poll Aristotle for general-n thm:550A** (project `2c4630b2` cancelled cycle 151; do not re-submit).

### Failed-approach inventory from prior cycles (do not re-attempt)

- **Cycle 210's `compose_assoc` attempts**: `congr 1` peels wrong layer; `subst hs` fails (Nat.add_assoc is not a free variable); `simp [compose]; rfl` produces syntactically-distinct `Fin.addCases` nestings. See `compose_assoc_HEq_plumbing.md`.

- **Cycle 208's `.symm` dot-notation pitfall**: `Equivalent` is a `∀`-form `def`, not a structure — `Function.symm` is what gets resolved. Use `Equivalent.symm` explicitly. (Not relevant this cycle but informs naming conventions.)

- **Cycle 211's implicit-lambda trap on `Setoid.r` unfolds**: `show paddedEuler.Equivalent <target>` is the workaround. (Not relevant this cycle — `compose_of_isRKOneStep` has no Setoid in its statement.)

- **Cycle 204's universe-polymorphism pitfall**: `Equivalent.{u}` requires explicit shared `.{u}` annotation when both hypothesis and goal mention it. Not relevant this cycle — `compose_of_isRKOneStep` does NOT mention `Equivalent` in its statement (it operates at the `IsRKOneStep` level, one layer below).

## §F. Verification checklist (run before commit)

1. `lake env lean OpenMath/Chapter3/Section381.lean` exits 0.
2. `grep -c sorry OpenMath/Chapter3/Section381.lean` returns 0 (or 1 if P2 scaffold shipped — should be 0 by default).
3. `lean_verify OpenMath.Chapter3.Section312.RKTableau.compose_of_isRKOneStep` returns axiom-clean (`[propext, Classical.choice, Quot.sound]` baseline; `Classical.choice` may appear if any Mathlib `Fin.append` lemma uses it internally — that's fine).
4. Cycle 211's `Equivalent.setoid.{u}` and cycle 212's `Equivalent.setoidSigma.{u}` still axiom-clean (regression check via `lean_verify`).
5. No new linter warnings in `Section381.lean` (the existing unused-variable warnings on lines 577 and 2245 are pre-existing — do not "fix" them).
6. Warm rebuild of `Section381.lean` ≤ 10s. If it balloons past 30s warm, investigate — likely a `simp` chain doing more work than it should.

## §G. Faithfulness check

`compose_of_isRKOneStep` is **infrastructure** for thm:382A, not a textbook entity — no `entities/*.json` file to consult. Its conclusion is the algebraic dual of one direction of Butcher §382's implicit identity (that one step of `m₁ · m₂` factors through two sub-steps).

- **Tautology check**: NO. The conclusion `(M₁.compose M₂).IsRKOneStep f y₀ H y_final` is genuinely constructed from `h₁` and `h₂`; neither hypothesis matches the conclusion verbatim.
- **Identity check**: NO. The proof builds a stage tuple via `Fin.append` and discharges two non-trivial obligations.
- **Hypothesis strength**: minimal. No Lipschitz, no smallness, no `CompleteSpace`. The hypotheses are exactly what's algebraically needed.
- **Definition smuggling**: not applicable — no new definitions.
- **Absent theorem**: not applicable — no `sorry`-promised follow-ups.

## §H. Task results template addendum

In the cycle 213 task results, explicitly record:

1. Whether P2 (scaffold sorry) was shipped or skipped, and why.
2. The exact Mathlib lemma names used for `Fin.append` evaluation and `Fin (s₁ + s₂)` sum splitting (these will be needed verbatim in cycle 214's forward direction). Format as: `[name] = [verified-present | not-found | wrong-shape] | [used-as]`.
3. Total LOC of `compose_of_isRKOneStep` body (target ≤ 50 LOC; report actual).
4. Warm rebuild time after cycle 213 edits.
5. Whether any new helper lemmas were extracted (e.g., a `compose_stage_top_eq` / `compose_stage_bot_eq` split if the case-split body got long, or a private `Fin.sum_univ_addCases` helper if Risk 1 fired).
6. P3 stretch findings (Fin.append audit) — formatted as the checklist from item (2) above.

## §I. Bottom line

Ship `compose_of_isRKOneStep` (~40 LOC, axiom-clean, no smallness). Default: skip the iff scaffold sorry (keep sorry count at 0). Audit `Fin.append` lemmas as a P3 stretch to de-risk cycle 214. Target sorry count: **0**.

§441 Phase C.2 GPFS-blocked, skipped (31st consecutive).
