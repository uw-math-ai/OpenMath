# Cycle 206 Strategy — §380 `Equivalent.trans` (option b: side-hypothesis)

## TL;DR

Ship `Equivalent.trans` in `OpenMath/Chapter3/Section381.lean` via
**option (b) — add `[CompleteSpace N]` as a side-hypothesis on the
trans theorem itself**, NOT by strengthening the `Equivalent`
definition. This completes the refl + symm + trans equivalence-
relation triple for `Equivalent` and unblocks cycle 207+ work on
`PReducesTo → Equivalent` (deferred direction (2) of thm:381H).

**Skip §441 Phase C.2 GPFS smoke test (26th consecutive).** Standing
pattern across cycles 182–205; failure mode unchanged (EXIT=124 at
300s, near-zero CPU, no zombies). Loop-maintainer territory.

---

## §A. §441 Phase C.2 — SKIP (26th consecutive cycle)

GPFS pathology on `OpenMath/Chapter4/Section441.lean` has reproduced
on every smoke-test attempt since cycle 182 (25 consecutive 5-min
timeouts at near-zero CPU). Per the standing instructions in
`.prover-state/issues/cycle_182_gpfs_slowness.md`, this is
**loop-maintainer territory** — workers do NOT edit
`scripts/autonomous_loop.py` and do NOT attempt the C.2 closure
until a loop-maintainer signal indicates GPFS recovery.

**Action this cycle**: do not run a Section441 smoke test. Do not
poll for GPFS recovery. Proceed directly to §B.

If `attempts.md` carries a phantom "factor-of-2 still blocking",
"Section441.lean missing from commit", or similar §441-related
verdict, treat as a known stale propagation (per
`.prover-state/issues/phantom_commit_verdict_pattern.md`) and
ignore. Phase B closes at `Section441.lean:913`
(`aPoly_coeff_one_pos_of_stable_preconsistent`, cycle 179); Phase
C.1 lands at `Section441.lean:455+` (cycle 181). **Do not
re-audit any of this.**

---

## §B. Primary deliverable — `Equivalent.trans` via option (b)

### Planner decision: adopt **option (b)** — side-hypothesis variant

Cycle 205's task results flagged this as a planner judgment call.
Per the worker's framing of the three options:

* **(a) Strengthen `Equivalent` definition with `[CompleteSpace N]`.**
  Requires re-verifying cycle 030's `equivalent_explicitEuler_self`,
  cycle 203's `equivalent_self`, cycle 204's `Equivalent.symm` +
  `paddedEuler_equivalent_self` all compile under the extra
  typeclass binder. Multi-cycle risk if a downstream witness
  inadvertently relies on the un-strengthened def.

* **(b) Side-hypothesis on `trans` only.** Add `[CompleteSpace N]`
  to the trans theorem signature. N is determined by the two
  Equivalent hypotheses; typeclass synthesis picks up the
  instance automatically at every call site. **ADOPTED.**

* **(c) Defer trans entirely.** Leaves the equivalence-relation
  closure with refl + symm only. Rejected — coherence of the
  presentation suffers, and the cycle 201–205 Banach infrastructure
  was built specifically to enable this.

### Reasoning for (b)

1. **Zero retroactive cost.** No edits to refl (cycle 203), symm
   (cycle 204), `paddedEuler_equivalent_self` (cycle 204),
   `equivalent_explicitEuler_self` (cycle 030). All four remain
   axiom-clean as currently stated.
2. **Textbook faithful.** Butcher §380 does not impose completeness
   — the textbook works over ℝⁿ where it is automatic. Surfacing it
   as an instance hypothesis on the one consumer that genuinely
   needs it (trans, which invokes Banach existence on the middle
   method) is honest about the implementation-level dependency.
3. **No caller burden in practice.** Every concrete RK method of
   interest lives on ℝ, ℝⁿ, or a finite-dim normed space — all
   trivially `CompleteSpace`. The instance fires automatically at
   every call site.
4. **Universe-polymorphism alignment.** Per cycle 204's discovery,
   `Equivalent.{u_1}` is universe-polymorphic; trans needs an
   explicit shared `.{u}` annotation across both hypotheses and
   the goal. The side-hypothesis approach makes this annotation
   localised to one theorem rather than the def.

### Implementation recipe — `Equivalent.trans`

**Placement**: in `OpenMath/Chapter3/Section381.lean`, namespace
`OpenMath.Chapter3.Section312.RKTableau`, immediately after cycle
204's `Equivalent.symm`.

**Target signature** (skeleton; adjust to match the exact
`Equivalent` def shape after reading the source):

```lean
theorem Equivalent.trans.{u}
    {s : ℕ} {N : Type u} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [CompleteSpace N]
    {M M' M'' : RKTableau s}
    (h₁ : Equivalent.{u} (N := N) M M')
    (h₂ : Equivalent.{u} (N := N) M' M'') :
    Equivalent.{u} (N := N) M M''
```

The explicit `.{u}` annotation on the theorem AND on every
`Equivalent` reference is mandatory — cycle 204's `Equivalent.symm`
hit an "Application type mismatch: N has type Type u_2 but expected
Type u_1" error without it. **Preemptively apply.**

### Step 1 — Read the source before writing tactics

Use the Read tool on `OpenMath/Chapter3/Section381.lean` to locate:

1. The `Equivalent` definition (confirm exact quantifier structure:
   `∃ h₀ > 0, ∀ h, |h| < h₀ → ...` or some variant).
2. `Equivalent.symm` (cycle 204) — mirror its universe-annotation
   pattern.
3. `IsRKOneStep_exists` (cycle 205 P2) — signature and the exact
   smallness hypothesis it consumes.
4. `RKStageMap_contracting` (cycle 202) — confirms the smallness
   threshold is `|h| · L · C < 1` where `C := ∑ᵢⱼ |M.A i j|`.
5. `equivalent_self` (cycle 203) — its threshold construction
   `h₀ := 1/(2*(L*C+1))` is the template for the smallness-bridge
   in trans.

### Step 2 — Bridge the smallness thresholds

This is the only substantive analytical step. Each of M, M', M''
has its own
```
C_X := ∑ᵢⱼ |X.A i j|
```
and `IsRKOneStep_exists` requires `|h| · L · C_X < 1` for the
specific method X on which existence is invoked. For trans, we
invoke existence on M' (the middle).

If `Equivalent`'s definition is universally quantified over h₀
existentially (the likely shape based on cycle 203's
construction), the trans body shape is:

```lean
-- (Adjust intros to match Equivalent's actual quantifier list.)
intro f L hf_lip y₀
obtain ⟨h₀₁, h₀₁_pos, hConcl₁⟩ := h₁ f L hf_lip y₀
obtain ⟨h₀₂, h₀₂_pos, hConcl₂⟩ := h₂ f L hf_lip y₀
-- M' existence threshold:
set C_M' : ℝ := ∑ i, ∑ j, |M'.A i j| with hC_M'_def
have hC_M'_nn : 0 ≤ C_M' := by
  apply Finset.sum_nonneg; intro i _
  apply Finset.sum_nonneg; intro j _
  exact abs_nonneg _
set h₀_M' : ℝ := 1 / (2 * (L * C_M' + 1)) with hh₀_M'_def
have h₀_M'_pos : 0 < h₀_M' := by
  apply one_div_pos.mpr
  nlinarith [(L : ℝ).coe_nonneg]  -- L : NNReal ⇒ (L : ℝ) ≥ 0
refine ⟨min h₀₁ (min h₀₂ h₀_M'), ?_, ?_⟩
· exact lt_min h₀₁_pos (lt_min h₀₂_pos h₀_M'_pos)
intro h hh y₁ y₃ hy₁ hy₃
have hbound_M' : |h| < h₀_M' :=
  lt_of_lt_of_le hh (le_trans (min_le_right _ _) (min_le_right _ _))
have h_small_M' : |h| * L * C_M' < 1 := by
  -- From hbound_M' : |h| < 1/(2*(L*C_M'+1)),
  -- deduce |h| * (2*(L*C_M'+1)) < 1 via le_div_iff₀.
  -- Then nlinarith closes |h|·L·C_M' < 1 (cycle 203 recipe).
  have h2 : 0 < 2 * (L * C_M' + 1) := by nlinarith [(L : ℝ).coe_nonneg]
  rw [lt_div_iff₀ h2] at hbound_M'  -- ⚠ direction may need adjusting
  nlinarith [(L : ℝ).coe_nonneg, abs_nonneg h]
obtain ⟨y₂, hy₂⟩ := M'.IsRKOneStep_exists hf_lip y₀ h_small_M'
have hbound₁ : |h| < h₀₁ := lt_of_lt_of_le hh (min_le_left _ _)
have hbound₂ : |h| < h₀₂ :=
  lt_of_lt_of_le hh (le_trans (min_le_right _ _) (min_le_left _ _))
calc y₁ = y₂ := hConcl₁ h hbound₁ y₁ y₂ hy₁ hy₂
  _   = y₃ := hConcl₂ h hbound₂ y₂ y₃ hy₂ hy₃
```

⚠ This skeleton is a planner sketch — the *exact* shape (intros,
existential/universal quantifier order, smallness-hypothesis
direction in `IsRKOneStep_exists`) depends on cycle 205's literal
signature and on the `Equivalent` def. **Read the source first.**

### Step 3 — Verify axiom-clean

Use:
```
lean_verify OpenMath.Chapter3.Section312.RKTableau.Equivalent.trans
```
Expected: `[propext, Classical.choice, Quot.sound]` (the standard
trio). If the proof is fully constructive after `obtain`/`refine`
resolution, `Classical.choice` may be absent — that's also fine.

### LOC budget

~30 LOC including docstring. Body proper ~20 LOC after the
smallness-bridge derivation. **If your draft exceeds 50 LOC, stop
and reconsider** — there is likely a cleaner threshold construction
you are missing. Cycle 203's `equivalent_self` body is the
canonical reference for the threshold algebra.

### Aristotle suitability

**Low.** This is careful threshold-bookkeeping with universe-
annotation requirements and a specific Banach-existence call site.
Manual closure is faster than prompting Aristotle through the
.{u} / `IsRKOneStep_exists` / `min` plumbing. **Do not submit.**

---

## §C. Stretch deliverable (only if §B closes with margin)

### `paddedEuler` non-vacuity for `IsRKOneStep_exists` (~5 LOC)

Cycle 205 §D flagged this as a low-priority sanity check. ~5 LOC
specialisation, e.g.:

```lean
example (y₀ : ℝ) (h : ℝ)
    (h_small : |h| * (1 : ℝ) *
      (∑ i, ∑ j, |paddedEuler.A i j|) < 1) :
    ∃ y₁, paddedEuler.IsRKOneStep id y₀ h y₁ :=
  paddedEuler.IsRKOneStep_exists LipschitzWith.id y₀ h_small
```

Confirms the cycle 205 existence helper fires non-vacuously on a
concrete tableau over ℝ (where `CompleteSpace ℝ` is automatic).

### Trivial trans corollary at `paddedEuler`

If both §B and the above land, add:

```lean
theorem paddedEuler_equivalent_self_trans
    (h₁ : paddedEuler.Equivalent paddedEuler)
    (h₂ : paddedEuler.Equivalent paddedEuler) :
    paddedEuler.Equivalent paddedEuler :=
  h₁.trans h₂
```

Trivially true since trans is total at the same method; the value
is exercising `[CompleteSpace ℝ]` instance synthesis on a concrete
method.

**Only attempt §C if §B closes within ~30 LOC and there is genuine
margin.** Do not let stretch work jeopardise §B.

---

## §D. What NOT to try

1. **DO NOT attempt option (a) (strengthen the `Equivalent` def).**
   The planner has decided: option (b) is adopted. No freelancing
   on the def shape this cycle.

2. **DO NOT modify cycle 203's `equivalent_self`, cycle 204's
   `Equivalent.symm`, `paddedEuler_equivalent_self`,
   `RKStageMap_fixedPoint_unique`, or cycle 205's
   `RKStageMap_fixedPoint_exists`, `IsRKOneStep_exists`.** They
   are axiom-clean and load-bearing. Touching them risks
   regression for zero benefit.

3. **DO NOT skip the explicit `.{u}` universe annotation.** Cycle
   204's `Equivalent.symm` confirmed `Equivalent` is universe-
   polymorphic, and auto-bound universes pick fresh levels per
   reference. Apply the annotation preemptively to every
   `Equivalent` reference in the trans signature AND the goal
   statement.

4. **DO NOT run a Section441 smoke test.** GPFS pathology
   unresolved (25 consecutive timeouts). See §A.

5. **DO NOT poll Aristotle.** No outstanding jobs.

6. **DO NOT introduce `axiom` or `constant`.** Cycle 205 shipped
   `IsRKOneStep_exists` axiom-clean; trans must remain so.

7. **DO NOT raise `maxHeartbeats` above 200000.** If a tactic
   times out, decompose rather than raise the limit.

8. **DO NOT attempt PReducesTo → Equivalent** (deferred direction
   (2) of thm:381H). It is the natural cycle 207+ target once
   trans is in hand — multi-cycle work involving the iteration-
   invariant "`Yᵢ⁽ᵏ⁾ = Yⱼ⁽ᵏ⁾` for `i, j` in same partition
   block". Out of scope for cycle 206.

9. **DO NOT freelance into a different §380 entity (`thm:382A`,
   `thm:382B`, `thm:384A`, `thm:386A`, etc.).** Closing the
   equivalence-relation triple (refl + symm + trans) is the high-
   value capstone for the `Equivalent` infrastructure that cycles
   201–205 built. Ship trans before opening a new sub-cluster.

10. **DO NOT touch `scripts/autonomous_loop.py`.** Loop-maintainer
    territory.

11. **DO NOT edit `extraction/raw_text/` or
    `extraction/formalization_data/entities/`.** Both are
    regenerated.

12. **DO NOT use the `linear_combination` tactic on smallness
    arithmetic.** Cycle 203 closed `|h| · L · C < 1` from
    `|h| ≤ h₀ = 1/(2*(L*C+1))` via `le_div_iff₀ + nlinarith`. Reuse
    that recipe verbatim; don't experiment with alternatives.

---

## §E. Pre-commit faithfulness check

Run the CLAUDE.md checklist on the new `Equivalent.trans`:

* **Tautology check**: conclusion `M.Equivalent M''` is not among
  the hypotheses `M.Equivalent M'` and `M'.Equivalent M''`.
  ✓ Pass.
* **Identity check**: proof is NOT `exact h₁` or `exact h₂` — it
  constructs the chain through a middle existence witness via
  `IsRKOneStep_exists`. ✓ Pass.
* **Hypothesis strength check**: `[CompleteSpace N]` is a new
  instance hypothesis vs. Butcher's textbook signature. **Document
  in the docstring**:
  > Faithfulness note: Butcher §380 does not impose completeness;
  > we add `[CompleteSpace N]` as an instance hypothesis here
  > because the proof invokes Banach existence
  > (`IsRKOneStep_exists`, cycle 205) on the middle method. All
  > concrete methods of interest over ℝⁿ have `CompleteSpace`
  > automatic, so this is a no-op at every call site. See
  > `.prover-state/issues/equivalent_self_general_deferred.md`
  > for the broader Banach infrastructure context.
* **Absent theorem check**: no theorem is promised in a comment
  but unwritten.

---

## §F. Pre-commit hygiene checks

* `lake env lean OpenMath/Chapter3/Section381.lean` exits 0.
* `grep -c sorry OpenMath/Chapter3/Section381.lean` returns 0.
* Tautology scanner clean:
  ```
  grep -nE ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' \
    OpenMath/Chapter3/Section381.lean
  ```
  returns nothing.
* `lean_verify
  OpenMath.Chapter3.Section312.RKTableau.Equivalent.trans` returns
  `[propext, Classical.choice, Quot.sound]` (or a subset).
* No regression on cycle 203/204/205 theorems — spot-check via
  `lean_verify`:
  - `RKTableau.equivalent_self`
  - `RKTableau.Equivalent.symm`
  - `RKTableau.paddedEuler_equivalent_self`
  - `RKTableau.RKStageMap_fixedPoint_unique`
  - `RKTableau.RKStageMap_fixedPoint_exists`
  - `RKTableau.IsRKOneStep_exists`

---

## §G. Cycle 207 setup

After cycle 206 ships trans:

* The equivalence-relation triple (refl + symm + trans) is
  complete. Cycle 207 can update `Equivalent`'s docstring to
  market it as a proper equivalence relation on complete normed
  spaces.
* The natural cycle 207 substantive target is **`PReducesTo →
  Equivalent`** (thm:381H deferred direction (2)). Cycle 205's
  `IsRKOneStep_exists` plus cycle 206's `Equivalent.trans` are
  the load-bearing prerequisites; the remaining work is the
  iteration-invariant "`Yᵢ⁽ᵏ⁾ = Yⱼ⁽ᵏ⁾` for `i, j` in same
  partition block" (likely 2–3 cycles).
* Alternative pivots (`thm:382A`, `thm:382B`, `thm:384A`,
  `thm:386A`, a fresh §388 entity) remain available if the cycle
  207 planner judges PReducesTo → Equivalent of lower marginal
  value than opening a new sub-cluster.

---

## §H. Pre-flight git verification (mandatory)

Before writing any Lean, run:

```bash
git log -1 --format='%H %s'
git rev-parse HEAD
git rev-parse origin/butcher-experiments
```

Expected: HEAD on `02f2ee0 Cycle 205 — §380 Banach FP existence
half`, HEAD == origin/butcher-experiments. If they disagree,
investigate; if they agree, ignore any `attempts.md` phantom
verdicts and proceed.

Confirm cycle 205 deliverables present at HEAD:

```bash
grep -n "RKStageMap_fixedPoint_exists\|IsRKOneStep_exists" \
  OpenMath/Chapter3/Section381.lean
```

Both should appear in the file. Confirm sorry-clean:

```bash
grep -c sorry OpenMath/Chapter3/Section381.lean
```

Returns 0. If any of these fail, **stop and investigate** rather
than re-doing cycle 205 work.

---

## §I. Summary

* **Primary**: ship `Equivalent.trans` (option b — side-hypothesis
  `[CompleteSpace N]`). ~30 LOC, axiom-clean, completes the
  refl + symm + trans equivalence-relation triple.
* **Stretch (only with margin)**: `paddedEuler` non-vacuity for
  `IsRKOneStep_exists` + trivial paddedEuler trans corollary.
* **Skip**: §441 Phase C.2 (GPFS-blocked, 26th consecutive).
* **Defer**: PReducesTo → Equivalent (cycle 207+).

Sorry count must remain 0. No new axioms. No `maxHeartbeats`
bumps. No edits to existing axiom-clean theorems. Document the
`[CompleteSpace N]` side-hypothesis as a faithfulness note in the
trans docstring per §E.
