# Cycle 207 Strategy — §380 `pReduced_equivalent` (PReducesTo → Equivalent, per-step)

## TL;DR

Ship **`pReduced_equivalent`** (P1, ~60–80 LOC, axiom-clean target) —
the per-step bridge `M.IsPReducibleVia P → Equivalent M (M.pReduced P)`.
This is the substantive new content unlocked by cycle 206's
`Equivalent.trans` and cycle 204/205's Banach uniqueness/existence.
With this in hand, the deferred direction (2) of `thm:381H`
(`PReducesTo → Equivalent`, see `thm_381H_deferred.md`) becomes one
straightforward induction away.

Stretch targets: **`zeroReduced_equivalent`** (P2, ~40–60 LOC) and
**`PReducesTo.toEquivalent`** (P3, ~15–25 LOC) composing P1 + P2 +
`equivalent_self` (cycle 203) + `Equivalent.trans` (cycle 206) into a
one-shot induction.

DO NOT start `thm:381G` (multi-cycle prerequisite track for the other
deferred directions; see `thm_381H_deferred.md`) and DO NOT touch §441
Phase C.2 (GPFS-blocked, 27th cycle; loop-maintainer territory).

---

## §A — §441 Phase C.2 is GPFS-blocked; skip per established policy

26 consecutive cycles (182–206) have had Section441.lean smoke-tests
time out at exactly 300s with near-zero CPU (≈0.2–0.5% of wall). The
cycle 182 draft + cycle 184 namespace fix is preserved at
`.prover-state/cycle_182_draft_section441.lean` and ready to ship the
moment GPFS recovers. **Do not attempt a Section441.lean compile this
cycle.** Add a single one-liner to `attempts.md` ("§441 Phase C.2
GPFS-blocked, 27th consecutive, skipped per strategy §A") and move on.
This is loop-maintainer escalation territory, per
`.prover-state/issues/cycle_182_gpfs_slowness.md` and
`.prover-state/issues/lem_441A_phase_C_scoping.md`.

---

## §B — Background: why `pReduced_equivalent` is now tractable

Cycle 206 closed `Equivalent.trans` (axiom-clean), completing the
equivalence-relation triple (refl + symm + trans) for `def:381A`.
The Banach FP foundation it consumed (cycles 201–205) is the same
load-bearing infrastructure needed for the textbook proof of
`PReducesTo → Equivalent` (§380 page 8631–8638 of `ch03.txt`):

> It suffices to show that if `i, j ∈ P_I` in a P-reducible method
> (def:381D), then for any IVP, `Yᵢ = Yⱼ` for `h < h₀`. Calculate the
> stages by iteration starting with `Yᵢ⁽⁰⁾ = η` for every `i ∈ {1,
> ..., s}`. The value of `Yᵢ⁽ᵏ⁾` in iteration `k` is identical for
> all `i` in the same partitioned component (by induction on `k`,
> using the row-sum-constancy of the partition).

The Lean version of "by iteration" is **Banach uniqueness** (cycle
204's `RKStageMap_fixedPoint_unique`) — instead of inducting on `k`,
we **lift** `Y'` (M.pReduced P's stages) up to M's stage indices and
show the lift is a fixed point of M's stage map, then collapse by
uniqueness. This is the cleanest direction.

---

## §C — Priority 1 (REQUIRED): `pReduced_equivalent`

### Statement

Place AFTER `Equivalent.trans` (line 1895) in
`OpenMath/Chapter3/Section381.lean`, inside the
`OpenMath.Chapter3.Section312.RKTableau` namespace block.

```lean
/-- *Per-step P-reduction preserves equivalence.* If `M` is
P-reducible via partition `P`, then `M` is equivalent to the
P-reduced method `M.pReduced P` in the sense of def:381A.

Textbook §380 page 304: the stage values of `M` are constant on each
partition block (proved via Banach uniqueness applied to the lifted
P-reduced stages). The output of `M` then collapses to the output of
`M.pReduced P` by grouping `M.b i • f(Y i)` over blocks.

Closes the per-step half of the deferred direction
`PReducesTo → Equivalent` of `thm:381H` (see
`thm_381H_deferred.md`). Combined with `Equivalent.trans` (cycle
206) and `equivalent_self` (cycle 203), the inductive lift to a full
`PReducesTo M M' → Equivalent M M'` is mechanical (Priority 3
below). -/
theorem pReduced_equivalent.{u}
    {s sBar : ℕ} {M : RKTableau s} {P : PPartition s sBar}
    (hP : M.IsPReducibleVia P) :
    @Equivalent.{u} s sBar M (M.pReduced P)
```

### Proof recipe

Mirror cycle 203's `equivalent_self` body recipe verbatim, plus the
key block-grouping step. Concrete LOC blocks:

**Block 1: threshold construction (~12 LOC, verbatim from
`equivalent_self` lines 1796–1812)**

```lean
intro N _ _ _ f L hL y₀
set C : ℝ := ∑ i : Fin s, ∑ j : Fin s, |M.A i j| with hC_def
have hC_nn : 0 ≤ C := Finset.sum_nonneg fun _ _ =>
  Finset.sum_nonneg fun _ _ => abs_nonneg _
have h_LCnn : 0 ≤ (L : ℝ) * C := mul_nonneg L.coe_nonneg hC_nn
have h_denom_pos : 0 < 2 * ((L : ℝ) * C + 1) := by linarith
refine ⟨1 / (2 * ((L : ℝ) * C + 1)), by positivity, ?_⟩
intro h hh_pos hh_le y₁ y₁' hY hY'
obtain ⟨Y, hY_stage, hY_out⟩ := hY
obtain ⟨Y', hY'_stage, hY'_out⟩ := hY'
have h_abs : |h| = h := abs_of_pos hh_pos
have h_mul : h * (2 * ((L : ℝ) * C + 1)) ≤ 1 :=
  (le_div_iff₀ h_denom_pos).mp hh_le
have h_small : |h| * (L : ℝ) * C < 1 := by
  rw [h_abs]
  nlinarith [hh_pos, h_LCnn, h_mul]
```

**Block 2: define the lift and prove it satisfies M's stage equation
(~25–35 LOC, the substantive new content)**

```lean
-- Y_lifted i := Y' (P.block i): replicate each pReduced stage across
-- its block.
set Y_lifted : Fin s → N := fun i => Y' (P.block i) with hY_lifted_def
have hY_lifted_fix : M.RKStageMap h f y₀ Y_lifted = Y_lifted := by
  funext i
  -- Goal: (M.RKStageMap h f y₀ Y_lifted) i = Y_lifted i
  -- Unfold RHS: Y_lifted i = Y' (P.block i).
  -- Unfold LHS by RKStageMap definition:
  --   = y₀ + h • Σⱼ M.A i j • f(Y_lifted j)
  --   = y₀ + h • Σⱼ M.A i j • f(Y' (P.block j))
  -- Group the sum by P-block (Finset.sum_fiberwise; see §C.1 below):
  --   = y₀ + h • Σ_J (Σ_{j with P.block j = J} M.A i j) • f(Y' J)
  -- Inner sum = (M.pReduced P).A (P.block i) J by `pReduced_A_apply`
  -- (requires hP, which is exactly `M.IsPReducibleVia P`).
  -- So LHS = y₀ + h • Σ_J (M.pReduced P).A (P.block i) J • f(Y' J)
  --       = Y' (P.block i) (by hY'_stage at index P.block i)
  --       = Y_lifted i.
  sorry  -- ~20 LOC of `simp [RKStageMap]` + Finset sum manipulation
```

Key Mathlib lemmas for the sum-grouping step:
* `Finset.sum_fiberwise` or `Finset.sum_fiberwise_of_maps_to` — group
  `Σ j ∈ Finset.univ, g j` by an equivalence `Fin s → Fin sBar`.
  The likely signature is
  ```
  ∑ b ∈ s.image g, ∑ a ∈ s.filter (g · = b), f a = ∑ a ∈ s, f a
  ```
  Use it with `s := Finset.univ : Finset (Fin s)`, `g := P.block`.
  Verify with `lean_loogle` / `lean_local_search` before commitment.
* `pReduced_A_apply` (line 319): the row-sum-constancy package.
  Signature: takes `h : M.IsPReducibleVia P`, returns
  `(M.pReduced P).A I J = Σ_{j ∈ filter (P.block · = J)} M.A i j`
  for any `i` with `P.block i = I`. **This is the load-bearing
  consumer of the `hP` hypothesis.**
* `RKStageMap` unfolding (line 1605): `(M.RKStageMap h f y₀ Y) i =
  y₀ + h • Σⱼ M.A i j • f(Y j)`.

**Block 3: extract Y = Y_lifted via Banach uniqueness (~5 LOC,
verbatim from cycle 203 lines 1813–1820)**

```lean
have hY_fix : M.RKStageMap h f y₀ Y = Y := by
  funext i; exact (hY_stage i).symm
have hY_eq : Y = Y_lifted :=
  M.RKStageMap_fixedPoint_unique h hL y₀ h_small hY_fix hY_lifted_fix
```

**Block 4: collapse the outputs (~15–20 LOC, second sum-grouping)**

```lean
-- Output of M:  y₁ = y₀ + h • Σᵢ M.b i • f(Y i)
-- Substituting Y = Y_lifted = fun i => Y' (P.block i):
--   = y₀ + h • Σᵢ M.b i • f(Y' (P.block i))
-- Group by block (Finset.sum_fiberwise again):
--   = y₀ + h • Σ_J (Σ_{i with P.block i = J} M.b i) • f(Y' J)
-- Inner sum = (M.pReduced P).b J by `pReduced_b_apply` (defeq, no
-- `IsPReducibleVia` hypothesis needed).
-- So  y₁ = y₀ + h • Σ_J (M.pReduced P).b J • f(Y' J) = y₁'.
rw [hY_out, hY'_out, hY_eq]
-- Goal: y₀ + h • Σᵢ M.b i • f(Y_lifted i)
--      = y₀ + h • Σⱼ (M.pReduced P).b j • f(Y' j)
sorry  -- the sum-grouping closure
```

### §C.1 — Finset sum-fiberwise lemma identification (DO FIRST)

The cleanest Mathlib lemma is probably `Finset.sum_fiberwise` (or its
`_of_maps_to` variant). **Verify with `lean_loogle` /
`lean_local_search` BEFORE writing the sum-grouping bodies.** Suggested
queries:

```
lean_local_search "sum_fiberwise"
lean_loogle "∑ _, ∑ _ ∈ Finset.filter _ _, _ = ∑ _, _"
lean_loogle "Finset.sum_fiberwise"
```

If `Finset.sum_fiberwise` is the wrong shape, try:
* `Finset.sum_partition`
* `Fintype.sum_fiberwise`
* Building it inline from `Finset.sum_bij`

If you cannot find a single load-bearing lemma in ~15 min, factor the
"group-by-block" sum identity into a **private helper** taking
`(g : α → β) (f : α → M)`-style data and prove it inline by
`Finset.induction` on `Finset.univ`. Do NOT spend >30 min searching
— write the helper.

### §C.2 — Universe annotation

`Equivalent` is universe-polymorphic (cycle 204 discovery). Annotate
the theorem and any `@Equivalent` references with `.{u}` — see
`Equivalent.symm.{u}` (line 1828) and `Equivalent.trans.{u}` (line
1863) for the exact pattern. The `intro N _ _ _ f L hL y₀` pattern
has **four underscores** for the three typeclass instances plus
`[CompleteSpace N]` (cycle 206 addition to `Equivalent`'s binders).

### §C.3 — Aristotle suitability

**Submit Block 2 + Block 4 sum-grouping bodies as an Aristotle batch
near the start of the cycle.** The proof shape is mechanical
`Finset.sum_fiberwise` + `pReduced_A_apply` / `pReduced_b_apply`
plus a `simp [RKStageMap]` unfold; medium suitability. Submit a
single self-contained file with the `pReduced` and `IsPReducibleVia`
definitions inlined, then continue manual work in parallel.
CLAUDE.md discipline: single poll at the end of the cycle, no
re-poll.

---

## §D — Priority 2 (STRETCH): `zeroReduced_equivalent`

### Statement

```lean
/-- *Per-step 0-reduction preserves equivalence.* If `M` is
0-reducible via the Boolean predicate `inP1` (P₀ non-empty), then `M`
is equivalent to the 0-reduced method `M.zeroReduced inP1`. -/
theorem zeroReduced_equivalent.{u}
    {s : ℕ} {M : RKTableau s} {inP1 : Fin s → Bool}
    (hP0 : ∃ i, inP1 i = false)
    (h0 : M.IsZeroReducibleVia inP1) :
    @Equivalent.{u} s _ M (M.zeroReduced inP1)
```

### Proof recipe (project-down approach, NOT lift-up)

0-reduction has asymmetric structure (P₀ stages disappear), so the
clean argument is the **project-down** approach — opposite to P-
reduction:

1. Take `Y` (stages of M, given by hY) and `Y'` (stages of
   M.zeroReduced inP1, given by hY').
2. Define `Z : Fin sBar → N` by `Z J := Y (zeroReducedEmb inP1 J)`
   (project Y onto P₁).
3. Show Z satisfies `M.zeroReduced inP1`'s stage equation. Key step:
   ```
   (M.zeroReduced inP1).RKStageMap h f y₀ Z J
     = y₀ + h • Σ_K (M.zeroReduced inP1).A J K • f(Z K)
     = y₀ + h • Σ_K M.A (emb J) (emb K) • f(Y (emb K))   [zeroReduced_A_apply]
     = y₀ + h • Σ_{j ∈ P₁} M.A (emb J) j • f(Y j)         [reindex via emb]
     = y₀ + h • Σ_{j : Fin s} M.A (emb J) j • f(Y j)      [j ∈ P₀ ⇒ M.A (emb J) j = 0, by h0.2]
     = Y (emb J)                                          [hY_stage]
     = Z J. ✓
   ```
4. By Banach uniqueness on `M.zeroReduced inP1`'s stage map (needs
   `|h| · L · C_zr < 1` where `C_zr := Σ_{I,J} |(M.zeroReduced inP1).A I J|`;
   since C_zr ≤ C_M, **the cycle 203 threshold `h₀ := 1 / (2·(L·C_M+1))`
   suffices**), `Z = Y'`.
5. Output collapse: `y₁ = y₀ + h • Σᵢ M.b i • f(Y i)`. Split the sum
   into P₀ and P₁ parts. P₀ part vanishes by `h0.1` (M.b i = 0 for
   i ∈ P₀). P₁ part reindexes via `emb` to
   `y₀ + h • Σⱼ M.b (emb j) • f(Y (emb j)) = y₀ + h • Σⱼ
   (M.zeroReduced inP1).b j • f(Z j) = y₁'` (by `zeroReduced_b_apply`).

Key Mathlib lemmas:
* `Finset.sum_attach` / `Finset.sum_image` / `Finset.sum_filter` —
  for the reindex via `zeroReducedEmb`. The cleanest path is probably
  `Finset.sum_image` on the image of `zeroReducedEmb` (which equals
  `Finset.univ.filter (inP1 · = true)`).
* `zeroReduced_A_apply` (line 244), `zeroReduced_b_apply` (line 253).

### §D.1 — Skip-conditions

Skip P2 if:
* P1 took longer than expected and the cycle is near its budget.
* The Finset-sum-restriction-via-`emb` step requires Mathlib lemmas
  not findable in ~15 min.

P2 is genuinely different infrastructure from P1 (P₁-projection vs.
block-grouping), so do not block the cycle on it.

---

## §E — Priority 3 (STRETCH-of-STRETCH): `PReducesTo.toEquivalent`

ONLY attempt if P1 AND P2 are both axiom-clean and the cycle has
budget. Final inductive composition:

```lean
/-- *Reflexive-transitive closure of P-reduction implies def:381A
equivalence.* Closes the deferred direction (2) of `thm:381H`. -/
theorem PReducesTo.toEquivalent.{u}
    {s s' : ℕ} {M : RKTableau s} {M' : RKTableau s'}
    (h : PReducesTo M M') :
    @Equivalent.{u} s s' M M' := by
  induction h with
  | refl M => exact equivalent_self M
  | step P _hLt hVia _h_tail ih =>
      exact (pReduced_equivalent hVia).trans ih
  | zeroStep inP1 hP0 hVia _h_tail ih =>
      exact (zeroReduced_equivalent hP0 hVia).trans ih
```

Three constructors, three one-liners chained through `Equivalent.trans`
(cycle 206). ~15 LOC including docstring.

**Universe gotcha**: cycle 204 discovered that `@Equivalent.{u}`
annotations must be shared across any signature that takes
Equivalent as both hypothesis and conclusion. Annotate
`PReducesTo.toEquivalent.{u}` and use `@Equivalent.{u}` in the
conclusion if the elaborator complains.

---

## §F — What NOT to try this cycle

* **DO NOT attempt the other two deferred directions of `thm:381H`**
  (`PhiEquivalent → PEquivalent` and `Equivalent → PEquivalent`) —
  both block on `thm:381G` per `thm_381H_deferred.md`, which is a
  4–5 cycle prerequisite track. Cycle 207 is the wrong cycle.
* **DO NOT touch Section441.lean** — 26 consecutive GPFS timeouts.
  Log one-line skip in attempts.md.
* **DO NOT introduce confluence infrastructure for P-reduction**
  (`p_reduction_confluence_gap.md`) — multi-cycle scope.
* **DO NOT change the `Equivalent` definition** — cycle 206 just
  added `[CompleteSpace N]` to the internal binders; further
  modification would invalidate `equivalent_self`,
  `Equivalent.symm`, `Equivalent.trans`,
  `equivalent_explicitEuler_self`, `paddedEuler_equivalent_self`,
  and now `pReduced_equivalent`.
* **DO NOT modify `scripts/autonomous_loop.py`** — phantom-verdict
  bug and tautology scanner bug remain loop-maintainer territory
  per `phantom_commit_verdict_pattern.md` and
  `tautology_scanner_false_positives.md`.
* **DO NOT raise maxHeartbeats above 200000**.
* **DO NOT introduce `axiom` or `constant`**.
* **DO NOT attempt P1 via "project-down"** (define `Z : Fin sBar → N`
  by `Z J := Y i` for any `i` in block `J` and show `Z = Y'`). That
  approach requires first proving Y is constant on blocks, which is
  the thing we are trying to prove. The lift-up approach is the
  cleaner direction for P-reduction. (For 0-reduction the project-
  down approach IS cleaner; the asymmetry is real and intentional.)
* **DO NOT submit `pReduced_equivalent`'s ENTIRE body to Aristotle.**
  Submit only Block 2 (the lifted stage-equation verification) and
  optionally Block 4 (output collapse) as focused sub-jobs. Block 1
  is verbatim cycle 203 lines 1796–1812 and Block 3 is verbatim
  cycle 203 lines 1813–1820 — copy them manually.
* **DO NOT spend >30 minutes searching for the right
  `Finset.sum_fiberwise` lemma.** If not found, write a private
  helper via `Finset.induction` on `Finset.univ`.

---

## §G — Pitfalls to watch for

1. **Universe annotation propagation.** Use `.{u}` on the theorem
   declaration and `@Equivalent.{u}` on hypothesis/conclusion
   references. Mirror cycle 204's `Equivalent.symm.{u}` (line 1828)
   and cycle 206's `Equivalent.trans.{u}` (line 1863).

2. **`intro N _ _ _ f L hL y₀`** — FOUR underscores (one per
   typeclass: `NormedAddCommGroup`, `NormedSpace ℝ`,
   `CompleteSpace`), per the cycle 206 update to `Equivalent`'s
   binders. THREE underscores is a cycle-204-era pattern that no
   longer works.

3. **`pReduced_A_apply` consumes `hP : M.IsPReducibleVia P`.** The
   load-bearing application of `hP` is here. If you find yourself
   trying to use `hP` elsewhere, you are off-recipe.

4. **`pReduced_b_apply` is definitional (`rfl`)** — no
   `IsPReducibleVia` hypothesis needed for the output-collapse step.

5. **`Finset.sum_fiberwise` direction.** The lemma converts between
   `∑ b, ∑ a in fiber b, f a` and `∑ a, f a`. You want the LATTER
   direction (collapse a `Σⱼ : Fin s` to a `Σ_J : Fin sBar` with an
   inner block-restricted `Σⱼ`). Use `←` if needed. Verify direction
   by `lean_hover_info` on the lemma name before applying.

6. **`Y'` has type `Fin sBar → N`, not `Fin s → N`.** When applying
   `hY'_stage` at index `P.block i` (an element of `Fin sBar`), you
   get an equation for `Y' (P.block i)`. Keep the indices straight.

7. **Tautology scanner.** Don't introduce `have h_<name> := ...`
   followed by `exact h_<name>` — use `hname` (no underscore). See
   `tautology_scanner_false_positives.md`.

8. **Block 2's `simp [RKStageMap]` may not unfold cleanly.** The
   definition of `RKStageMap` (line 1605) uses `fun i => ...`. If
   `simp [RKStageMap]` doesn't fire, try `show ... = ...; simp only
   [...]` or `unfold RKStageMap`. Verify the unfolded shape with
   `lean_goal` before applying further simp.

---

## §H — Cycle 208 prefigure (if this cycle ships P1+P2+P3)

If P1, P2, P3 all land axiom-clean, cycle 208 has these options. Do
NOT pre-empt the decision; record them for the cycle 208 planner.

* **Statement-only `thm:381H` scaffold** with two of four iff
  directions closed (PEquivalent → PhiEquivalent via cycle 187,
  PReducesTo → Equivalent via cycle 207). Carefully: the cycle 200
  attempt at this with 3 sorries was rolled back in cycle 201; only
  attempt if 0–1 sorries (i.e. nearly all directions closeable).
* **`def:382A`/`thm:382A`** (composition group of RK methods) —
  fresh §382 entity opening a new sub-cluster.
* **`thm:314A`** (Independence of elementary differentials) — would
  unblock thm:381G work later.
* **paddedEuler non-vacuity for `IsRKOneStep_exists`** (~5–10 LOC)
  + Setoid promotion of `Equivalent` (~5–10 LOC) — quick consolidation
  cycle.

---

## §I — Cycle deliverable bar

* **Minimum**: ship P1 (`pReduced_equivalent`) axiom-clean. Sorry
  count: 0 → 0.
* **Target**: ship P1 + P2. Sorry count: 0 → 0.
* **Stretch**: ship P1 + P2 + P3. Sorry count: 0 → 0.
* **Fallback** (if Block 2 sum-grouping stalls past 90 min): write
  the missing-lemma gap up in an issue file
  (`finset_sum_fiberwise_for_pReduced.md`), then ship the cycle
  205/206 stretch `paddedEuler_IsRKOneStep_exists` (~5–10 LOC,
  trivial since paddedEuler is explicit so the witness is the
  explicit Euler output formula) + a ~10-LOC `Equivalent.setoid`
  Setoid promotion as Plan-C deliverables. **Avoid the 0-sorry no-
  content failure mode** — every cycle must produce a named
  axiom-clean deliverable per CLAUDE.md.

Pass criteria for axiom-cleanliness:
* `lake env lean OpenMath/Chapter3/Section381.lean` exits 0.
* `lean_verify OpenMath.Chapter3.Section312.RKTableau.pReduced_equivalent`
  returns `[propext, Classical.choice, Quot.sound]` only.
* `grep -c sorry OpenMath/Chapter3/Section381.lean` returns 0.
* Tautology scanner clean.
* No regression on cycles 203/204/205/206 theorems
  (`equivalent_self`, `Equivalent.symm`, `Equivalent.trans`,
  `RKStageMap_fixedPoint_*`, `IsRKOneStep_exists`,
  `paddedEuler_equivalent_self`, `equivalent_explicitEuler_self`).

---

## §J — Time budget guidance

* 0–10 min: `lean_local_search` / `lean_loogle` for
  `Finset.sum_fiberwise` (§C.1). If found, proceed to §C; if not
  found in 15 min, plan to write a private helper.
* 10–20 min: Aristotle batch submission of Block 2 + Block 4 bodies
  (§C.3). Use a self-contained file with `pReduced`,
  `IsPReducibleVia`, `RKStageMap` definitions inlined.
* 20–45 min: write Block 1 (threshold; verbatim copy from cycle 203).
* 45–120 min: write Block 2 (lifted stage equation; the hard part).
* 120–135 min: write Block 3 (Banach uniqueness; verbatim).
* 135–180 min: write Block 4 (output collapse).
* 180–210 min: verify P1 axiom-clean; commit.
* 210–270 min: attempt P2.
* 270–290 min: attempt P3.
* 290+ min: Aristotle poll, commit final state.

If you hit the 120-min mark with Block 2 still open and no
near-term closure, switch to **§I Fallback**: open the gap-issue
file and ship `paddedEuler_IsRKOneStep_exists` + Setoid promotion
instead. **Do not leave a `sorry` in `pReduced_equivalent` at the
end of the cycle** — it would regress the 0-sorry count and trigger
a supervisor rollback (per cycle 201 precedent).
