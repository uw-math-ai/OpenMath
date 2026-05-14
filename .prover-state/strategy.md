# Cycle 220 Strategy — §382 group inverse element

## §A — GPFS smoke test (mandatory, ≤6 min)

Before any §382 work, run **once**:

```bash
time timeout 300 lake env lean OpenMath/Chapter4/Section441.lean
```

Expected: 37th consecutive 5-min timeout with near-zero CPU. **If it
times out, skip §441 Phase C.2 entirely** and proceed to §B below.
Append one line to `.prover-state/issues/cycle_182_gpfs_slowness.md`
recording the timeout count (37) and proceed.

If by some surprise it succeeds (<5 min), the cycle 182 draft +
cycle 184 namespace fix at `.prover-state/cycle_182_draft_section441.lean`
becomes the new top priority; bail out of this strategy and ship
that instead. Confirm `head -10 .prover-state/cycle_182_draft_section441.lean`
exists first.

**Do not re-attempt §441 within this cycle if §A times out.**

---

## §B — Main deliverable: §382 inverse element (`thm:382B`)

### Target entity

`thm:382B` (Butcher §382 p. 307) — currently `unformalized` in
`extraction/formalization_data/lean_status.json`. The textbook
statement is `[m · m⁻¹] = [m⁻¹ · m] = 1`. Per cycle 219's task
results' "Suggested next approach", this is **cycle 220's
deliverable**.

### Textbook inverse formula (from `entities/thm_382B.json`)

For `M : RKTableau s` with stages `(A, b, c)`, the inverse method
`M.inverse : RKTableau s` has:

* `(M.inverse).A i j := M.A i j − M.b j`
* `(M.inverse).b i := −M.b i`
* `(M.inverse).c i := M.c i − ∑ j, M.b j`

(The stage count stays at `s`.)

### Proof technique (abstract-N-level, sidesteps the textbook's P-reducibility argument)

The textbook's proof shows the composite is P-reducible to a method
with `b = 0`. We take a cleaner Lean route: prove
`m.compose m.inverse ≡ id` directly at the `IsRKOneStep` level using
cycle 214's `compose_isRKOneStep_iff` and cycle 219's
`id_isRKOneStep_iff`. The load-bearing observation:

**Lemma (key):** If `M.IsRKOneStep f y₀ H y_mid` with stage tuple
`Y : Fin s → N`, then `M.inverse.IsRKOneStep f y_mid H y₀` with the
**same** stage tuple `Y`.

**Proof:** Plug `Y` into `M.inverse`'s stage equation:
```
Y i = y₀ + H • ∑ j, M.A i j • f (Y j)                  -- M's stage eq
    = (y_mid − H • ∑ j, M.b j • f (Y j)) + H • ∑ j, M.A i j • f (Y j)
                                                       -- (using M's output eq)
    = y_mid + H • ∑ j, (M.A i j − M.b j) • f (Y j)
    = y_mid + H • ∑ j, M.inverse.A i j • f (Y j)       -- ✓
```
And the output equation:
```
y_mid + H • ∑ i, M.inverse.b i • f (Y i)
  = y_mid + H • ∑ i, (−M.b i) • f (Y i)
  = y_mid − H • ∑ i, M.b i • f (Y i)
  = y_mid − (y_mid − y₀)
  = y₀                                                  -- ✓
```

This gives a witness `M.inverse.IsRKOneStep f y_mid H y₀` from the
`M`-step. Symmetrically, an `M.inverse`-step from `y_mid` back can
produce an `M`-step from `y₀`. Combined with cycle 203's
`equivalent_self M.inverse` (which gives uniqueness of M.inverse's
step at small H), this forces every composite output `y_final = y₀`.

### Priorities (linear execution)

#### P1 (single-cycle minimum) — Define `RKTableau.inverse`

Add in `OpenMath/Chapter3/Section381.lean`, inside `namespace
OpenMath.Chapter3.Section312.RKTableau`, immediately after
`RKTableau.id` and `id_isRKOneStep_iff` (around line 2820):

```lean
/-- *Inverse method (§382).* For a Runge–Kutta method `M` with
stages `(A, b, c)`, the inverse method `M.inverse` has stages
`(A i j − b j,  −b i,  c i − ∑ j, b j)`. This is the §382 group
inverse construction (Butcher §382 p. 307). Same stage count
`s`. -/
def inverse {s : ℕ} (M : RKTableau s) : RKTableau s where
  A := fun i j => M.A i j - M.b j
  b := fun i => -M.b i
  c := fun i => M.c i - ∑ j, M.b j
```

LOC: ~10 with docstring.

#### P2 (the substantive deliverable) — Key step-inversion lemma

Add immediately after the definition:

```lean
/-- *Inverse-step inversion lemma.* If a stage tuple `Y` witnesses
`M.IsRKOneStep f y₀ H y_mid`, then the *same* stage tuple witnesses
`M.inverse.IsRKOneStep f y_mid H y₀`. This is the load-bearing
algebraic observation behind the §382 inverse-element absorption
laws. -/
theorem inverse_isRKOneStep_of_isRKOneStep {s : ℕ} (M : RKTableau s)
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    {f : N → N} {y₀ y_mid : N} {H : ℝ}
    (h : M.IsRKOneStep f y₀ H y_mid) :
    M.inverse.IsRKOneStep f y_mid H y₀ := by
  obtain ⟨Y, hY_stage, hY_out⟩ := h
  refine ⟨Y, ?_, ?_⟩
  · intro i
    -- Stage eq for M.inverse at base y_mid, same Y.
    -- Use hY_stage i (M's stage eq) and hY_out (M's output eq).
    sorry  -- See §C.1 below for the exact closure
  · -- Output eq: y_mid + H • ∑ i, (-M.b i) • f (Y i) = y₀
    sorry  -- See §C.2 below for the exact closure
```

**IMPORTANT**: The two `sorry` lines above are *placeholders for
the closure tactic*, not deliverables. They must be replaced with
**working tactics that close the goal axiom-clean** before commit.

**LOC target**: ~25–35 LOC total. **Time budget**: 30 min.

See §C below for the exact tactic forms most likely to fire.

#### P3 — `compose_inverse_equivalent` (right absorption)

Add after P2:

```lean
/-- *Right inverse absorption (§382).* `M · M⁻¹ ≡ id` at the
`Equivalent` level. Heterogeneous-stage: LHS has `s + s` stages,
RHS has `0`. The proof uses cycle 214's `compose_isRKOneStep_iff`
to factor any composite output, then `inverse_isRKOneStep_of_isRKOneStep`
to convert the M-half into an M.inverse-step from y_mid back to y₀,
then `equivalent_self M.inverse` (cycle 203) to identify the original
M.inverse-half's output with y₀. -/
theorem compose_inverse_equivalent.{u} {s : ℕ} (M : RKTableau s) :
    @Equivalent.{u} (s + s) 0 (M.compose M.inverse) RKTableau.id := by
  intro N _ _ _ f L hL
  obtain ⟨H₀, hH₀_pos, hEq⟩ := M.inverse.equivalent_self.{u} f L hL
  refine ⟨H₀, hH₀_pos, ?_⟩
  intro y₀ H hH_pos hH_le y_final y_final' h_compose h_id
  rw [RKTableau.id_isRKOneStep_iff] at h_id
  obtain ⟨y_mid, h_M_step, h_Minv_step⟩ :=
    (compose_isRKOneStep_iff M M.inverse f y₀ H y_final).mp h_compose
  have h_alt : M.inverse.IsRKOneStep f y_mid H y₀ :=
    M.inverse_isRKOneStep_of_isRKOneStep h_M_step
  have hy_final_eq_y₀ : y_final = y₀ :=
    hEq y_mid H hH_pos hH_le y_final y₀ h_Minv_step h_alt
  rw [hy_final_eq_y₀, h_id]
```

LOC: ~25.

#### P4 — `inverse_compose_equivalent` (left absorption)

Symmetric to P3. The key difference: we need
`M.IsRKOneStep f y_mid H y₀` from an `M.inverse.IsRKOneStep f y₀ H
y_mid`. **Use the §C.4 direct route** — prove a symmetric helper
`isRKOneStep_of_inverse_isRKOneStep` that gives
`M.IsRKOneStep f y_mid H y₀` from `M.inverse.IsRKOneStep f y₀ H
y_mid`. ~15 LOC for the helper + ~25 LOC for `inverse_compose_equivalent`.

Skip `inverse_inverse` (M.inverse.inverse = M) entirely — it's NOT
definitionally true (subtraction doesn't unfold to `rfl`) and the
symmetric helper is cleaner.

```lean
/-- *Inverse-step inversion lemma, symmetric direction.* Given a
stage tuple `Y` witnessing `M.inverse.IsRKOneStep f y₀ H y_mid`,
the same `Y` witnesses `M.IsRKOneStep f y_mid H y₀`. -/
theorem isRKOneStep_of_inverse_isRKOneStep {s : ℕ} (M : RKTableau s)
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    {f : N → N} {y₀ y_mid : N} {H : ℝ}
    (h : M.inverse.IsRKOneStep f y₀ H y_mid) :
    M.IsRKOneStep f y_mid H y₀ := by
  obtain ⟨Y, hY_stage, hY_out⟩ := h
  refine ⟨Y, ?_, ?_⟩
  · -- Symmetric to §C.1: y_mid = y₀ - H•∑b•f(Y), so y₀ = y_mid + H•∑b•f(Y).
    -- Y i = y₀ + H•∑(A-b)•f(Y) = y_mid + H•∑b•f(Y) + H•∑(A-b)•f(Y) = y_mid + H•∑A•f(Y).
    sorry  -- Close with §C.1-style tactic
  · -- Symmetric to §C.2: y_mid + H•∑b•f(Y) = y₀.
    -- From hY_out: y_mid = y₀ + H•∑(-b)•f(Y) = y₀ - H•∑b•f(Y), so y₀ = y_mid + H•∑b•f(Y).
    sorry  -- Close with §C.2-style tactic + sign flip
```

Then:

```lean
theorem inverse_compose_equivalent.{u} {s : ℕ} (M : RKTableau s) :
    @Equivalent.{u} (s + s) 0 (M.inverse.compose M) RKTableau.id := by
  intro N _ _ _ f L hL
  obtain ⟨H₀, hH₀_pos, hEq⟩ := M.equivalent_self.{u} f L hL
  refine ⟨H₀, hH₀_pos, ?_⟩
  intro y₀ H hH_pos hH_le y_final y_final' h_compose h_id
  rw [RKTableau.id_isRKOneStep_iff] at h_id
  obtain ⟨y_mid, h_Minv_step, h_M_step⟩ :=
    (compose_isRKOneStep_iff M.inverse M f y₀ H y_final).mp h_compose
  have h_alt : M.IsRKOneStep f y_mid H y₀ :=
    M.isRKOneStep_of_inverse_isRKOneStep h_Minv_step
  have hy_final_eq_y₀ : y_final = y₀ :=
    hEq y_mid H hH_pos hH_le y_final y₀ h_M_step h_alt
  rw [hy_final_eq_y₀, h_id]
```

LOC: ~40 combined.

#### P5 — Quotient-level absorption laws (mechanical)

Pattern from cycle 219's `composeQ_id_left`/`composeQ_id_right`:

```lean
theorem composeQ_inverse_right.{u} {s : ℕ} (M : RKTableau s) :
    composeQ.{u}
        (Quotient.mk Equivalent.setoidSigma.{u} ⟨s, M⟩)
        (Quotient.mk Equivalent.setoidSigma.{u} ⟨s, M.inverse⟩)
      = Quotient.mk Equivalent.setoidSigma.{u} ⟨0, RKTableau.id⟩ := by
  show Quotient.mk _ _ = Quotient.mk _ _
  exact Quotient.sound (M.compose_inverse_equivalent.{u})

theorem composeQ_inverse_left.{u} {s : ℕ} (M : RKTableau s) :
    composeQ.{u}
        (Quotient.mk Equivalent.setoidSigma.{u} ⟨s, M.inverse⟩)
        (Quotient.mk Equivalent.setoidSigma.{u} ⟨s, M⟩)
      = Quotient.mk Equivalent.setoidSigma.{u} ⟨0, RKTableau.id⟩ := by
  show Quotient.mk _ _ = Quotient.mk _ _
  exact Quotient.sound (M.inverse_compose_equivalent.{u})
```

LOC: ~15. Pure bookkeeping.

#### P6 — Non-vacuity witnesses on `paddedEuler`

In `namespace OpenMath.Chapter3.Section381`, after the cycle 219 P6
examples (around line 3098):

```lean
example : composeQ.{0}
    (Quotient.mk Equivalent.setoidSigma.{0} ⟨2, paddedEuler⟩)
    (Quotient.mk Equivalent.setoidSigma.{0} ⟨2, paddedEuler.inverse⟩)
  = Quotient.mk Equivalent.setoidSigma.{0} ⟨0, RKTableau.id⟩ :=
  RKTableau.composeQ_inverse_right paddedEuler

example : composeQ.{0}
    (Quotient.mk Equivalent.setoidSigma.{0} ⟨2, paddedEuler.inverse⟩)
    (Quotient.mk Equivalent.setoidSigma.{0} ⟨2, paddedEuler⟩)
  = Quotient.mk Equivalent.setoidSigma.{0} ⟨0, RKTableau.id⟩ :=
  RKTableau.composeQ_inverse_left paddedEuler
```

LOC: ~10. Verifies the laws compose on the cycle 030 backbone.

---

## §C — Tactic-level closure hints (use when P2 / P4 helper goals open)

### §C.1 — Stage-equation closure pattern

Starting goal (after `intro i` and unfolding `M.inverse`):
```
Y i = y_mid + H • ∑ j, (M.A i j − M.b j) • f (Y j)
```
with `hY_stage : Y i = y₀ + H • ∑ j, M.A i j • f (Y j)` and
`hY_out : y_mid = y₀ + H • ∑ j, M.b j • f (Y j)`.

Recipe:
```lean
simp only [inverse]
rw [hY_stage i]   -- LHS becomes y₀ + H • ∑ j, M.A i j • f (Y j)
-- Now goal: y₀ + H•∑A•f(Y) = y_mid + H•∑(A-b)•f(Y)
-- Replace y_mid via hY_out, then expand the (A-b) sum.
conv_rhs => rw [hY_out]
-- Goal: y₀ + H•∑A•f(Y) = (y₀ + H•∑b•f(Y)) + H•∑(A-b)•f(Y)
simp only [sub_smul, Finset.sum_sub_distrib, smul_sub]
abel
```

If `abel` doesn't close, fall back to:
```lean
ring_nf
-- if that also fails:
have hsplit : ∀ j, (M.A i j - M.b j) • f (Y j)
              = M.A i j • f (Y j) - M.b j • f (Y j) :=
  fun j => sub_smul _ _ _
simp_rw [hsplit, Finset.sum_sub_distrib]
linarith  -- WRONG; use module / linear_combination instead
```

Better: use `linear_combination`:
```lean
linear_combination hY_stage i - hY_out
```
This is the cleanest tactic for "I know A = X and B = Y; conclude
A - B = X - Y"-style goals.

### §C.2 — Output-equation closure pattern

Starting goal (after unfolding `M.inverse`):
```
y_mid + H • ∑ i, (-M.b i) • f (Y i) = y₀
```
with `hY_out : y_mid = y₀ + H • ∑ i, M.b i • f (Y i)`.

Recipe:
```lean
simp only [inverse]
-- Pull negation out of the sum.
have hsum_neg : ∀ i, (-M.b i) • f (Y i) = -(M.b i • f (Y i)) :=
  fun i => by rw [neg_smul]
simp_rw [hsum_neg, Finset.sum_neg_distrib]  -- or `← Finset.sum_neg`
-- Goal: y_mid + H • -(∑ i, M.b i • f (Y i)) = y₀
rw [smul_neg]
-- Goal: y_mid - H • ∑ i, M.b i • f (Y i) = y₀
linarith [hY_out]   -- WRONG (Y not real); use linear_combination instead
```

Cleaner:
```lean
linear_combination -hY_out
```
(or `linear_combination hY_out` if sign flips the other way).

### §C.3 — Risk: `Finset.sum_neg_distrib` vs `Finset.sum_neg`

`lean_loogle` for the actual name if `simp_rw` doesn't fire:

```
loogle: ∑ i, -f i = -∑ i, f i
```

Candidates: `Finset.sum_neg_distrib` (older), `Finset.sum_neg`
(newer Mathlib), or `neg_sum`. Pre-confirm via
`lean_local_search "Finset.sum_neg"` early in cycle.

### §C.4 — Why we use the symmetric helper instead of `M.inverse.inverse = M`

`M.inverse.inverse` unfolds to:
* `A i j := (M.A i j − M.b j) − (−M.b j) = M.A i j` ✓
* `b i := −(−M.b i) = M.b i` ✓
* `c i := (M.c i − ∑ j, M.b j) − ∑ j, (−M.b j) = M.c i` ✓

The unfolding is definitionally clean for `b` and `c`, but `A` and
`c` involve subtraction-reaching-rewrite that won't be `rfl`. Could
ship `inverse_inverse` via:
```lean
theorem inverse_inverse {s : ℕ} (M : RKTableau s) :
    M.inverse.inverse = M := by
  ext <;> simp [inverse]
```
**Optional**, only if needed. The symmetric helper `isRKOneStep_of_inverse_isRKOneStep`
is more direct for P4's needs and doesn't depend on this rewrite.

---

## §D — Risk inventory (anticipated, plan in advance)

* **R1** — `Finset.sum_neg_distrib` / `Finset.sum_neg` name drift.
  Mitigation: `lean_loogle` early; both signatures are
  `∀ f, ∑ i, -f i = -∑ i, f i`. Pre-confirm name before P2.
* **R2** — `linear_combination` may fail on module goals (smul +
  Finset.sum). Mitigation: `module` tactic instead, or explicit
  `Finset.sum_add_distrib` + `Finset.sum_sub_distrib` decomposition,
  closing per-term with `congr; ring` then `Finset.sum_congr rfl`.
  Cycle 207's `pReduced_equivalent` proof uses similar patterns
  successfully — review its structure if §C.1 stalls.
* **R3** — `RKTableau.mk.injEq` / Field projections. The `inverse`
  definition uses `where` syntax; verify access via `M.inverse.A`,
  `M.inverse.b`, `M.inverse.c` unfolds cleanly to the formula via
  `simp only [inverse]`. Mitigation: explicit `show` reframing if
  unfolds stall.
* **R4** — `Equivalent`'s uniform-threshold quantifier shape (cycle
  216 refactor): the order is `∃ h₀, ∀ y₀, ∀ h, ...`. P3 and P4
  both `obtain ⟨H₀, ...⟩` first, then `intro y₀ H ...` — match
  cycle 219's `compose_id_equivalent` proof shape exactly.
* **R5** — `IsRKOneStep`'s instance arguments must be unpacked in
  `intro N _ _ _ f L hL` — three underscores for
  `[NormedAddCommGroup N] [NormedSpace ℝ N] [CompleteSpace N]`.
  Match cycle 219's intro pattern.
* **R6** — Universe annotations. Every `Equivalent` reference must
  carry `.{u}`; same for `setoidSigma.{u}` in P5. Apply only to
  `Equivalent` / `setoidSigma`, NEVER to `RKTableau` (cycle 218
  dead end).
* **R7** — `equivalent_self M.inverse` may require explicit
  universe annotation: `M.inverse.equivalent_self.{u}`. Match the
  pattern from cycle 219's `compose_id_equivalent` proof.

---

## §E — Hard rules

* **Sorry count must remain 0 at commit time.** Any `sorry` shown
  in §B above is a placeholder; replace with working tactics or
  abort to §F.
* **No `axiom` / `constant` declarations.**
* **No `maxHeartbeats` bumps** above the project default.
* **No re-attempt of §441 Phase C.2** if §A times out (expected).
* **No modification of `scripts/autonomous_loop.py`** (loop-maintainer
  territory).
* **Faithfulness**: `RKTableau.inverse` matches Butcher §382 p. 307
  *literally* — `A_ij − b_j`, `−b_i`, `c_i − ∑b_j`. Do not "simplify"
  or reorder.

---

## §F — Abort threshold and fallback

* **If P2 stalls** (≥45 min on either the stage- or output-equation
  closure): do NOT ship a sorry-scaffolded version. Pivot to **Plan
  B**: ship ONLY P1 (`RKTableau.inverse` definition) plus three
  trivial `@[simp]` unfold lemmas:
  ```lean
  @[simp] theorem inverse_A (M : RKTableau s) (i j : Fin s) :
      M.inverse.A i j = M.A i j - M.b j := rfl
  @[simp] theorem inverse_b (M : RKTableau s) (i : Fin s) :
      M.inverse.b i = -M.b i := rfl
  @[simp] theorem inverse_c (M : RKTableau s) (i : Fin s) :
      M.inverse.c i = M.c i - ∑ j, M.b j := rfl
  ```
  plus a non-vacuity sanity `example` on `paddedEuler.inverse`.
  Sorry count remains 0; cycle scores ≥+1 on a partial deliverable.
* **If §B exceeds 90 min total**: commit whatever axiom-clean
  subset has shipped (at minimum P1). Defer P3/P4/P5/P6 to cycle
  221. Update `lean_status.json` accordingly (`thm:382B` stays
  `unformalized` if only P1 lands; `partial` if P3 lands but P4
  doesn't; `formalized` only when both absorption laws + their
  quotient lifts are shipped).
* **Do not ship anything that breaks cycle 218/219 verification.**
  Re-run `lean_verify` on:
  - `OpenMath.Chapter3.Section312.RKTableau.id`
  - `OpenMath.Chapter3.Section312.RKTableau.composeQ_id_left`
  - `OpenMath.Chapter3.Section312.RKTableau.composeQ_id_right`
  - `OpenMath.Chapter3.Section312.RKTableau.composeQ_eq_of_equivalent`
  before commit. All must remain `[propext, Classical.choice, Quot.sound]`.

---

## §G — Housekeeping at end of cycle

* `extraction/formalization_data/lean_status.json` — update
  `thm:382B` row's `lean_file` to `OpenMath/Chapter3/Section381.lean`,
  `lean_symbol` to `OpenMath.Chapter3.Section312.RKTableau.composeQ_inverse_right`
  (or `compose_inverse_equivalent` if only P3 lands), and `status`
  per the abort thresholds above.
* `plan.md` — bump `thm:382B` row from `[ ]` to `[x]` (if both
  absorption laws + quotient lifts ship) or `[~]` (if partial).
* `.prover-state/task_results/cycle_220.md` — document deliverables,
  any pre-flagged risks that fired, and the cycle 221 outlook.
  Cycle 221+ outlook: §382 associativity at `Equivalent` level
  (cycle 219 update to `compose_assoc_HEq_plumbing.md` already
  scopes this — abstract-N-level `Equivalent`-form
  `compose_equivalent_compose_assoc` plus `Quotient.inductionOn₃`
  + `Quotient.sound` lift). Then cycle 222 packages all four
  axioms into `instance : Group (Quotient Equivalent.setoidSigma)`.
* GPFS smoke test result appended to
  `.prover-state/issues/cycle_182_gpfs_slowness.md` (one line:
  cycle 220 — 37th consecutive timeout, EXIT=124).

---

## §H — Quick reference (load-bearing predecessors)

| Lemma | Location | Used in |
|---|---|---|
| `compose_isRKOneStep_iff` (cycle 214) | line ~2670 | P3, P4 |
| `equivalent_self` (cycle 203) | line 1802 | P3, P4 |
| `id_isRKOneStep_iff` (cycle 219) | line 2812 | P3, P4 |
| `compose_id_equivalent` (cycle 219, template) | line 2837 | P3, P4 proof shape |
| `composeQ` (cycle 218) | line ~2769 | P5 |
| `Equivalent.setoidSigma.{u}` (cycle 212) | line 1932 | P5 |
| `Quotient.sound` | Mathlib | P5 |

The proof shape for P3 mirrors `compose_id_equivalent` line 2837
verbatim with `RKTableau.id` swapped for `M.inverse` and
`id_isRKOneStep_iff` (used for the right-side reduction) replaced
by the new P2 lemma `inverse_isRKOneStep_of_isRKOneStep` plus
`equivalent_self M.inverse` for uniqueness. Cycle 219's P3 closed in
<10 min via this pattern; cycle 220 P3 should be similar once P2
lands.

---

## §I — What NOT to try

* **Do NOT attempt the textbook's P-reducibility proof.** Butcher's
  §382 proof of `thm:382B` shows the composite is P-reducible to a
  method with `b = 0`. This requires building a partition witness,
  applying `pReduced`, then showing equivalence to identity. ~3×
  the LOC of the abstract-N-level route and depends on
  `IsPReducibleVia` infrastructure that's tangential to cycle 220's
  scope. Use the `compose_isRKOneStep_iff` + `equivalent_self`
  route prescribed in §B.
* **Do NOT try to define `inverse` as `c_i := -c_i + 1` or any
  alternative formula.** Cycle 174 documented the failure mode of
  "simplifying" textbook formulas; stick literally to
  `c_i − ∑ j, b_j`. Even if `c_i − 1 = c_i − ∑ b_j` under
  preconsistency, the literal Butcher formula is the textbook one.
* **Do NOT route through `M.inverse.inverse = M` if it doesn't fall
  out trivially.** Use the symmetric helper instead (§C.4).
* **Do NOT add `[NeZero s]` or `0 < s` hypotheses.** The textbook
  formula works for `s = 0` (vacuously — `RKTableau 0` has no
  stages, `M.inverse` is also a 0-stage tableau, and the composite
  `M.compose M.inverse : RKTableau (0 + 0) = RKTableau 0` should be
  `Equivalent` to `RKTableau.id` trivially via the cycle 219
  identity-element infrastructure). If `s = 0` makes any proof
  awkward, that's a sign the proof isn't going through correctly,
  not that we should add a hypothesis.
* **Do NOT poll Aristotle** — no submissions are in flight, and
  the §382 inverse construction is a 60-90 min targeted manual
  proof, not an Aristotle-shaped problem.
* **Do NOT cherry-pick a different theorem.** §382's inverse is the
  natural follow-on to cycle 219's identity per the cycle 218/219
  outlooks. Do not pivot to a different §382 / §383 / §388 entity
  unless §A indicates a real GPFS recovery.

---

## §J — Recommended invocation sequence

1. (≤6 min) §A GPFS smoke test → append timeout to issue file.
2. (≤5 min) Pre-flight `lean_local_search` for `Finset.sum_neg`
   variant names per R1.
3. (≤10 min) Ship P1 (`RKTableau.inverse` def). Verify via
   `lean_verify` after compile.
4. (30 min) Ship P2 (`inverse_isRKOneStep_of_isRKOneStep`). Use
   the §C.1 / §C.2 closure recipes; if `abel` / `module` /
   `linear_combination` fails, decompose to per-term manipulation
   via cycle 207's `pReduced_equivalent` pattern.
5. (15 min) Ship P3 (`compose_inverse_equivalent`). Match cycle
   219's `compose_id_equivalent` proof shape verbatim with the
   M.inverse substitution.
6. (15 min) Ship P4 (`isRKOneStep_of_inverse_isRKOneStep` helper +
   `inverse_compose_equivalent`).
7. (5 min) Ship P5 (`composeQ_inverse_left`, `composeQ_inverse_right`).
8. (5 min) Ship P6 (paddedEuler non-vacuity examples).
9. (10 min) Housekeeping §G.

Target total: ~90 min for the full deliverable. Plan B fallback
(P1 only + simp lemmas + sanity) is achievable in 30 min.
