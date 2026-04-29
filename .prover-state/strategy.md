# Cycle 033 Strategy — Prove `thm:357C` (algebraic stability ⇒ BN-stability)

## Target

**`thm:357C` — Algebraic stability ⇒ BN-stability (Burrage–Butcher).**

This is the natural §357 follow-up to cycles 028 (`def:357B` algebraic
stability) and 032 (`def:357A` BN-stability). Both predicates and the
`IsRKOneStepNonAut` infrastructure are in place; the theorem connecting
them is the next item in the §356–§357 stability chain.

Statement to prove:

```lean
theorem algebraicallyStable_isBNStable
    {s : ℕ} (M : RKTableau s) (hAS : IsAlgebraicallyStable M) :
    IsBNStable M
```

Place this in `OpenMath/Chapter3/Section357.lean` directly after
`implicitMidpoint_isBNStable`.

## CRITICAL — settle the predicate-form question FIRST

The cycle 032 task results recommended this target with a caveat:
> *Caveat*: requires the two-solution form (357a) of dissipativity,
> not (357c). A faithful formalisation would either (a) add a parallel
> `IsBNStable_pair` predicate ... or (b) generalise the existing
> `IsBNStable` ...

**This caveat is wrong. Do NOT add `IsBNStable_pair`.** Re-read the
textbook `proof_text` in
`extraction/formalization_data/entities/thm_357C.json`. Butcher's proof
uses the **single-trajectory** form throughout:

* The "dissipativity" he uses is `⟨Yᵢ, Fᵢ⟩ ≤ 0` where
  `Fᵢ = f(xₙ₋₁ + cᵢh, Yᵢ)` — i.e. the (357c) condition applied at the
  stage values, NOT the two-solution (357a) form.
* The textbook statement of `thm:357C` is verbatim "If a Runge–Kutta
  method is algebraically stable then it is BN-stable" — and BN-stability
  (`def:357A`) is by definition the (357c) single-trajectory condition.
* The two-solution form `‖yₙ - zₙ‖ ≤ ‖yₙ₋₁ - zₙ₋₁‖` belongs to
  *B-stability* (a different concept that Butcher treats separately).

So use the existing `IsBNStable` predicate from `Section357.lean:109` —
no new `IsBNStable_pair` infrastructure. This keeps cycle 033 in scope.

## Mathematical proof (corrected derivation)

Given algebraic stability of `M` (i.e. `∀ i, 0 < b i` and
`(symplecticityMatrix M).PosSemidef`), and given `IsRKOneStepNonAut`
yielding stage values `Y : Fin s → N`, set
`Fᵢ := f(x₀ + cᵢ * h, Y i)`. The key algebraic identity is:

```
‖y₁‖² - ‖y₀‖² = 2 h Σᵢ bᵢ ⟨Fᵢ, Yᵢ⟩ - h² Σᵢⱼ mᵢⱼ ⟨Fᵢ, Fⱼ⟩          (★)
```

where `mᵢⱼ = (symplecticityMatrix M) i j = bᵢ aᵢⱼ + bⱼ aⱼᵢ - bᵢ bⱼ`.

### Derivation of (★) — follow this path exactly

I worked through this in detail; **the only correct path is below**.
Do NOT take shortcuts (a "Form A" derivation that skips the `mᵢⱼ`
reshuffle does NOT close the proof — both terms appear `≤ 0` only
when (★) is in its `mᵢⱼ` form).

1. **Polarization identity** in a real inner-product space:
   `‖a‖² - ‖b‖² = ⟨a + b, a - b⟩`. Search Mathlib first
   (`lean_loogle "‖_‖^2 - ‖_‖^2 = inner _ _"` /
   `lean_local_search "norm_sq_sub_norm_sq"`); if absent, prove inline
   using `real_inner_self_eq_norm_sq`, `inner_add_left`, `inner_sub_right`,
   `real_inner_comm`, `ring`.

2. **Update equation in subtractive form**: `y₁ - y₀ = h • ∑ⱼ bⱼ • Fⱼ`.

3. **Sum form for `y₀ + y₁` indexed by stage `i`**: from
   `Yᵢ = y₀ + h ∑ⱼ aᵢⱼ Fⱼ` (stage) and `y₁ = y₀ + h ∑ⱼ bⱼ Fⱼ` (update),
   `y₀ = Yᵢ - h ∑ⱼ aᵢⱼ Fⱼ` and
   `y₁ = Yᵢ + h ∑ⱼ (bⱼ - aᵢⱼ) Fⱼ`, hence
   `y₁ + y₀ = 2 Yᵢ + h ∑ⱼ (bⱼ - 2 aᵢⱼ) Fⱼ`.   (Holds for *every* `i`.)

4. **Combine via inner-product expansion**:
   `‖y₁‖² - ‖y₀‖² = ⟨y₁ + y₀, y₁ - y₀⟩` (step 1)
   `              = ⟨y₁ + y₀, h ∑ᵢ bᵢ Fᵢ⟩` (step 2)
   `              = h ∑ᵢ bᵢ ⟨Fᵢ, y₁ + y₀⟩` (real_inner_comm + linearity)
   `              = h ∑ᵢ bᵢ ⟨Fᵢ, 2 Yᵢ + h ∑ⱼ (bⱼ - 2 aᵢⱼ) Fⱼ⟩` (step 3)
   `              = 2 h ∑ᵢ bᵢ ⟨Fᵢ, Yᵢ⟩
                    + h² ∑ᵢⱼ bᵢ (bⱼ - 2 aᵢⱼ) ⟨Fᵢ, Fⱼ⟩`
   `              = 2 h ∑ᵢ bᵢ ⟨Fᵢ, Yᵢ⟩
                    - h² ∑ᵢⱼ (2 bᵢ aᵢⱼ - bᵢ bⱼ) ⟨Fᵢ, Fⱼ⟩`.

5. **Symmetrise via `⟨Fᵢ, Fⱼ⟩ = ⟨Fⱼ, Fᵢ⟩`**:
   `∑ᵢⱼ (2 bᵢ aᵢⱼ - bᵢ bⱼ) ⟨Fᵢ, Fⱼ⟩ = ∑ᵢⱼ (bᵢ aᵢⱼ + bⱼ aⱼᵢ - bᵢ bⱼ) ⟨Fᵢ, Fⱼ⟩
                                    = ∑ᵢⱼ mᵢⱼ ⟨Fᵢ, Fⱼ⟩`.

   (Use `Finset.sum_comm` to swap `i ↔ j` indices on the `2 bᵢ aᵢⱼ` term;
   half goes one way, half the other, giving the symmetric `bᵢ aᵢⱼ +
   bⱼ aⱼᵢ`.)

This yields (★) above.

### Concluding `‖y₁‖² ≤ ‖y₀‖²`

From (★):

* **First term** `2 h ∑ᵢ bᵢ ⟨Fᵢ, Yᵢ⟩ ≤ 0`: by dissipativity
  (`⟨Fᵢ, Yᵢ⟩ = ⟨f(x₀+cᵢh, Yᵢ), Yᵢ⟩ ≤ 0`) and `bᵢ > 0`, `h > 0`.
* **Second term** `-h² ∑ᵢⱼ mᵢⱼ ⟨Fᵢ, Fⱼ⟩ ≤ 0`: by PSD of `M`,
  `∑ᵢⱼ mᵢⱼ ⟨Fᵢ, Fⱼ⟩ ≥ 0`, so its `-h²·(·) ≤ 0`.

Sum is `≤ 0`, hence `‖y₁‖² ≤ ‖y₀‖²`, hence `‖y₁‖ ≤ ‖y₀‖` via the
existing private `norm_le_of_norm_sq_le` from cycle 032.

## Implementation plan — three lemmas + one theorem

Add to `OpenMath/Chapter3/Section357.lean`, after
`implicitMidpoint_isBNStable`. Keep the existing `private` lemmas from
cycle 032 untouched.

### Lemma 1 — symmetrisation of `mᵢⱼ` quadratic form

```lean
private lemma symplecticityMatrix_quadratic_form_eq {s : ℕ}
    (M : RKTableau s) {N : Type*}
    [NormedAddCommGroup N] [InnerProductSpace ℝ N]
    (F : Fin s → N) :
    ∑ i, ∑ j, (2 * M.b i * M.A i j - M.b i * M.b j) *
        inner ℝ (F i) (F j)
    = ∑ i, ∑ j, symplecticityMatrix M i j * inner ℝ (F i) (F j) := by
  sorry
```

Proof sketch:
* Unfold `symplecticityMatrix M i j` to
  `M.b i * M.A i j + M.b j * M.A j i - M.b i * M.b j` (via
  `Matrix.diagonal`, `Matrix.vecMulVec`, `Matrix.mul_apply` simp set
  used in cycle 027/028).
* Split `2 * M.b i * M.A i j = M.b i * M.A i j + M.b i * M.A i j`.
* On the second copy, use `Finset.sum_comm` to swap `i, j`, then
  `real_inner_comm (F j) (F i)` to convert `⟨Fᵢ, Fⱼ⟩` to `⟨Fⱼ, Fᵢ⟩`
  (which after relabelling is `⟨Fᵢ, Fⱼ⟩` again — the swap relabels the
  inner product back). The result is `M.b j * M.A j i * ⟨Fⱼ, Fᵢ⟩` after
  swapping, i.e. `M.b j * M.A j i * ⟨Fᵢ, Fⱼ⟩` after `real_inner_comm`.

### Lemma 2 — algebraic identity (★)

```lean
private lemma bn_stability_identity {s : ℕ}
    (M : RKTableau s) {N : Type*}
    [NormedAddCommGroup N] [InnerProductSpace ℝ N]
    (h : ℝ) (y₀ y₁ : N) (Y : Fin s → N) (F : Fin s → N)
    (hY_stage : ∀ i, Y i = y₀ + h • ∑ j, M.A i j • F j)
    (hy_update : y₁ = y₀ + h • ∑ i, M.b i • F i) :
    ‖y₁‖^2 - ‖y₀‖^2
      = 2 * h * (∑ i, M.b i * inner ℝ (F i) (Y i))
      - h^2 * (∑ i, ∑ j, symplecticityMatrix M i j *
                          inner ℝ (F i) (F j)) := by
  sorry
```

Proof outline (follow the 5-step derivation above). This is the
algebraic heart of the proof.

* Steps 1–4 are pure inner-product manipulation: `inner_sum`,
  `inner_smul_left`/`right` (use the `real_inner_*` variants to avoid
  `starRingEnd ℝ` artifacts — the cycle 032 dead-end), `Finset.sum_add_distrib`,
  `Finset.mul_sum`, `Finset.sum_mul`. End with a call to Lemma 1.
* If `lean_multi_attempt` struggles on the full chain, decompose
  further into:
  * Sub-lemma 2a: `y₁ + y₀ = 2 • Y i + h • ∑ⱼ (M.b j - 2 * M.A i j) • F j`
    for every `i` (one-line algebra from `hY_stage i` + `hy_update`).
  * Sub-lemma 2b: `‖y₁‖^2 - ‖y₀‖^2 = inner ℝ (y₁ + y₀) (y₁ - y₀)`
    (polarization, likely already in Mathlib).
* **Worst case**: if Lemma 2 doesn't close in ~2 hours of manual work,
  leave it as a `sorry` and submit to Aristotle. It's pure algebra in
  a real inner-product space — Aristotle should handle it.

### Lemma 3 — PSD bilinear form is non-negative on inner-product values

```lean
private lemma posSemidef_inner_form_nonneg {s : ℕ}
    {M : Matrix (Fin s) (Fin s) ℝ} (hM : M.PosSemidef)
    {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℝ N]
    (F : Fin s → N) :
    0 ≤ ∑ i, ∑ j, M i j * inner ℝ (F i) (F j) := by
  sorry
```

Proof strategy options (try in order, pick the first that works):

1. **Cholesky / `posSemidef_iff_eq_transpose_mul_self` route.** Search
   Mathlib first:
   ```
   lean_local_search "PosSemidef" → look for decomposition
   lean_loogle "Matrix.PosSemidef _ → ∃ _, _ = _ᵀ * _"
   ```
   The relevant file is `Mathlib/Analysis/Matrix/Order.lean` (which has
   the CFC `sqrt` machinery — see lines 110–141 in pinned Mathlib).
   `Matrix.PosSemidef.sqrt` is deprecated in favour of `CFC.sqrt`, and
   the lemma `CFC.sqrt_mul_sqrt_self : sqrt A * sqrt A = A` gives the
   factorization.
   * If `B := CFC.sqrt M`, then `M = B * B` (B is symmetric/Hermitian).
   * `∑ᵢⱼ Mᵢⱼ ⟨Fᵢ, Fⱼ⟩ = ∑ᵢⱼₖ Bᵢₖ Bₖⱼ ⟨Fᵢ, Fⱼ⟩`. Re-arrange to
     `∑ₖ ⟨∑ᵢ Bᵢₖ Fᵢ, ∑ⱼ Bₖⱼ Fⱼ⟩`. Since `B` is symmetric (Hermitian
     real), `Bᵢₖ = Bₖᵢ`, so this is `∑ₖ ‖∑ᵢ Bₖᵢ Fᵢ‖² ≥ 0`.

2. **`posSemidef_iff_dotProduct_mulVec` + orthonormal-basis route.** If
   the Cholesky route is too painful in Lean, fall back to:
   `Matrix.posSemidef_iff_dotProduct_mulVec` (line 290 of `PosDef.lean`)
   gives `∀ v : Fin s → ℝ, 0 ≤ Matrix.dotProduct v (M.mulVec v)`. Pick
   an orthonormal basis `{eₖ}` of `Submodule.span ℝ (Set.range F)`
   (finite-dimensional!), expand `Fᵢ = ∑ₖ ⟨Fᵢ, eₖ⟩ eₖ`, then
   `∑ᵢⱼ Mᵢⱼ ⟨Fᵢ, Fⱼ⟩ = ∑ₖ ∑ᵢⱼ Mᵢⱼ ⟨Fᵢ, eₖ⟩ ⟨Fⱼ, eₖ⟩
                       = ∑ₖ vₖᵀ M vₖ ≥ 0`
   where `vₖ i := ⟨Fᵢ, eₖ⟩`. Slightly more work but no CFC dependency.

3. **Aristotle batch fallback**: submit Lemma 3 with a sorry. The fact
   "PSD matrix + inner-product expansion ≥ 0" is a standard
   linear-algebra lemma; Aristotle may close it directly.

### Theorem — `algebraicallyStable_isBNStable`

```lean
theorem algebraicallyStable_isBNStable
    {s : ℕ} (M : RKTableau s) (hAS : IsAlgebraicallyStable M) :
    IsBNStable M := by
  intro N _ _ f hDiss x₀ y₀ h hh y₁ hStep
  obtain ⟨Y, hY_stage, hy_update⟩ := hStep
  obtain ⟨hb_pos, hM_psd⟩ := hAS
  -- Define F i := f (x₀ + c i * h) (Y i).
  set F : Fin s → N := fun i => f (x₀ + M.c i * h) (Y i) with hF_def
  -- Stage and update equations in F-form.
  have hY_stage' : ∀ i, Y i = y₀ + h • ∑ j, M.A i j • F j := hY_stage
  have hy_update' : y₁ = y₀ + h • ∑ i, M.b i • F i := hy_update
  -- Apply Lemma 2 (algebraic identity).
  have hIdentity := bn_stability_identity M h y₀ y₁ Y F hY_stage' hy_update'
  -- First term ≤ 0 by dissipativity + bᵢ > 0 + h > 0.
  have hFirst : 2 * h * (∑ i, M.b i * inner ℝ (F i) (Y i)) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 2 * h)
    apply Finset.sum_nonpos
    intro i _
    apply mul_nonpos_of_nonneg_of_nonpos (hb_pos i).le
    -- ⟨F i, Y i⟩ = ⟨f(x₀ + cᵢh, Y i), Y i⟩ ≤ 0 by dissipativity
    simpa [F, hF_def] using hDiss (x₀ + M.c i * h) (Y i)
  -- Second term: PSD of M ⇒ inner-product quadratic form ≥ 0.
  have hSecond : 0 ≤ ∑ i, ∑ j, symplecticityMatrix M i j *
                       inner ℝ (F i) (F j) :=
    posSemidef_inner_form_nonneg hM_psd F
  -- Combine: ‖y₁‖² - ‖y₀‖² ≤ 0.
  have hbound : ‖y₁‖^2 ≤ ‖y₀‖^2 := by
    have h2_nonneg : 0 ≤ h^2 := sq_nonneg h
    nlinarith [hIdentity, hFirst, hSecond, h2_nonneg,
               mul_nonneg h2_nonneg hSecond]
  exact norm_le_of_norm_sq_le y₁ y₀ hbound
```

If `nlinarith` doesn't close the final step, do it manually:
```
have hsecond_neg : -(h^2 * (∑ i, ∑ j, ...)) ≤ 0 := by
  rw [neg_nonpos]
  exact mul_nonneg (sq_nonneg h) hSecond
linarith [hIdentity, hFirst, hsecond_neg]
```

## Pre-flight Mathlib search list

Before writing Lemma 2 and Lemma 3 proofs, do these searches and
record results in scratch:

* `lean_local_search "norm_sq_sub_norm_sq"` — for the polarization
  identity `‖a‖² - ‖b‖² = ⟨a + b, a - b⟩`.
* `lean_loogle "‖_‖ ^ 2 - ‖_‖ ^ 2"` — alternative forms.
* `lean_local_search "PosSemidef"` in `Mathlib/LinearAlgebra/Matrix/PosDef.lean`
  and `Mathlib/Analysis/Matrix/Order.lean` — for the decomposition.
* `lean_local_search "posSemidef_iff_dotProduct"` — for the bilinear
  form characterisation.
* `lean_loogle "Matrix.PosSemidef _ → ∃ _, _ * _ = _"` — for Cholesky.
* `lean_loogle "Matrix.diagonal _ * _"` and
  `lean_loogle "Matrix.vecMulVec"` — for unfolding the symplecticity
  matrix entry formula (likely the same simp set used in cycle 027/028).

## What NOT to try

* Do **NOT** add an `IsBNStable_pair` predicate. The cycle 032 task
  results' caveat about needing the (357a) two-solution form is wrong
  — the textbook proof uses (357c) single-trajectory throughout. See
  the "CRITICAL" section above.
* Do **NOT** restate `def:357A` as the matrix condition. That would be
  definition smuggling; `def:357A` is the semantic norm-non-increase
  condition (already correct in `Section357.lean:109`).
* Do **NOT** introduce `axiom` or `constant` for the PSD-bilinear-form
  bridge (Lemma 3). Mathlib has the tools (CFC `sqrt`, or
  `dotProduct_mulVec` characterisation). If after searching you cannot
  find a clean path, **decompose Lemma 3 into a smaller sub-lemma and
  submit to Aristotle** — do not axiomatise.
* Do **NOT** raise `maxHeartbeats` above 200000 if the algebraic
  identity (Lemma 2) blows up. Decompose into smaller sub-lemmas
  instead.
* Do **NOT** compute `y₁ + y₀ = 2 Yᵢ - h ∑ⱼ bⱼ Fⱼ`. That is wrong; the
  correct expression is `2 Yᵢ + h ∑ⱼ (bⱼ - 2 aᵢⱼ) Fⱼ`. The first form
  comes from confusing `y₁ - y₀` with `y₁ + y₀` mid-derivation. Do the
  derivation per step 3 of the recipe above and double-check the
  signs.
* Do **NOT** use `inner_smul_left` / `inner_smul_right` (without
  `real_`) — they generate `starRingEnd ℝ h` terms that `ring` cannot
  close. Always use `real_inner_smul_left` / `real_inner_smul_right`
  (cycle 032 dead-end).
* Do **NOT** modify `scripts/autonomous_loop.py` (loop-infrastructure
  rule from cycles 014–015).
* Do **NOT** modify the existing `IsBNStable`, `IsAlgebraicallyStable`,
  `IsRKOneStepNonAut`, `IsRKOneStep`, `symplecticityMatrix`, or
  `implicitMidpoint` definitions. They are correct and committed.
* Do **NOT** re-prove `implicitMidpoint_isBNStable` or
  `implicitMidpoint_isAlgebraicallyStable`. Both are already complete
  from cycles 028/032; reuse them as-is.

## Aristotle batch plan

If after ~30 minutes of manual work the proof is still incomplete,
submit the following ~5 sorry'd lemmas to Aristotle in a single batch
(per CLAUDE.md "Aristotle-first" rule):

1. `bn_stability_identity` (Lemma 2) — the algebraic identity.
2. `symplecticityMatrix_quadratic_form_eq` (Lemma 1) — the
   symmetrisation.
3. `posSemidef_inner_form_nonneg` (Lemma 3) — the PSD bridge.
4. (If decomposed) sub-lemma 2a: `y₁ + y₀ = 2 • Y i + h • ∑ⱼ ...` for
   every `i`.
5. (If decomposed) the polarization identity `‖a‖² - ‖b‖² = ⟨a+b, a-b⟩`
   if not already in Mathlib.

Sleep 30 min once submitted, check, incorporate, fix partials.

## Faithfulness check (must pass before commit)

Per CLAUDE.md "Pre-Commit Faithfulness Checklist":

* **Tautology check**: conclusion `IsBNStable M` is NOT verbatim a
  hypothesis. Hypothesis is `IsAlgebraicallyStable M` — distinct
  predicate. ✓
* **Identity check**: proof body must contain the algebraic identity
  work (Lemmas 1–3). The closer must NOT be a single `exact hAS` or
  similar trivial closer. ✓ by construction.
* **Hypothesis-strength check**: hypotheses are exactly
  `IsAlgebraicallyStable M`. No extra smoothness, no extra positivity
  beyond what `IsAlgebraicallyStable` already provides. ✓
* **Quoted textbook statement** (from `thm_357C.json:12`):
  > If a Runge–Kutta method is algebraically stable then it is
  > BN-stable.
  Lean statement: `IsAlgebraicallyStable M → IsBNStable M`. **Same
  content.** ✓
* **Definition smuggling check**: BN-stability is the semantic
  norm-non-increase predicate (`def:357A`); algebraic stability is the
  matrix condition (`def:357B`). The theorem proves the second is
  sufficient for the first — a real implication, not a tautology. ✓
* **Promised sorry check**: any helper lemma left as a `sorry` after
  Aristotle batch must be explicitly mentioned in `cycle_033.md` (and,
  if blocking, in an issue file). No silent sorrys.

## Bookkeeping (after proof compiles cleanly)

1. Run `lake env lean OpenMath/Chapter3/Section357.lean` — must be
   clean.
2. Run `lake build` — should still hit 2845/2845 (no new files).
3. `#print axioms OpenMath.Chapter3.Section357.algebraicallyStable_isBNStable`
   — must be `[propext, Classical.choice, Quot.sound]`.
4. Update `extraction/formalization_data/lean_status.json`:
   `thm:357C → formalized` with symbol path
   `OpenMath.Chapter3.Section357.algebraicallyStable_isBNStable`.
5. Update `plan.md`: 33 / 175 → 34 / 175, mark `thm:357C` row as `[x]`.
6. Write `cycle_033.md` task results per the standard format.
7. Commit and push.

## If blocked

If after the full cycle (Aristotle batch + manual proof attempts) the
theorem cannot be closed completely, write
`.prover-state/issues/thm_357C_blocked.md` documenting:

* Which of Lemmas 1, 2, 3 closed and which did not.
* What Aristotle returned (success / partial / failure for each).
* Which Mathlib API was searched and what was missing.
* Concrete suggestions for the next cycle (e.g. "Lemma 3 needs a real
  Cholesky decomposition, which Mathlib's CFC `sqrt` provides over ℂ
  but requires a small bridge for ℝ; build that bridge in cycle 034").

Even a partial result (e.g. Lemmas 1 and 2 proved, Lemma 3 sorried) is
acceptable progress — the file should still compile cleanly with the
sorry visible. Document it explicitly.

The forbidden outcomes are:
* A cycle with zero changes.
* A silently-sorried lemma not mentioned in `cycle_033.md`.
* An axiomatised PSD bridge.
* Modifying any existing definition (`IsBNStable`,
  `IsAlgebraicallyStable`, `IsRKOneStepNonAut`, `symplecticityMatrix`,
  `implicitMidpoint`).
