# Cycle 346 Results

## Worked on

PRIMARY, SECONDARY, and STRETCH all shipped, all axiom-clean.

- **PRIMARY** (Section451.lean: +65 LOC after `bdf2LMM_isGStable`):
  - `bdf2_solution_decomp` (private): every solution of BDF2's
    homogeneous recurrence decomposes as
    `Y_n = A + B · (1/3)^n` with `A := (3 Y₁ - Y₀)/2`,
    `B := (3(Y₀ - Y₁))/2`.
  - `bdf2LMM_isStable : bdf2LMM.IsStable` (the Dahlquist
    zero-stability of BDF2 from `OpenMath/Chapter4/Section404.lean:202`).
- **SECONDARY** (Section422.lean: +37 LOC after cycle 345's
  consolidation block):
  - `coef_β_nonneg_of_β_nonneg`: general helper, `(∀ i, 0 ≤ M.β i) ⇒
    0 ≤ Σ i.val · M.β i`.
  - `bdf2LMM_β_nonneg`: `fin_cases` + `simp [bdf2LMM]` + `norm_num`.
  - `bdf2LMM_coef_β_nonneg`: trivial composition.
- **STRETCH** (Section422.lean: +27 LOC, closing cycle 345's
  BDF2 non-vacuity deferral):
  - `example` showing that under `Eq422a bdf2LMM η_q`, the
    quotient-level elementary weight `Φ_η(τ) = 1`. Numerical
    sanity: `coef_α = 2/3`, `coef_β = 0`, `sum_β = 2/3`, so
    `(2/3)/(2/3 + 0) = 1`.

Final counts: Section422 759→864→**931** LOC; Section451
242→**307** LOC. Sorry count both files: **0**.

## Approach

Followed the cycle 346 strategy verbatim.

### PRIMARY (Section451.lean)

Wrote `bdf2_solution_decomp` by strong induction on `n` with
`match` on the motive (the cleaner branch from the strategy's
pre-flight #2). Three sub-steps:

1. Extracted a clean recurrence `hrec : ∀ m, Y (m+2) = (4/3)·Y(m+1) +
   (-1/3)·Y m` via `simp [bdf2LMM, Fin.sum_univ_two]` on `hY m`.
   (The strategy's explicit `show (m+2-(0+1):ℕ) = m+1` `simp`
   lemmas turned out unnecessary — `simp` (non-`only`) already
   evaluates the `match Fin.succ _` patterns AND simplifies the
   `Nat` subtractions in one pass. Strategy ihad `simp only` plus
   the `show` lemmas; I tried that first, it left `match Fin.succ 0`
   unreduced, swapped to `simp` (non-`only`), one line.)
2. Strong induction with `match n, ih with`:
   * `| 0, _ => simp; ring` (LHS = `Y 0`, RHS pow at `0` is `1` ⇒
     trivial algebra).
   * `| 1, _ => simp; ring` (LHS = `Y 1`, RHS pow at `1` is `1/3` ⇒
     `(3Y₁-Y₀)/2 + (3(Y₀-Y₁))/2·(1/3) = (3Y₁-Y₀)/2 + (Y₀-Y₁)/2 = Y₁`).
   * `| n+2, ih => rw [hrec n, ih (n+1) (by omega), ih n (by omega)]; ring`.

Then `bdf2LMM_isStable` consumes the decomposition:

```
|Y_n| = |(3Y₁-Y₀)/2 + (3(Y₀-Y₁))/2·(1/3)^n|
      ≤ |(3Y₁-Y₀)/2| + |(3(Y₀-Y₁))/2·(1/3)^n|   -- abs_add_le
      = |(3Y₁-Y₀)/2| + |(3(Y₀-Y₁))/2|·|(1/3)^n| -- abs_mul
      ≤ |(3Y₁-Y₀)/2| + |(3(Y₀-Y₁))/2|·1         -- pow_le_one₀
      = |(3Y₁-Y₀)/2| + |(3(Y₀-Y₁))/2|.
```

The `gcongr` tactic handled the monotone step; `pow_le_one₀` from
the strategy's name list fired cleanly (verified via `lean_loogle`
that it lives in `Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic`).

Strategy named `abs_add`; the actual Mathlib name (verified via
loogle) is `abs_add_le`. Substituted.

### SECONDARY (Section422.lean)

Verbatim from the strategy. One minor adjustment for the
`bdf2LMM_β_nonneg` proof: the strategy's
`fin_cases i <;> simp [bdf2LMM] <;> norm_num` triggered an
`unnecessarySeqFocus` linter warning (some sub-goals were closed
by `simp` alone, leaving `norm_num` with no goals). Swapped to:

```
fin_cases i
all_goals simp [...bdf2LMM]
all_goals try norm_num
```

— clean compile, no warnings.

### STRETCH (Section422.lean)

Built atop SECONDARY exactly as the strategy proposed. Final
`simp [bdf2LMM, Fin.sum_univ_two, Fin.sum_univ_three]; norm_num`
closes the numerical reduction.

## Result

**SUCCESS** — all three deliverables compiled and axiom-checked
clean.

### Build

* `lake env lean OpenMath/Chapter4/Section451.lean` — clean.
* `lake env lean OpenMath/Chapter4/Section422.lean` — clean.
* `lake build OpenMath.Chapter4.Section422` — full chain rebuilds
  cleanly (8037 jobs). Section441 rebuilt as part of the chain
  (266s) — this contradicts the strategy's note about
  Section441 GPFS-blocked timeouts. Possibly the GPFS situation
  improved, or the supervisor's `lake build` benefits from a warm
  cache that `lake env lean` per-file checks do not.

### Axioms

```
'OpenMath.Chapter4.Section451.bdf2LMM_isStable' : [propext, Classical.choice, Quot.sound]
'OpenMath.Chapter4.Section422.coef_β_nonneg_of_β_nonneg' : [propext, Classical.choice, Quot.sound]
'OpenMath.Chapter4.Section422.bdf2LMM_β_nonneg' : [propext, Classical.choice, Quot.sound]
'OpenMath.Chapter4.Section422.bdf2LMM_coef_β_nonneg' : [propext, Classical.choice, Quot.sound]
```

### Sorry / tautology scans

* `grep -c sorry` on both files: 0 / 0.
* `:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$` regex: no hits.

## Faithfulness check

### `bdf2_solution_decomp` (private, Section451.lean:262)

- Entity ID: none — this is an internal helper, not a textbook
  entity.
- Mathematical claim: closed-form solution of the homogeneous
  BDF2 recurrence with characteristic roots `1` and `1/3`. The
  derivation matches Butcher §403's general theory of linear
  multistep schemes via characteristic polynomials.
- Lean statement captures: the unique explicit decomposition
  `Y_n = A + B · (1/3)^n` that is forced by `Y₀` and `Y₁` —
  matches textbook content.

### `bdf2LMM_isStable` (Section451.lean:287)

- Entity ID: none — this is a witness for `IsStable` (Butcher
  §403, Definition 403A, p. 341, cycle 270's
  `def:403A` in `Section404.lean:202`), not a textbook theorem
  in its own right.
- Lean statement (`bdf2LMM.IsStable`) is literally the
  textbook predicate applied to BDF2.
- Hypothesis strength: none (no extra hypotheses).
- The proof is genuinely doing the work — it derives the
  boundedness from the explicit decomposition, no
  `exact h`-style identity proofs.

### `coef_β_nonneg_of_β_nonneg` (Section422.lean:881)

- Entity ID: none — Phase D′ scaffolding helper.
- Hypothesis: `∀ i, 0 ≤ M.β i` (β-coefficient pointwise
  non-negativity). This is strictly stronger than the textbook's
  "stable + consistent" hypothesis that cycle 345's
  `Eq422a_at_vertex_eta_eq_of_stable_preconsistent` ultimately
  wants discharged. Justification: documented explicitly in the
  docstring + section header; this is a *first-step* helper, the
  full Phase D′ β-side machinery (deriving `0 ≤ coef_β` from
  stability alone, analog of cycle 178's α-side
  `ρPoly_deriv_eval_one_pos_of_stable_preconsistent`) is deferred
  per strategy `## What NOT to try` §"Phase D′ β-side machinery".

### `bdf2LMM_β_nonneg` (Section422.lean:889)

- Entity ID: none — numerical witness.
- Statement: each β-coefficient of BDF2 is non-negative.
  Matches Section451 def: `β 0 = 2/3, β 1 = β 2 = 0`, all ≥ 0.

### `bdf2LMM_coef_β_nonneg` (Section422.lean:897)

- Entity ID: none — numerical witness combining the previous two.
- Statement: `0 ≤ coef_β(bdf2LMM)`. True (in fact `= 0`).

### Stretch `example` (Section422.lean:905)

- Entity ID: none — non-vacuity example.
- Numerical claim verified: `coef_α = 2/3` (cycle 344 already
  ships this), `coef_β = 0`, `sum_β = 2/3`, so `η(τ) = 1`. The
  example asserts this conclusion as a consequence of
  `Eq422a bdf2LMM η_q` and is closed by `rw` + `simp` + `norm_num`.

## Dead ends

1. **`simp only [bdf2LMM, Fin.sum_univ_two, h1, h2]` did not
   reduce the `match Fin.succ _` patterns.** The strategy
   suggested this would work, but `simp only` doesn't unfold the
   match arm selection for `(0 : Fin 2).succ = ⟨1, …⟩ : Fin 3`.
   `simp` (non-`only`) handles both the match unfolding and the
   `Nat` subtraction normalization in one pass — the `h1`, `h2`
   `show` lemmas became unused (warning surfaced this).
2. **Strategy named `abs_add` for the triangle inequality.** Loogle
   confirms the Mathlib name is `abs_add_le` (or `_root_.abs_add`
   may exist in older Mathlib versions but didn't resolve here).
3. **`fin_cases i <;> simp [bdf2LMM] <;> norm_num` triggers
   `unnecessarySeqFocus` linter.** Some `fin_cases` branches
   close at the first `<;> simp`, so the second `<;> norm_num`
   sees an empty goal list — the linter flags this as a no-op
   composition. Fixed by splitting into `fin_cases i` followed
   by `all_goals simp …; all_goals try norm_num`.

## Discovery

* **`simp` (non-`only`) reduces both the
  `match Fin.succ _ with …` arms and the `Fin.val + 1 : ℕ`
  subtraction simultaneously** when called on a hypothesis derived
  from `LinearMultistepMethod.IsHomogeneousSolution`. This is
  much shorter than the explicit `show … = …` `simp` lemmas the
  strategy sketched. Worth remembering for future LMM recurrence
  unfolds (BDF3, Adams-Bashforth, etc.).
* **`fin_cases i <;> simp [...]` may close some branches and
  leave others open.** The standard Mathlib idiom for "split,
  simp, finish off arithmetic" without triggering
  `unnecessarySeqFocus` is `fin_cases i; all_goals simp [...]; all_goals
  try <closer>`. Worth recording for future BDF / Adams /
  Runge-Kutta numerical-witness lemmas.
* **`pow_le_one₀` is the current Mathlib name** (verified via
  loogle this cycle). The "₀" subscript distinguishes from the
  `_root_.pow_le_one` variant which requires stronger structure
  on the base type.
* **`abs_add_le` is the current Mathlib triangle-inequality lemma
  name**, not `abs_add` (which doesn't exist or is shadowed).
* **Section441 builds in 266s in the supervisor's full chain** —
  this conflicts with the strategy's note about 43+ consecutive
  GPFS-blocked timeouts. It's possible those timeouts were specific
  to `lake env lean OpenMath/Chapter4/Section441.lean` single-file
  rebuilds without warm cache. Future strategies may consider
  testing Section441 in the warm-cache `lake build` path before
  declaring it blocked.

## Suggested next approach

### Option A (recommended) — Phase D′ β-side machinery

Build the textbook bridge `M.IsStable + M.IsConsistent ⇒ 0 ≤
coef_β(M)` (the analog of cycle 178's α-side
`ρPoly_deriv_eval_one_pos_of_stable_preconsistent`). This would
eliminate the `hβ_nn` hypothesis from cycle 345's
`Eq422a_at_vertex_eta_eq_of_stable_preconsistent` and produce a
fully textbook-faithful single-hypothesis statement.

Plan sketch (multi-cycle):
1. Define `σPoly` (the β-side characteristic polynomial,
   analog of `ρPoly` in Section441) attached to a
   `LinearMultistepMethod`.
2. Bridge `coef_β(M) = σ'(1)` (analog of cycle 344's
   `coef_α_eq_ρPoly_deriv_at_one_of_preconsistent`).
3. Show `0 ≤ σ'(1)` for stable consistent `M` (analog of cycle
   178's `ρPoly_deriv_eval_one_pos_of_stable_preconsistent`).

Risk: medium. The α-side took ~4 cycles of infrastructure (175–178).
β-side is parallel but has its own subtleties (the β-vector
includes the leading coefficient, unlike α). Estimated 3–4 cycles.

### Option B — Phase D.3 inductive solver for `η : RootedTree → ℝ`

The cycle 343/344 infrastructure (`WellFoundedRelation`,
`elementaryWeightQ_phi`) is ready for the full inductive
construction. Per strategy `## What NOT to try` §Phase D.3, this
is multi-cycle HIGH-risk. Defer.

### Option C — pivot to a fresh entity

Per strategy `## What NOT to try` §"Do NOT pivot", `thm:302A`,
`thm:302B`, `thm:384A` all have known risk. Don't pivot without
strong reason.

### Option D — BDF3 / Adams-Bashforth witnesses

The infrastructure built this cycle (`bdf2_solution_decomp`
pattern, β-helpers) generalizes. BDF3 is a 3-step method with
characteristic polynomial roots `1, r, r̄` (complex conjugate
pair) — the decomposition is more involved but the same
strong-induction template applies. If Phase D′ proves too
ambitious, building one more numerical witness LMM (e.g.
Adams-Bashforth 2-step) would expand the §404 non-vacuity story
and pre-stage future §501-series convergence proofs.
