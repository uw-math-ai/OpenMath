# Cycle 075 Strategy — open §410B order-condition cluster (thm:410B + bridges)

## Situation snapshot

* Cycle 074 closed **`thm:410A`** (commit `fa8abdb`, score +2) and
  landed all of cycle 073's §410 generating-function infrastructure.
  `OpenMath/Chapter4/Section410.lean` is now ~340 LOC, 0 sorries,
  axioms `[propext, Classical.choice, Quot.sound]`. Progress
  counter at **44/175**.
* Cycle 074's task results explicitly suggest: **`thm:410B`**
  ("Order Condition for LMM"), then `C_one_eq_zero_iff_isConsistent`
  bridge, then `thm:410C` / `thm:410D`.
* No sorries anywhere in the codebase. No pending Aristotle results.
* Open issues: all are deferral notes from older cycles; none block
  this cycle.

## Cycle goal

**Open the §410B order-condition cluster** by:

1. Defining `LinearMultistepMethod.HasOrderAtLeast M p` (the
   per-coefficient predicate `∀ j ≤ p, C M j = 0`).
2. Proving the **§410↔§404 consistency bridge**
   `C_one_eq_zero_iff_isConsistent`.
3. Proving **`thm:410B`** as the generating-function reformulation:
   `M.HasOrderAtLeast p ↔ ∀ j ≤ p, (PowerSeries.coeff ℝ j) (genFn M) = 0`
   where `genFn M := aeval expNegPS αPoly - X * aeval expNegPS βPoly`.
4. Landing concrete witnesses (explicit Euler order ≥ 0, ≥ 1,
   and a `C_2 ≠ 0` non-vacuity check showing the predicate is
   genuinely restrictive).

Net deliverable: **+1 entity (thm:410B) → 45/175**, plus the
infrastructure (`HasOrderAtLeast`, `C_one_eq_zero_iff_isConsistent`,
`genFn` abbreviation) for the rest of the §410 cluster.

## Why thm:410B and not thm:410D / thm:431A / thm:422A

* **thm:410B** is the natural follow-up to thm:410A — it closes the
  loop from "C_j is the j-th coefficient" (thm:410A) to "method has
  order p iff first p+1 coefficients vanish" (thm:410B).
  Mathematically nearly trivial in our encoding (it's a packaging
  of thm:410A + a definition), so a clean 1-cycle target.
* **thm:410D** depends on thm:410B; sequencing demands 410B first.
* **thm:431A** (Schur stability for LMMs) is self-contained but
  needs Schur infrastructure (root location for polynomials with
  modulus < 1) — much heavier than the §410B packaging.
* **thm:422A** (LMM as a one-step method on ℝ^k) is heavier still
  (vector-valued one-step infrastructure + similarity to LMM
  recurrence).

`C_one_eq_zero_iff_isConsistent` is folded into this cycle as
preparatory infrastructure: §410B's witnesses (explicit Euler has
order ≥ 1) need it.

## Faithfulness framing — DO READ BEFORE CODING

Butcher (§410, p. 330, paragraph immediately preceding thm:410A):
> "this will enable us to expand (410a) in a Taylor series
>   `C₀ y(xn) + C₁ h y'(xn) + C₂ h² y''(xn) + ⋯ + Cp h^p y^(p)(xn) + ⋯`
>   (410b) and order p will mean that C₀ = C₁ = ⋯ = Cp = 0."

Then (§410, p. 331, statement of thm:410B):
> "A linear multistep method [α, β] has order p (or higher) if and
> only if `α(exp(z)) + zβ(exp(z)) = O(z^{p+1})`."

Two faithfulness observations:

1. **The textbook uses `C₀ = ⋯ = Cp = 0` as the definition of
   "order p"** (the sentence "order p will mean that C₀ = ⋯ = Cp =
   0" is definitional). The asymptotic interpretation
   `L(y, x, h) = O(h^{p+1})` is implicit via (410b)'s Taylor
   expansion but is *not* the textbook's stated definition. So
   defining `HasOrderAtLeast M p := ∀ j ≤ p, C M j = 0` matches
   Butcher's text directly. **Add a docstring quoting the textbook
   sentence + a brief note that the asymptotic interpretation is
   captured implicitly via (410b) and quantitatively via lem:406B
   for p = 1.**

2. **Sign convention.** Butcher's thm:410B uses `α(exp(z)) +
   zβ(exp(z))` (forward sign). Our §410 encoding (cycle 073/074)
   uses backward sign per def:406A:
   `α(exp(-z)) - zβ(exp(-z))`. Both encode the same mathematical
   content; the equivalence is a sign conjugation `z ↦ -z`. We
   stick with the backward convention (matches all of §404, §405,
   §406, §410A). **Add a docstring footnote explaining the sign
   discrepancy and pointing to thm:410A for the convention.**
   Do NOT introduce a forward variant in this cycle — that's a
   `thm:410C`-bridge concern.

## Concrete deliverable plan

### Deliverable D1 — `HasOrderAtLeast` definition (~25 LOC)

In `OpenMath/Chapter4/Section410.lean`, after the existing `C` and
its helpers:

```lean
/-- **Butcher §410B order predicate.**

A linear multistep method has order at least `p` if its first `p+1`
Taylor coefficients vanish: `C M j = 0` for all `j ≤ p`.

This matches Butcher's definitional statement (§410, p. 330):
"order p will mean that C₀ = C₁ = ⋯ = Cp = 0".

The asymptotic interpretation `L(y, x, h) = O(h^{p+1})` is captured
implicitly via Butcher's Taylor expansion (410b); for `p = 1` it is
captured quantitatively by `lem:406B`
(`localTruncationError_bound`, Section404.lean). Equivalence to the
generating-function form `α(exp(-z)) - zβ(exp(-z)) = O(z^{p+1})` is
the content of `thm_410B` below. -/
def LinearMultistepMethod.HasOrderAtLeast {k : ℕ}
    (M : LinearMultistepMethod k) (p : ℕ) : Prop :=
  ∀ j ≤ p, C M j = 0
```

### Deliverable D2 — `genFn` abbreviation (~10 LOC)

```lean
/-- **Generating function of an LMM.** Per Butcher (410c)
(in our backward-sign convention),
`genFn M = α(exp(-z)) - z·β(exp(-z))`. By thm_410A, the j-th formal
power-series coefficient of `genFn M` equals `C M j`. -/
noncomputable def genFn {k : ℕ} (M : LinearMultistepMethod k) :
    PowerSeries ℝ :=
  (Polynomial.aeval expNegPS) (αPoly M)
    - PowerSeries.X * (Polynomial.aeval expNegPS) (βPoly M)
```

Then refactor `thm_410A` and `thm_410A_zero` to use `genFn`:
```lean
theorem thm_410A {k : ℕ} (M : LinearMultistepMethod k) (j : ℕ) :
    (PowerSeries.coeff (R := ℝ) j) (genFn M) = C M j := …
```

(Refactor is α-equivalent — should be a one-line `unfold genFn` in
the existing proof.)

### Deliverable D3 — `C_one_eq_zero_iff_isConsistent` bridge (~50 LOC)

```lean
/-- **§410↔§404 bridge.** Under preconsistency (def:404A), the
first Taylor coefficient `C M 1` vanishes if and only if the method
satisfies (404b), i.e. is consistent (def:404B).

Computation (using `Nat.factorial_one`, `pow_one`, `pow_zero`):
  `C M 1 = -Σᵢ M.α (i.succ) · (-(i+1))¹/1!
            - Σᵢ M.β i · (-i)⁰/0!`
        = `Σᵢ (i+1) · M.α (i.succ) - Σᵢ M.β i`
        = `(404b LHS) - (404b RHS)`.
So `C M 1 = 0 ↔ M.SatisfiesEq404b`. -/
theorem C_one_eq_zero_iff_isConsistent {k : ℕ}
    (M : LinearMultistepMethod k) (hpre : M.IsPreconsistent) :
    C M 1 = 0 ↔ M.IsConsistent := by
  rw [LinearMultistepMethod.IsConsistent]
  refine Iff.trans ?_ (and_iff_right hpre)
  -- Goal: C M 1 = 0 ↔ M.SatisfiesEq404b
  unfold C LinearMultistepMethod.SatisfiesEq404b
  -- After unfold, both sides are linear identities; use ring after
  -- collapsing factorial and power-of-0 terms.
  …
```

**Tactic plan for the algebra step:**

1. `simp only [pow_one, pow_zero, Nat.factorial_one, Nat.factorial_zero,
   Nat.cast_one, mul_one, div_one]` — collapse `1! = 1`, `0! = 1`,
   `(-x)^1 = -x`, `(-x)^0 = 1`.
2. The α-sum becomes `-Σᵢ M.α i.succ * (-(i.val+1 : ℝ))`, which
   simplifies via `neg_neg` and `mul_comm` to
   `Σᵢ (i.val+1 : ℝ) * M.α i.succ`.
3. The β-sum becomes `-Σᵢ M.β i * 1` = `-Σ M.β i`.
4. Goal: `Σᵢ (i.val+1 : ℝ) · M.α i.succ - Σ M.β i = 0 ↔
   Σᵢ (i.val+1 : ℝ) · M.α i.succ = Σ M.β i`. Close via `linarith`
   (or `omega` after `sub_eq_zero`).

**Cast bridging note (per memory `feedback_satisfieseq404b_cast.md`):**
`SatisfiesEq404b` uses `((i : ℕ) + 1 : ℝ)` (cast from `Fin k`).
After `unfold C`, we have `(-((i.val + 1 : ℕ) : ℝ))^1 = -(↑(i.val + 1))`
where the cast is on the *expanded* `Nat`. These are
extensionally equal — use `convert ... using 1; Finset.sum_congr; push_cast; ring`
if direct rewriting stalls.

### Deliverable D4 — `thm_410B` (~40 LOC)

```lean
/-- **Butcher §410 Theorem 410B (order condition).**

A linear multistep method has order at least `p` if and only if
the first `p+1` formal power-series coefficients of its generating
function `α(exp(-z)) - zβ(exp(-z))` vanish.

(Sign convention: Butcher's textbook statement uses
`α(exp(z)) + zβ(exp(z))` with forward sign convention. Our encoding
uses backward sign matching def:406A and thm:410A; the two
formulations are equivalent under `z ↦ -z`.)

Proof: by thm_410A, `coeff j (genFn M) = C M j` for every `j`, so
the predicate `∀ j ≤ p, coeff j (genFn M) = 0` is *literally*
`∀ j ≤ p, C M j = 0`, which is `M.HasOrderAtLeast p`. -/
theorem thm_410B {k : ℕ} (M : LinearMultistepMethod k) (p : ℕ) :
    M.HasOrderAtLeast p
      ↔ ∀ j ≤ p, (PowerSeries.coeff (R := ℝ) j) (genFn M) = 0 := by
  unfold LinearMultistepMethod.HasOrderAtLeast
  refine ⟨fun h j hj => ?_, fun h j hj => ?_⟩
  · rw [thm_410A]; exact h j hj
  · rw [← thm_410A]; exact h j hj
```

### Deliverable D5 — Witnesses (~50 LOC)

```lean
/-- **Non-vacuity witness — explicit Euler has order ≥ 0.**
Order ≥ 0 is exactly preconsistency (C₀ = 0). -/
theorem explicitEulerLMM_hasOrderAtLeast_zero :
    explicitEulerLMM.HasOrderAtLeast 0 := by
  intro j hj
  interval_cases j
  exact C_zero_explicitEuler

/-- **Non-vacuity witness — explicit Euler has order ≥ 1.**
By `C_one_eq_zero_iff_isConsistent` and
`explicitEulerLMM_isConsistent`. -/
theorem explicitEulerLMM_hasOrderAtLeast_one :
    explicitEulerLMM.HasOrderAtLeast 1 := by
  intro j hj
  interval_cases j
  · exact C_zero_explicitEuler
  · exact (C_one_eq_zero_iff_isConsistent explicitEulerLMM
            explicitEulerLMM_isPreconsistent).mpr
            explicitEulerLMM_isConsistent

/-- **Restrictiveness check — explicit Euler does NOT have order 2.**
Computes `C explicitEulerLMM 2` directly and shows it is non-zero
(it equals `1/2`, since explicit Euler is the standard order-1
method). This proves `HasOrderAtLeast` is genuinely restrictive
(not vacuous) and matches the textbook's classification of
explicit Euler as a first-order method. -/
theorem explicitEulerLMM_C_two_ne_zero :
    C explicitEulerLMM 2 ≠ 0 := by
  unfold C explicitEulerLMM
  simp [Fin.sum_univ_succ]
  -- After simp, goal reduces to a concrete numerical inequality
  -- (e.g. `1/2 ≠ 0` after factorials collapse). Close with `norm_num`.
  norm_num
```

The expected `C explicitEulerLMM 2` value (per Butcher's Adams
classification) is `-1/2` (with our sign convention; can be
positive depending on detail). The proof should compute it exactly
via `simp [Fin.sum_univ_succ, Fin.sum_univ_zero]` then `norm_num`.

If the explicit numerical value is awkward, the simpler tactic
plan is:
```lean
unfold C explicitEulerLMM
simp [Fin.sum_univ_succ, Fin.sum_univ_zero, Nat.factorial_succ,
      Nat.factorial_zero]
norm_num
```

## Aristotle batch (mandatory per CLAUDE.md)

Submit a batch of 5 sub-lemmas to Aristotle **at the start of the
cycle** (before manual proof attempts). Sleep 30 min, then
incorporate or proceed manually.

**Batch contents** (write to
`.prover-state/aristotle_submissions/cycle_075/sub_lemmas.lean`):

1. **`C_one_eq_zero_iff_isConsistent`** (the bridge — D3 above).
   Provide context: `IsPreconsistent`, `IsConsistent`,
   `SatisfiesEq404b` definitions from Section404.lean. The
   algebraic step is the only mildly tricky part and Aristotle
   excels at this style of `simp + ring` finisher.
2. **`thm_410B`** (D4 above). Provide context: `HasOrderAtLeast`
   definition, `genFn` definition, `thm_410A` statement. The proof
   is mechanical (forward/reverse via `rw [thm_410A]`) so Aristotle
   should close it cleanly; gives a sanity check on the lemma
   shape.
3. **`explicitEulerLMM_hasOrderAtLeast_one`** (D5). Tests that the
   bridge wires up correctly.
4. **`explicitEulerLMM_C_two_ne_zero`** (D5). Numerical
   computation; well-suited for Aristotle.
5. **`αPoly_implicitEuler`** + **`βPoly_implicitEuler`** (combined
   as one Aristotle file): for implicit Euler `(α₁=1, β₀=1, β₁=0)`,
   show `αPoly = 1 - X` and `βPoly = 1`. Direct unfold + `simp`.
   Useful non-vacuity coverage of the implicit branch (mirrors the
   existing `αPoly_explicitEuler`/`βPoly_explicitEuler`).

**Polling**: ONE check after 30 min. Do NOT re-poll.

## Step-by-step worker checklist

1. **(5 min)** Verify cycle 074 state: `git log -1 --oneline`
   should show `fa8abdb`. Run
   `lake env lean OpenMath/Chapter4/Section410.lean` and confirm
   clean compile + 0 sorries.

2. **(15 min)** Submit Aristotle batch (above). Use
   `mcp__aristotle__submit_directory` on
   `.prover-state/aristotle_submissions/cycle_075/`. Record
   project ID. Set wakeup for 30 min.

3. **(20 min)** Add `genFn` abbreviation (D2). Refactor existing
   `thm_410A` and `thm_410A_zero` to use it. Compile-check
   (`lake env lean OpenMath/Chapter4/Section410.lean`).

4. **(15 min)** Add `HasOrderAtLeast` definition (D1) with
   docstring quoting Butcher. Compile-check.

5. **(40 min)** Prove `C_one_eq_zero_iff_isConsistent` (D3)
   manually. Use `lean_multi_attempt` to test the simp/ring
   tactic at the algebra step before committing.

6. **(20 min)** Prove `thm_410B` (D4) manually. Should be ~10 LOC
   by direct rw + `thm_410A`.

7. **(30 min)** Add witnesses (D5). Use `lean_multi_attempt` for
   the `C explicitEulerLMM 2 ≠ 0` numerical step.

8. **(15 min)** Check Aristotle once. If `C_one_eq_zero_iff_isConsistent`
   or any other returned lemma has a cleaner proof than yours,
   substitute it (with attribution comment); otherwise keep
   manual. Verify file still compiles + axioms still
   `[propext, Classical.choice, Quot.sound]`.

9. **(20 min)** Pre-commit faithfulness checklist (CLAUDE.md):
   - For each new `def`/`theorem`, quote textbook statement and
     verify Lean version captures the same content.
   - **Tautology check**: `HasOrderAtLeast` ↔ "all C_j = 0" is the
     definition; `thm_410B` is "all C_j = 0" ↔ "all coefficients
     of genFn vanish". The latter is non-trivial because
     `coeff j (genFn) = C M j` is `thm_410A` (a substantive
     identity, not an unfold). PASS.
   - **Identity check**: `thm_410B`'s proof is a 2-step
     `rw [thm_410A]` in each direction. NOT vacuous because
     `thm_410A` is doing the work.
   - **Hypothesis strength check**: Butcher's 410B takes only an
     LMM. Our version is parameterised only by
     `M : LinearMultistepMethod k`. PASS.

10. **(10 min)** Update `extraction/formalization_data/lean_status.json`:
    flip `thm:410B` to `formalized` with notes pointing at
    `OpenMath/Chapter4/Section410.lean::thm_410B`. Update
    `plan.md::thm:410B` from `[ ]` to `[x]` and bump progress
    counter `44 → 45 of 175`.

11. **(15 min)** Write `.prover-state/task_results/cycle_075.md`
    documenting deliverables, approach, faithfulness check, and
    suggested next step (likely `thm:410D` or
    `thm:410C`-bridging).

12. **(10 min)** Final `lake build OpenMath.Chapter4.Section410`
    + `#print axioms OpenMath.Chapter4.Section410.thm_410B`
    sanity check. Commit and push.

Total budget: ~3.5 hours of worker time. Net diff: +5 to +8
theorems and 1 new definition; probably ~150–200 LOC added.

## What NOT to do this cycle

* **Do NOT define `HasOrderAtLeast` asymptotically.** A predicate
  like `∃ C, ∀ y h, |L(y,x,h)| ≤ C · h^{p+1}` would be the
  *characterization* via lem:406B-style bounds. It is heavier
  (requires `Filter.IsBigO` or a quantitative bound) and is NOT
  Butcher's stated definition. The C_j-vanishing form matches
  Butcher's text verbatim and is faithful.

* **Do NOT introduce a forward-sign `αPolyForward`/`βPolyForward`
  pair to literally match Butcher's 410B `+z β(exp(z))` form.**
  That is `thm:410C` territory (the textbook notes 410C is "this
  result restated in (ρ, σ) notation"). The sign-conjugation
  bridge can be a future deliverable. Document the sign mismatch
  in `thm_410B`'s docstring instead.

* **Do NOT formalize Butcher's `O(z^{p+1})` directly via
  `Filter.IsBigO`.** That requires a topology on `PowerSeries ℝ`
  which Mathlib does not have at the level of generality we need
  here. Use the per-coefficient form
  `∀ j ≤ p, coeff j (genFn M) = 0`, which is the textbook's
  operational meaning of `O(z^{p+1})` for formal power series.

* **Do NOT touch `Section404.lean` or `Section405.lean`.** All work
  for cycle 075 lives in `Section410.lean`. Keep the diff
  localized.

* **Do NOT raise `maxHeartbeats`.** If the explicit-Euler
  numerical step `C explicitEulerLMM 2 ≠ 0` is slow, decompose:
  use `decide` on the rational-arithmetic step, or compute the
  literal value first with `have hC2 : C explicitEulerLMM 2 = 1/2 := ...`
  then `rw [hC2]; norm_num`.

* **Do NOT skip the Aristotle batch.** Per CLAUDE.md:
  "Maximize Aristotle usage. It is free compute." The 5-sub-lemma
  batch above is the cycle's mandated batch.

* **Do NOT poll Aristotle more than once.** The CLAUDE.md
  "submit, sleep 30 min, check once" rule is explicit; cycle 074's
  worker followed it correctly and so should you.

* **Do NOT introduce `axiom` or `constant` for any step.** The
  cycle 075 plan has no infrastructure gaps — all needed Mathlib
  pieces (`Polynomial.aeval`, `PowerSeries.coeff`, factorials,
  `Fin.sum_univ_succ`) exist and were exercised by cycle 074.

* **Do NOT widen `IsConvergent` further.** The cycle 068
  strengthening (joint Lipschitz + global C¹ + global trajectory
  bound) is sufficient and documented. §410B does not consume
  `IsConvergent`.

* **Do NOT commit Section410.lean with any new sorry.** Net sorry
  count must stay at 0. If a sub-lemma proof goes sideways,
  decompose it into smaller pieces and prove the pieces; do NOT
  leave a `sorry` placeholder. (Cycle 073's revert is the
  cautionary tale.)

* **Do NOT use the `unfold C; ring` shortcut for the
  `C M 1 = 0 ↔ M.SatisfiesEq404b` step.** As cycle 074 discovered,
  `match`-based definitions like `C` do not auto-reduce under
  `ring`. Use the explicit
  `simp only [pow_one, pow_zero, Nat.factorial_one, Nat.factorial_zero,
   Nat.cast_one, mul_one, div_one]` collapse first, then `linarith`
  or `omega` to close.

* **Do NOT chase the "forward-vs-backward sign convention" issue
  this cycle.** Document it in the `thm_410B` docstring; defer
  the literal forward-form variant to a later cycle (likely the
  `thm:410C` bridge cycle).

* **Do NOT modify `scripts/autonomous_loop.py`.** Per the standing
  `tautology_scanner_false_positives.md` issue, scanner / prompt-builder
  bugs are loop-maintainer territory, not worker territory.

## Backup plan if Aristotle returns surprising results

If Aristotle returns a proof for `thm_410B` that uses a
*different* abbreviation than `genFn` (e.g. inlines the
`aeval expNegPS αPoly - X * aeval expNegPS βPoly` expression),
either accept the inline form and skip D2's `genFn` abbreviation,
or do the trivial `unfold genFn` rewrite in the returned proof.
Prefer keeping the abbreviation — it makes the §410C / §410D
work cleaner.

If Aristotle's `C_one_eq_zero_iff_isConsistent` proof works but
uses the `convert` cast bridge from
`feedback_satisfieseq404b_cast.md`, prefer it (the cast bridge is
the proven-correct pattern; the simp/linarith plan in D3 is the
fallback).

If Aristotle's `explicitEulerLMM_C_two_ne_zero` proof returns a
specific numerical value for `C explicitEulerLMM 2`, record it in
the witness's docstring (it should be `1/2` or `-1/2` depending
on sign collection — the actual sign is an interesting datum
worth documenting).

If Aristotle fails on **all 5** sub-lemmas (unusual for goals this
algebraically standard), fall back to the manual proofs in D3/D4/D5;
they are individually small enough to close in cycle time.

## Backup plan if the cycle stalls

If by hour 3 not all 5 deliverables (D1–D5) are landed:

* **Minimum viable cycle**: ship D1 (`HasOrderAtLeast` definition)
  + D2 (`genFn` abbreviation + thm_410A refactor) + D3
  (`C_one_eq_zero_iff_isConsistent`) + D4 (`thm_410B`). Defer D5
  witnesses to cycle 076. This still bumps the progress counter
  to 45/175 and lands the §410B order condition.
* **Smaller fallback**: ship D1 + D2 + D4 only. The
  `C_one_eq_zero_iff_isConsistent` bridge can be deferred — it
  is needed only by D5's `explicitEulerLMM_hasOrderAtLeast_one`,
  not by `thm_410B` itself.

In any case, **commit ONLY zero-sorry work**. Cycle 073's revert
shows that any sorry-bearing commit triggers an automatic revert
even if the work is sound. Better to ship a smaller diff than to
re-trigger the revert.

## Cross-references

* `OpenMath/Chapter4/Section410.lean:125-132` — `C` definition.
* `OpenMath/Chapter4/Section410.lean:304-338` — existing
  `thm_410A` (refactor target for D2).
* `OpenMath/Chapter4/Section404.lean:124-137` — `SatisfiesEq404b`,
  `IsConsistent`, `IsPreconsistent` (consumed by D3).
* `OpenMath/Chapter4/Section404.lean:88-152` — explicit Euler
  preconsistency / consistency witnesses (consumed by D5).
* `extraction/formalization_data/entities/thm_410B.json` —
  textbook statement (faithfulness target for D4).
* `.prover-state/task_results/cycle_074.md` §"Suggested next
  approach" — origin of this cycle's plan.
* Memory `feedback_satisfieseq404b_cast.md` — cast bridging
  pattern relevant to D3's algebra step.
