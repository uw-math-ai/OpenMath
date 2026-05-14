# Cycle 240 strategy

## Priority 0 — DO NOT attempt the §441 GPFS smoke test

43 consecutive cycles (182–239) have hit the same near-zero-CPU
GPFS-disk-wait timeout pattern on `OpenMath/Chapter4/Section441.lean`.
Cycle 239's task results conclude the pattern is conclusive. Skip
the smoke test entirely. Do NOT attempt any work in
`OpenMath/Chapter4/Section441.lean` itself.

Section441B.lean and Section381.lean compile cleanly (warm ~6s);
all cycle 240 work goes there.

## Aristotle queue check

None pending; no outstanding Aristotle submissions across §441,
§383, or §302 tracks. Skip polling.

## Priority 1 — Ship two `cInverseLog` closed-form witnesses in Section441B.lean

Cycle 239's recommended option 3. Add two axiom-clean closed-form
theorems in `OpenMath/Chapter4/Section441B.lean`, immediately after
`cInverseLog_one_eq_neg_one_sixth` at line 170 (i.e. between
`cInverseLog_one_eq_neg_one_sixth` and `cInverseLog_zero_pos`).

### Deliverable 1.A — `cInverseLog_two_eq : cInverseLog 2 = -2/45`

Compute c₄ closed-form via (441c) at `coeff 4`. The identity
`cInverseLogSeries * cSeries = 1` evaluated at coefficient 4 gives:

```
∑ (i,j) ∈ antidiagonal 4, (coeff i cIL) * (coeff j cS) = 0
```

Antidiagonal `{(0,4), (1,3), (2,2), (3,1), (4,0)}`. Odd-index `cIL`
coefficients vanish; the three non-vanishing contributions are:

* (0,4): `2 · cInverseLog 2`
* (2,2): `(2/3) · cInverseLog 1 = (2/3) · (-1/6) = -1/9`
* (4,0): `(2/5) · cInverseLog 0 = (2/5) · (1/2) = 1/5`
* (1,3), (3,1): zero (odd cIL)

Sum: `2 c₄ - 1/9 + 1/5 = 0` ⟹ `2 c₄ = (1-5)/45 = -4/45` ⟹ `c₄ = -2/45`.

### Deliverable 1.B — `cInverseLog_three_eq : cInverseLog 3 = -22/945`

Compute c₆ closed-form via (441c) at `coeff 6`. Antidiagonal of 6 has 7 pairs:

* (0,6): `2 · cInverseLog 3`
* (2,4): `(2/3) · cInverseLog 2 = (2/3) · (-2/45) = -4/135`
* (4,2): `(2/5) · cInverseLog 1 = (2/5) · (-1/6) = -1/15`
* (6,0): `(2/7) · cInverseLog 0 = (2/7) · (1/2) = 1/7`
* (1,5), (3,3), (5,1): zero (odd cIL)

Over LCM 945: `2 c₆ = 28/945 + 63/945 - 135/945 = -44/945` ⟹ `c₆ = -22/945`.

This requires Deliverable 1.A to be in place first (uses
`cInverseLog_two_eq` to substitute the coeff 4 cSeries term).

## Proof recipe — verbatim port of cycle 237's `cInverseLog_one_eq_neg_one_sixth`

The proof at `Section441B.lean:138–170` is the working template. For
`cInverseLog_two_eq` write:

```lean
theorem cInverseLog_two_eq : cInverseLog 2 = -2 / 45 := by
  have hmul := cInverseLogSeries_mul_cSeries_eq_one
  have hcoeff : (PowerSeries.coeff (R := ℝ) 4) (cInverseLogSeries * cSeries)
      = (PowerSeries.coeff (R := ℝ) 4) (1 : PowerSeries ℝ) := by
    rw [hmul]
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_one] at hcoeff
  simp only [show (4 : ℕ) ≠ 0 by decide, if_false] at hcoeff
  rw [show (Finset.antidiagonal 4 : Finset (ℕ × ℕ)) =
      {(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} from by decide] at hcoeff
  rw [show ({(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} : Finset (ℕ × ℕ)) =
      insert (0, 4) (insert (1, 3) (insert (2, 2) (insert (3, 1)
        {(4, 0)}))) from rfl] at hcoeff
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton] at hcoeff
  rw [coeff_cInverseLogSeries 0, coeff_cInverseLogSeries 1,
      coeff_cInverseLogSeries 2, coeff_cInverseLogSeries 3,
      coeff_cInverseLogSeries 4] at hcoeff
  simp only [show Even (0 : ℕ) from ⟨0, by decide⟩,
             show ¬ Even (1 : ℕ) from Nat.not_even_one,
             show Even (2 : ℕ) from ⟨1, by decide⟩,
             show ¬ Even (3 : ℕ) from by decide,
             show Even (4 : ℕ) from ⟨2, by decide⟩,
             if_true, if_false] at hcoeff
  have h0 : (PowerSeries.coeff (R := ℝ) 0) cSeries = 1 / 2 := by
    have := cInverseLog_zero_eq_half
    unfold cInverseLog at this
    simpa using this
  have h2 : (PowerSeries.coeff (R := ℝ) 2) cSeries = -1 / 6 := by
    have := cInverseLog_one_eq_neg_one_sixth
    unfold cInverseLog at this
    simpa using this
  rw [h0, h2] at hcoeff
  norm_num at hcoeff
  unfold cInverseLog
  have hex : (2 * 2 : ℕ) = 4 := by norm_num
  rw [hex]
  linarith
```

For `cInverseLog_three_eq`, antidiagonal at 6 with 7 pairs; same
structure with two extra `insert` levels, six `coeff_cInverseLogSeries`
applications (0..5 actually need 0..6), four `Even`/`¬ Even` simp facts,
and one more `coeff cS` substitution `h4 : (PowerSeries.coeff (R := ℝ)
4) cSeries = -2/45` (derived from cycle-240's own
`cInverseLog_two_eq`). The literal antidiagonal expansion:

```
{(0,6), (1,5), (2,4), (3,3), (4,2), (5,1), (6,0)}
```

## Pre-flagged risks

* **R1 — `Finset.antidiagonal 4` / `antidiagonal 6` via `by decide`.**
  Cycle 237 used `by decide` for antidiagonal 2. The decision
  procedure scales but MAY be slow at 6. Fallback: use
  `Finset.antidiagonal_succ` to peel off the `(0, n)` and `(n, 0)`
  pairs incrementally, or use `Finset.ext` + explicit case analysis.
  If `by decide` exceeds 30s, switch to fallback immediately.

* **R2 — `Even`/`¬ Even` simp facts for n = 3, 5.** Use
  `show ¬ Even (3 : ℕ) from by decide` (and `5` likewise). Cycle 237
  used `Nat.not_even_one` for n = 1; for higher odd n, `by decide`
  closes uniformly.

* **R3 — `linarith` numeric tractability.** The residue `2 · c₄ -
  1/9 + 1/5 = 0` should close after `norm_num` normalises the simp
  output. For c₆ the rational fractions are heavier; if `linarith`
  times out, follow with explicit `have : ... ; linarith` or
  `field_simp at hcoeff ⊢; linarith`.

* **R4 — `unfold cInverseLog at this; simpa using this`.** The cycle
  237 idiom for extracting `coeff (2*n) cSeries` from `cInverseLog n`.
  Reuse verbatim for h0, h2 (Deliverable 1.A) and h0, h2, h4
  (Deliverable 1.B).

* **R5 — `2 * 3 = 6` substitution.** Mirror of cycle 237's `2 * 1 = 2`
  step. Use `have hex : (2 * 3 : ℕ) = 6 := by norm_num` before the
  final `rw [hex]; linarith`.

## What NOT to try

* Do NOT attempt a unified recurrence theorem `cInverseLog n = -(1/2) ·
  ∑_{i=1}^{n} (1/(2i+1)) · cInverseLog (n-i)`. Cleaner in principle
  but requires antidiagonal-as-Fin manipulation and is multi-cycle.
  Stay with hand-expanded antidiagonals for n=2 and n=3.
* Do NOT touch `cInverseLog_neg` (cycle 238's strong-induction proof).
  It's axiom-clean; do not regress it.
* Do NOT touch `OpenMath/Chapter4/Section441.lean` (43 consecutive
  GPFS timeouts).
* Do NOT touch §380s `Section381.lean` infrastructure this cycle.
  Cycle 239 just shipped substantive §383 work; let it settle for one
  cycle.
* Do NOT freelance a §384 homomorphism step. The
  `Equivalent → PhiEquivalent` blocker is multi-cycle B-series work
  (see `thm_381H_deferred.md`).

## Priority 2 (stretch) — `cInverseLog_two_neg`, `cInverseLog_three_neg`

If Priority 1 closes within ~60 min of the cycle budget, add:

```lean
theorem cInverseLog_two_neg : cInverseLog 2 < 0 := by
  rw [cInverseLog_two_eq]; norm_num

theorem cInverseLog_three_neg : cInverseLog 3 < 0 := by
  rw [cInverseLog_three_eq]; norm_num
```

These are 1-line corollaries that strengthen cycle 238's
`cInverseLog_neg` headline with concrete numerical witnesses. Pure
non-vacuity; no new mathematical content.

## Priority 3 (stretch) — cross-check vs cycle 238 headline

If Priorities 1 + 2 close cleanly, add at the end of Section441B.lean
an `example` block confirming cycle 238's strong-induction headline
returns the same sign as the closed forms:

```lean
example : cInverseLog 2 < 0 := cInverseLog_neg 2 (by norm_num)
example : cInverseLog 3 < 0 := cInverseLog_neg 3 (by norm_num)
```

Catches any subtle off-by-one in the cycle 238 proof and gives a
"general theorem ⟹ specific witness" sanity check.

## Build verification

After all priorities land:

```bash
time lake env lean OpenMath/Chapter4/Section441B.lean
grep -c sorry OpenMath/Chapter4/Section441B.lean       # expect 0
```

Then verify axioms via `lean_verify` on each new symbol:
* `OpenMath.Chapter4.Section441B.cInverseLog_two_eq`
* `OpenMath.Chapter4.Section441B.cInverseLog_three_eq`
* (optional) `cInverseLog_two_neg`, `cInverseLog_three_neg`

Each should return `[propext, Classical.choice, Quot.sound]`.

If `lake env lean` warm compile exceeds 60s, something is wrong —
abort and investigate. Section441B.lean cold rebuild ~7s in cycle
237; warm ~3s; should stay well under 30s after the cycle 240 adds.

## Faithfulness check

For each new symbol introduced this cycle:

* **`cInverseLog_two_eq`** (theorem):
  - Textbook reference: Butcher §441 p. 376 only gives `c₀ = 1/2,
    c₂ = -1/6` explicitly. `c₄ = -2/45` follows from the (441c)
    recurrence Butcher derives. Not named in the textbook but a
    direct consequence.
  - Tautology check: PASS (closed-form value, not identity-like).
  - Identity-proof check: PASS — proof routes through
    `cInverseLogSeries_mul_cSeries_eq_one` + antidiagonal expansion;
    real work, not `exact h`.

* **`cInverseLog_three_eq`** (theorem): same structure as 1.A. `c₆ =
  -22/945`.

* **`cInverseLog_two_neg` / `cInverseLog_three_neg`** (stretch):
  one-line `norm_num` corollaries of the closed-form theorems. Real
  arithmetic check.

* No definition smuggling, no hypothesis strengthening, no `axiom`
  declarations, no `maxHeartbeats` bumps.

## Commit message draft

```
Cycle 240 — §441 Section441B closed-form witnesses at n=2, n=3.

Add cInverseLog_two_eq (c₄ = -2/45) and cInverseLog_three_eq
(c₆ = -22/945) as axiom-clean closed-form witnesses, extending
cycle 237's c₂ = -1/6 template via antidiagonal expansion at
coeff 4 and coeff 6 of cInverseLogSeries · cSeries = 1.

Verification:
- Section441B.lean compiles warm in ~Xs, 0 sorries.
- All new theorems axiom-clean [propext, Classical.choice, Quot.sound].
- No regression on cycle 237/238 lem:441B work.

GPFS smoke test on Section441.lean skipped (44th consecutive
timeout; see cycle_182_gpfs_slowness.md).
```

## Cycle 241+ outlook

* **Option A**: continue §441 Section441B with `cInverseLog_four_eq`
  / `cInverseLog_five_eq` via the same template. Marginal value
  beyond the cycle-238 general headline; mostly bookkeeping. Single
  cycle each.
* **Option B**: pivot to a §302 tree-combinatorics target (e.g.
  `thm:302A`, `thm:302B`, `thm:302C`, `thm:304A`). These are
  independent of GPFS and B-series; can ship a fresh entity in
  a single cycle.
* **Option C**: continue §383 quotient infrastructure (e.g.,
  cycle 239's option 2 — abstract-quotient `_composeQ_phi` via
  `Quotient.inductionOn₂` packaging). Limited near-term utility
  unless §384 thm:384A becomes a hard target.
* **Option D**: tackle one of the `[ ]` Ch.3 §380s entities
  (`thm:381G`, `thm:381H` — both currently blocked on the deferred
  `Equivalent → PhiEquivalent` direction; multi-cycle work).

Recommend Option B (§302 tree-combinatorics) — highest single-cycle
ship rate and unlocks fresh Chapter 3 textbook content.

## Task results expectation

Write `.prover-state/task_results/cycle_240.md` documenting:
* GPFS smoke test SKIPPED per strategy §0 (do NOT attempt).
* Each new theorem with axiom-cleanliness verification.
* If antidiagonal 6 `by decide` is slow: fallback path taken
  (`Finset.antidiagonal_succ` peeling or explicit `Finset.ext`).
* If `linarith` cannot close the c₆ residue: `field_simp; ring` or
  explicit `nlinarith` fallback used.
* Suggested next approach: continue with Section441B closed forms
  (Option A), or pivot to §302 tree-combinatorics (Option B).
