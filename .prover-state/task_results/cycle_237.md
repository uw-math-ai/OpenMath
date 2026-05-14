# Cycle 237 Results

## Worked on

`lem:441B` Phase B — universal `cInverseLog : ℕ → ℝ` coefficients
of `log((1+z)/(1-z))/z` via PowerSeries inversion. New file
`OpenMath/Chapter4/Section441B.lean` (~190 LOC, 6 public
theorems + 1 helper `coeff_cInverseLogSeries` simp lemma + 3
definitions).

## Approach

Followed cycle 237 strategy §B verbatim:

1. GPFS smoke test on `Section441.lean` (one-shot, 60s timeout)
   — TIMEOUT (42nd consecutive). Used `Section441B.lean` per §C.
2. Verified Mathlib PowerSeries API via `lean_loogle`:
   `PowerSeries.invOfUnit`, `PowerSeries.mul_invOfUnit`,
   `PowerSeries.constantCoeff_invOfUnit`,
   `PowerSeries.coeff_mul`, `PowerSeries.coeff_one`,
   `PowerSeries.coeff_zero_eq_constantCoeff`.
3. Wrote `Section441B.lean` with full proofs (no sorry-first
   needed for Phase B — proofs are short Mathlib-style
   computations).
4. Submitted Aristotle backup (single file with 4 sorries) at
   ~cycle minute 7 as safety net.
5. Two iteration rounds to fix:
   - **Wrong import path**: Used `Mathlib.Data.Nat.Parity`
     which no longer exists in this Mathlib version; the
     replacement is `Mathlib.Algebra.Ring.Parity`.
   - **`ℝ` not in scope**: needed `import Mathlib.Data.Real.Basic`
     (Section410.lean's `import Mathlib` blanket-imports
     everything, but a stand-alone file requires the explicit
     `Mathlib.Data.Real.Basic`).
   - **`PowerSeries.coeff ℝ n` positional R-arg bug**:
     `coeff`/`constantCoeff` take `R` as an implicit type
     argument; positional `ℝ` was being parsed as `n : ℕ`.
     Fixed via named `(R := ℝ)` syntax matching Section410's
     idiom.
   - **`Units.val_inv_eq_inv_val` not firing**: target was
     already in `(↑u)⁻¹` form after constantCoeff_invOfUnit
     reduction; replaced with direct `simp [twoUnit]` close.
   - **`linarith` couldn't close c₂ = -1/6**: numerical
     divisions `2/(↑0+1)` and `2/(↑2+1)` weren't pre-evaluated;
     added `norm_num at hcoeff` step before `linarith`.
6. Full file compiles (3s warm, 7s clean), all 6 theorems
   axiom-clean.
7. Cancelled Aristotle backup once local proofs verified
   (free-compute well-spent; no need to consume further).

## Result

**SUCCESS** — Phase B fully shipped axiom-clean.

Public deliverables in `OpenMath/Chapter4/Section441B.lean`:

| Symbol | Kind | Role |
|---|---|---|
| `cInverseLogSeries` | `noncomputable def` | LHS of (441c): `2 + (2/3)X² + ⋯` |
| `coeff_cInverseLogSeries` | `@[simp] lemma` | Closed-form coefficient `2/(n+1)` if even else `0` |
| `cInverseLogSeries_constantCoeff_eq_two` | `lemma` | `constantCoeff = 2` (required for `invOfUnit`) |
| `twoUnit` | `noncomputable def` | `Units.mk0 (2:ℝ) _` |
| `twoUnit_val` | `@[simp] lemma` | `(↑twoUnit : ℝ) = 2` |
| `cSeries` | `noncomputable def` | `cInverseLogSeries.invOfUnit twoUnit` |
| `cInverseLogSeries_mul_cSeries_eq_one` | `theorem` | **The (441c) identity** |
| `cInverseLog` | `noncomputable def` | `(n : ℕ) ↦ coeff (2*n) cSeries` |
| `cInverseLog_zero_eq_half` | `theorem` | `c₀ = 1/2` |
| `cInverseLog_one_eq_neg_one_sixth` | `theorem` | `c₂ = -1/6` |
| `cInverseLog_zero_pos` | `theorem` | `0 < c₀` (P5 non-vacuity) |
| `cInverseLog_one_neg` | `theorem` | `c₂ < 0` (first non-trivial Phase C instance) |

All 6 named theorems axiom-clean:
`[propext, Classical.choice, Quot.sound]`.

Sorry count: 0 (unchanged from cycle 236).

## Faithfulness check

For each new `def` and `theorem` introduced this cycle:

### `cInverseLogSeries`, `coeff_cInverseLogSeries`,
### `cInverseLogSeries_constantCoeff_eq_two`

Entity ID and textbook statement
(`extraction/formalization_data/entities/lem_441B.json` /
`extraction/raw_text/ch04.txt:1947–2030`):

> "Using the series for log((1+z)/(1-z))/z, we see that
> `c₀, c₂, c₄, …` satisfy (2 + (2/3)z² + (2/5)z⁴ + ⋯)(c₀ +
> c₂z² + c₄z⁴ + ⋯) = 1." (Butcher §441 eq. (441c))

Lean: `cInverseLogSeries := PowerSeries.mk fun n => if Even n
then 2/(n+1) else 0`. Coefficient at `X^(2i)` is `2/(2i+1)`;
coefficient at `X^(2i+1)` is `0`. Matches the LHS of (441c)
verbatim. **Captures: same content.**

### `twoUnit`, `cSeries`

These are infrastructure for invoking
`PowerSeries.invOfUnit`. `twoUnit := Units.mk0 (2:ℝ) _`
witnesses that `2` is a unit of ℝ; `cSeries :=
cInverseLogSeries.invOfUnit twoUnit` is by definition the
formal-power-series inverse of the LHS of (441c). Following
Butcher's textbook construction: `(c₀ + c₂z² + c₄z⁴ + ⋯)` is
literally defined to be the series with this property.
**Captures: same content.**

### `cInverseLogSeries_mul_cSeries_eq_one`

This is Butcher's (441c) identity, exact. Proved via
`PowerSeries.mul_invOfUnit` + the constant-coefficient witness.
Not a tautology: it asserts an algebraic relationship between
two non-trivial power series. **Captures: same content** (the
(441c) identity verbatim).

### `cInverseLog`

`cInverseLog n := coeff (2n) cSeries` matches Butcher's `c_{2n}`
indexing. Butcher writes the constants as `c₀, c₂, c₄, …`
indexed by even integers; our `cInverseLog : ℕ → ℝ` re-indexes
so that `cInverseLog k = c_{2k}`. The Lean function is a
**reindexing** of the textbook sequence; equivalent up to the
trivial index relabelling. **Captures: same content** (with
explicit re-indexing).

### `cInverseLog_zero_eq_half`

Textbook: "It follows that `c₀ = 1/2`" (Butcher p. 376, last
line of the (441c) discussion). Lean: `cInverseLog 0 = 1 / 2`.
**Captures: same content.**

### `cInverseLog_one_eq_neg_one_sixth`

Textbook: "It follows that ... `c₂ = -1/6`" (Butcher p. 376,
last line of the (441c) discussion). Lean: `cInverseLog 1 =
-1 / 6` (i.e., `c_{2·1} = c₂ = -1/6`). **Captures: same
content** (with the reindexing convention).

### `cInverseLog_zero_pos`, `cInverseLog_one_neg`

P5 non-vacuity witnesses. `cInverseLog_zero_pos : 0 <
cInverseLog 0` — trivial from `c₀ = 1/2`. `cInverseLog_one_neg
: cInverseLog 1 < 0` — first non-trivial instance of the
negativity claim of `lem:441B` (sign for `c₂ = -1/6`).
These are stronger versions of the equality witnesses and
serve as Phase C base cases. **Captures: weaker** than the
full Phase C claim, but justified as base-case witnesses for
the deferred Phase C induction.

### No definition smuggling

`cInverseLog` is defined as a PowerSeries coefficient extraction
of an *algebraically inverted* series — NOT as "the negative
sequence" or "the sequence satisfying the negativity property".
The negativity claim of `lem:441B` is the deferred Phase C
*theorem* about these constants, not their definition.

### No tautology / identity-proof bug

The headline (441c) identity `cInverseLogSeries * cSeries = 1`
is proved by invoking `PowerSeries.mul_invOfUnit` — this
genuinely instantiates the formal-power-series inverse
machinery; it is not `id` or `rfl`. The base-case theorems
(`zero_eq_half`, `one_eq_neg_one_sixth`) genuinely compute
their values via `constantCoeff_invOfUnit` and `coeff_mul`
respectively; not vacuous.

### No extra hypotheses

The two equality theorems take no hypotheses (constants are
universal). The Phase D non-vacuity theorems take no
hypotheses either. **Captures: same content.**

### No phantom theorem references

The file docstring lists what is shipped vs deferred to Phase
C; everything listed as shipped is in the file.

## Dead ends

* **`Mathlib.Data.Nat.Parity` import**: this module no longer
  exists in the current Mathlib version. The Even-on-Nat
  lemmas have migrated to `Mathlib.Algebra.Ring.Parity`. First
  compile attempt failed with "object file .../Parity.olean
  does not exist".

* **Bare `import Mathlib` not needed**: tried just specifying
  `Mathlib.RingTheory.PowerSeries.*` + `Mathlib.Algebra.Ring.Parity`
  + `Mathlib.Algebra.BigOperators.NatAntidiagonal` but ℝ was
  not in scope (the synthInstance errors gave away `ℝ` as a
  *local variable*, not the real numbers). Added
  `import Mathlib.Data.Real.Basic` explicitly.

* **`PowerSeries.coeff ℝ n` positional syntax**: `coeff` takes
  `R` as an *implicit* type argument, not positional. Need
  the named-implicit syntax `(R := ℝ)` for explicitness
  (matches Section410.lean idiom). The bug manifested as
  `argument ℝ has type R⟦X⟧` — Lean parsed `ℝ` as the
  explicit `n : ℕ` argument.

* **`Units.val_inv_eq_inv_val` rewrite mismatch**: after
  applying `constantCoeff_invOfUnit`, Lean's default
  normalization already presented the goal as `(↑twoUnit)⁻¹ = 1/2`,
  so the explicit rewrite `Units.val_inv_eq_inv_val` (which
  goes the same direction) found no `↑(u⁻¹)` pattern to match.
  Solution: drop the rewrite, use `simp [twoUnit]` to close
  directly via `((Units.mk0 2 _ : ℝˣ)⁻¹ : ℝ) = 2⁻¹ = 1/2`.

* **`linarith` couldn't handle `2/(↑0 + 1)` and `2/(↑2 + 1)`**:
  the numerical divisions had unevaluated `↑0` and `↑2` casts;
  added `norm_num at hcoeff` before `linarith`.

## Discovery

* **Mathlib PowerSeries inversion is mature and ergonomic**.
  `PowerSeries.invOfUnit` + `constantCoeff_invOfUnit` +
  `mul_invOfUnit` are all here, with implicit-R type-class
  inference. The unit-witness pattern (`Units.mk0` for fields)
  composes cleanly.

* **The (441c) identity is genuinely formalisable as a
  multiplicative power-series identity** — no need for ad-hoc
  coefficient-by-coefficient bookkeeping at the definition
  step. Once Phase C starts, the coefficient extraction is a
  straightforward `coeff_mul` application; the hard part will
  be the Even-indexing collapse and the strong induction.

* **GPFS pathology continues**: the §441-side
  `Section441.lean` smoke test timed out for the 42nd
  consecutive cycle (cycles 182–237 = 56 calendar days, ~8
  weeks). The newly-created `Section441B.lean` (no transitive
  Section441 dependency, only mathlib) compiled cleanly in 3s
  warm / 7s clean, confirming the pathology is
  Section441-transitive-load-specific.

* **Section441B's clean compile in <10s on cold cache** is
  encouraging — for future §441-Phase-C work, splitting into
  smaller PowerSeries-only files (no `Mathlib.Analysis.*`
  load) sidesteps GPFS contention entirely.

## Suggested next approach

**Cycle 238+ entry point**: `lem:441B` Phase C.

The strict-negativity claim `∀ n, 1 ≤ n → cInverseLog n < 0`
needs:

1. **Auxiliary `d_{2i}` series**: define
   `dSeries (n : ℕ) : PowerSeries ℝ` from Butcher's (441d):
   `dSeries n := PowerSeries.mk fun i => if Even i then
   2*(2n+1)/(i+1) - 2*(2n-1)/(i-1) else 0` (with i = 0 special
   case = `2 · (2n+1)`; i.e., `d₀ = 2(2n+1)`).
2. **Closed-form `d_{2i} = -8(n-i)/((2i+1)(2i-1))`** for
   `1 ≤ i ≤ n`, plus `d_{2n} = 0`.
3. **(441d) identity**: `(∑ d_{2i} z^{2i}) * (∑ c_{2i} z^{2i})
   = 2n + 1 - (2n-1)z²` (a polynomial identity in `PowerSeries`).
4. **Sign of `d_{2i}`**: `d_{2i} < 0` for `1 ≤ i ≤ n-1`.
5. **Strong induction**: assuming `c_{2i} < 0` for
   `i = 1, …, n-1`, extract the `z^{2n}` coefficient from the
   (441d) identity to derive `c_{2n} = -(c₂·d_{2n-2} +
   c₄·d_{2n-4} + ⋯ + c_{2n-2}·d₂) / d₀`, and conclude
   negativity.

Estimated 80–150 LOC. Aristotle suitability: medium-low —
strong induction + sign analysis combinations are typically
harder for Aristotle than mechanical computations.

Alternative cycle 238 targets if Phase C blocks:

* `thm:441C` Dahlquist barrier (depends on `lem:441B` Phase C
  + `lem:441A` Phase C closure — likely multi-cycle still).
* GPFS smoke retry for Phase C.2 of `lem:441A` (43rd attempt
  — escalation continues).
* Continue §380 cluster (now resumed after this §441B pivot).

## Files touched this cycle

* Created `OpenMath/Chapter4/Section441B.lean` (~190 LOC).
* Edited `OpenMath/Chapter4.lean` (one-line import addition).
* Edited `plan.md` (`lem:441B` row: `[ ]` → `[~]`,
  cycle 237 closure note).
* Edited `extraction/formalization_data/lean_status.json`
  (`lem:441B` row: `unformalized` → `partial` with cycle 237
  notes).
* Appended to
  `.prover-state/issues/cycle_182_gpfs_slowness.md`
  (42nd-timeout one-liner).
* Created this file: `.prover-state/task_results/cycle_237.md`.
* Appended to
  `.prover-state/issues/lem_441B_misinterpretation.md`
  ("Cycle 237 update — Phase B SHIPPED").
