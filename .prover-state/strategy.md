# Cycle 238 Strategy

## Headline

**Ship Phase C of `lem:441B`**: strict negativity of `cInverseLog n`
for `n ≥ 1`. Continue working in `OpenMath/Chapter4/Section441B.lean`
(created cycle 237) — it has **no transitive `Section441.lean`
dependency**, only Mathlib, and compiles clean in 3s warm / 7s clean.
This entirely sidesteps the 42-cycle GPFS pathology blocking
`Section441.lean`.

If Phase C lands, `lem:441B` closes fully (`partial → formalized`).

## Context — what cycle 237 left us

* `OpenMath/Chapter4/Section441B.lean` exists with 6 axiom-clean
  theorems + 3 definitions + 1 helper simp lemma (~190 LOC).
* `cInverseLogSeries`, `cSeries`, `cInverseLog : ℕ → ℝ` defined.
* (441c) identity `cInverseLogSeries * cSeries = 1` proved.
* Base cases: `cInverseLog 0 = 1/2`, `cInverseLog 1 = -1/6`.
* Sign witnesses: `cInverseLog_zero_pos`, `cInverseLog_one_neg`.
* `lem:441B` status: `unformalized → partial`.
* Sorry count: 0.
* No Aristotle results pending.

## Phase C target

Headline theorem:

```lean
theorem cInverseLog_neg {n : ℕ} (hn : 1 ≤ n) : cInverseLog n < 0
```

Per the cycle 237 task results "Suggested next approach", the textbook
proof (Butcher §441 p. 376) uses identity (441d):

```
(2(2n+1) + d_2·z² + d_4·z⁴ + ⋯ + d_{2n-2}·z^{2n-2}) · cSeries
  = 2n + 1 - (2n-1)·z²
```

where `d_{2i} := -8(n-i) / ((2i+1)(2i-1))` for `1 ≤ i ≤ n-1`,
`d_0 := 2(2n+1)`, `d_{2n} := 0`. The `d_{2i}` depend on `n` (the
*index* in `cInverseLog n`), so the auxiliary series is parametric in
`n`.

Extracting the `z^{2n}` coefficient from (441d) gives a recurrence
that lets a strong induction on `n` conclude `c_{2n} < 0`.

## Phase C plan — 4 sub-steps

### Step C.1 — Define the parametric auxiliary `dSeries`

```lean
noncomputable def dSeries (n : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk fun k =>
    if k = 0 then 2 * (2 * (n : ℝ) + 1)
    else if Even k ∧ 1 ≤ k / 2 ∧ k / 2 ≤ n - 1 then
      -8 * ((n : ℝ) - k / 2) / ((k + 1) * (k - 1))
    else 0
```

Verify the closed-form coefficients via `@[simp]` lemmas
`coeff_dSeries_zero`, `coeff_dSeries_even_inner`,
`coeff_dSeries_odd_zero`. Mirror cycle 237's
`coeff_cInverseLogSeries` style for the conditional unfolding.

### Step C.2 — Prove the (441d) PowerSeries identity

```lean
theorem dSeries_mul_cSeries_eq (n : ℕ) (hn : 1 ≤ n) :
    dSeries n * cSeries =
      PowerSeries.C ℝ (2 * (n : ℝ) + 1) -
      PowerSeries.C ℝ (2 * (n : ℝ) - 1) * PowerSeries.X ^ 2
```

Strategy: multiply (441c) by `(2n + 1 - (2n-1)·X²)`. The product
`(2n + 1 - (2n-1)·X²) · cInverseLogSeries` should equal `dSeries n`
by direct coefficient-by-coefficient calculation. Then:

```
dSeries n * cSeries
  = (2n+1 - (2n-1)·X²) · cInverseLogSeries · cSeries
  = (2n+1 - (2n-1)·X²) · 1                    [by (441c) from cycle 237]
  = 2n+1 - (2n-1)·X²
```

Factor as: first prove the helper
`private lemma poly_mul_cInverseLogSeries_eq_dSeries (n : ℕ) (hn : 1 ≤ n) :
  (PowerSeries.C ℝ (2*n+1) - PowerSeries.C ℝ (2*n-1) * X^2) * cInverseLogSeries = dSeries n`
via `PowerSeries.ext` + per-coefficient evaluation (using
cycle 237's `coeff_cInverseLogSeries` simp). Then the main identity
follows from `mul_assoc + mul_comm + the helper +
cInverseLogSeries_mul_cSeries_eq_one`.

### Step C.3 — Sign of `d_{2i}` for `1 ≤ i ≤ n-1`

```lean
theorem coeff_dSeries_neg (n i : ℕ) (h₁ : 1 ≤ i) (h₂ : i ≤ n - 1) :
    PowerSeries.coeff ℝ (2 * i) (dSeries n) < 0
```

Direct evaluation of the closed form: numerator `-8(n-i)` is negative
(since `n-i ≥ 1`); denominator `(2i+1)(2i-1)` is positive for `i ≥ 1`.
Close by `positivity` / `nlinarith` on the explicit form.

### Step C.4 — Strong induction headline

```lean
theorem cInverseLog_neg : ∀ n : ℕ, 1 ≤ n → cInverseLog n < 0
```

Proof: `Nat.strong_induction_on` on `n`.

* `n = 1`: cite cycle 237's `cInverseLog_one_neg`.
* `n ≥ 2`: extract the `z^{2n}` coefficient from `dSeries n * cSeries =
  (2n+1) - (2n-1)·X²` via `PowerSeries.coeff_mul` on the LHS and
  `coeff_C_mul`/`coeff_X_pow` on the RHS. The RHS coefficient is 0
  at `2n` (for `n ≥ 2`).

  By `PowerSeries.coeff_mul`, LHS = `∑_{(p,q) ∈ antidiagonal (2n)}
  dSeries.coeff p · cSeries.coeff q = 0`.

  Antidiagonal cases:
  - `(0, 2n)`: contributes `2(2n+1) · cInverseLog n`.
  - `(2i, 2n-2i)` for `1 ≤ i ≤ n-1`: contributes `d_{2i} · c_{2n-2i}`,
    where `d_{2i} < 0` (Step C.3) and `c_{2n-2i} < 0` (strong IH on
    `cInverseLog (n-i)` since `1 ≤ n-i ≤ n-1 < n`). Each product
    positive.
  - `(2n, 0)`: `dSeries.coeff (2n) = 0` (out of range, since `2n > 2(n-1)`).
  - Odd indices: `dSeries.coeff = 0` (only even powers).

  Rearranging: `2(2n+1) · cInverseLog n = -∑ (positive) < 0`, so
  `cInverseLog n < 0`. ✓

**Risk**: the antidiagonal-splitting via `Finset.sum_filter` on
parity + range is the heaviest manual step. If it stalls beyond
~80 LOC, fall back to:
* `Nat.rec` direct induction with explicit `n = 0 | n = 1 | n + 2`
  cases, OR
* a `match n with` on `n` then `Fin.sum_univ_*`-style explicit
  enumeration for small cases combined with a generic step.

## DO NOT try (from history)

* **DO NOT** attempt to compile `Section441.lean` directly — 42
  consecutive 5-min timeouts (cycles 182–237, 56 calendar days).
  Use `Section441B.lean` exclusively.
* **DO NOT** import `Mathlib.Data.Nat.Parity` — does not exist in
  this Mathlib version. The Even-on-Nat lemmas are in
  `Mathlib.Algebra.Ring.Parity` (cycle 237 dead end).
* **DO NOT** rely on bare `import Mathlib` — `Section441B.lean` is
  a stand-alone file and needs explicit imports including
  `Mathlib.Data.Real.Basic` for `ℝ` (cycle 237 dead end).
* **DO NOT** use positional `R` argument on `PowerSeries.coeff` /
  `constantCoeff` — `R` is implicit; use named-implicit `(R := ℝ)`
  (cycle 237 dead end).
* **DO NOT** define `cInverseLog` via the (441d) recurrence —
  circular. The existing cycle 237 definition
  `cInverseLog n := coeff (2n) cSeries` is correct; (441d) is used in
  the *proof* of negativity, not in the definition.
* **DO NOT** smuggle the negativity claim into the *definition* of
  `cInverseLog`. The negativity must be a *theorem*, not the
  definition (CLAUDE.md "definition smuggling check").
* **DO NOT** add an `axiom` or `constant` declaration for any step.
* **DO NOT** raise `maxHeartbeats` above 200000. Decompose instead.
* **DO NOT** try `Units.val_inv_eq_inv_val` — after
  `constantCoeff_invOfUnit` reduction the term is already in
  `(↑u)⁻¹` form; use `simp [twoUnit]` directly (cycle 237 lesson).

## Procedure — sorry-first discipline

Per CLAUDE.md's "sorry-first (ABSOLUTE RULE)":

1. **Open `Section441B.lean`** (the cycle-237 file).
2. **Add `dSeries`, `coeff_dSeries_*` simp lemmas with sorry'd
   bodies** (Step C.1). Verify the file compiles
   (`lake env lean OpenMath/Chapter4/Section441B.lean`).
3. **Add `dSeries_mul_cSeries_eq` with sorry'd body** (Step C.2).
4. **Add `coeff_dSeries_neg` with sorry'd body** (Step C.3).
5. **Add `cInverseLog_neg` with sorry'd body** (Step C.4).
6. **Compile** — confirm `sorry` count is exactly 4 (one per step).
7. **Batch-submit the four sorries to Aristotle** with the full
   `Section441B.lean` as context (free compute — submit per
   CLAUDE.md "Aristotle-first MANDATORY" via
   `mcp__aristotle__submit_file` on `Section441B.lean` with the
   sorries in place). Sleep 30 minutes, poll once.
8. **In parallel** (during sleep), close the easiest sub-steps
   manually:
   - Step C.3 (`coeff_dSeries_neg`) is the smallest (just numerical
     sign analysis on the explicit closed form). ~15 LOC.
   - Step C.1 (`dSeries` + coeff simp lemmas). ~30 LOC.
9. **After Aristotle poll**: incorporate any returned proofs. Then
   manually finish remaining sorries. Step C.2 and Step C.4 are
   the substantive ones, ~50 LOC each.

## Faithfulness check (mandatory pre-commit)

Per CLAUDE.md, before commit:

* **Quote textbook**: Butcher §441 p. 376: "Lemma 441B. The
  coefficients `c₂, c₄, …` are all negative."
* **Lean statement**: `cInverseLog_neg : ∀ n ≥ 1, cInverseLog n < 0`,
  where `cInverseLog k := coeff (2k) cSeries` matches Butcher's
  `c_{2k}` (re-indexed). **Captures: same content** (up to trivial
  re-indexing — documented in cycle 237 issue file update).
* **No definition smuggling**: `cInverseLog` is defined as a
  PowerSeries coefficient of an algebraically-inverted series
  (not as "the negative sequence"). The negativity is a theorem.
* **No tautology**: the proof routes through (441d) which is a
  non-trivial algebraic identity; it is not `id` or `exact h`.
* **Hypothesis strength**: only `n ≥ 1` (matches Butcher's `c₂, c₄, …`
  indexing convention starting from `c₂`).
* **Verify absent-theorem promises**: if any docstring promises
  helper lemmas, ensure they exist.

## Cycle 238 deliverable bar

* **Primary success** (target): `lem:441B` Phase C closed.
  `cInverseLog_neg` axiom-clean. Update `lean_status.json` row
  `lem:441B`: `partial → formalized`. Update `plan.md` row:
  `[~] → [x]`.
* **Acceptable partial success**: 2-3 of the 4 sub-steps closed
  (C.1, C.3 most likely); the others remain as sorries with clear
  closure paths. Sorry count rises ≤ 2 net. `lem:441B` stays
  `partial` but with substantial progress recorded.
* **Minimum acceptable**: Step C.1 (the `dSeries` definition +
  coefficient simp lemmas) lands axiom-clean. This is the
  infrastructure for cycles 239+. Sorry count rises ≤ 3 net.

## GPFS pathology

Per cycle 182-237 pattern, **DO NOT** run smoke tests on
`Section441.lean` this cycle (43rd timeout would be wasted compute).
The pathology is specific to the `Mathlib.Analysis.*` heavy
transitive load of `Section441.lean`. `Section441B.lean` (Mathlib
`PowerSeries` + `Polynomial` + `Real`) has no `Mathlib.Analysis.*`
dependency and is unaffected.

Append a one-liner to
`.prover-state/issues/cycle_182_gpfs_slowness.md` **only if** you
observe GPFS issues on `Section441B.lean` itself this cycle. Do not
add a 43rd entry for `Section441.lean`.

## Backup plan — if Phase C C.2 (441d identity) blocks

If Step C.2 (the (441d) PowerSeries identity) proves intractable in
this cycle (estimated >100 LOC or hits a `simp` blowup), pivot to:

**Option B — close `lem:441B` Phase C for `n = 2` only** as a
concrete stepping stone, mirroring the §550 thm:550A stepping-stone
pattern from cycles 138/140/144/145/147/148/150:

```lean
theorem cInverseLog_two_neg : cInverseLog 2 < 0
```

Compute `cInverseLog 2` by direct unfolding of the (441c) inverse
PowerSeries at index 4 (use `coeff_invOfUnit` + `coeff_mul` to set
up a linear equation in `c_4`). Solve and verify `< 0`.

If even the `n = 2` case stalls, write an issue file
`.prover-state/issues/lem_441B_phase_C_blockers.md` documenting
the specific stall point, then pivot the cycle deliverable to
**`thm:384A` Φ as a group hom**: ship the `Equivalent → PhiEquivalent`
inclusion lemma (the deferred direction in
`thm_381H_deferred.md`) as a precursor to `Φ : Quotient
Equivalent.setoidSigma →* Quotient PhiEquivalent.setoidSigma`. This
is a different file (`Section381.lean`) and should compile healthy
(cycle 222 shipped the §382 `Group` instance there at 9.657s warm).
