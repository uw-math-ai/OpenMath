# Cycle 238 Results

## Worked on

`lem:441B` Phase C — strict negativity of `cInverseLog n` for
`n ≥ 1`. Headline `cInverseLog_neg` and all four planner sub-steps
(C.1–C.4) closed axiom-clean in
`OpenMath/Chapter4/Section441B.lean`. `lem:441B` status
transitions `partial → formalized`.

## Approach

Followed cycle 238 strategy verbatim, with one simplification:
**defined `dSeries` algebraically** instead of via the closed-form
conditional (the strategy's suggested form), which turned out to
collapse Step C.2 into a one-line `mul_assoc + (441c) + mul_one`
rewrite.

### Step C.1 — `dSeries` + coefficient simp lemmas (~50 LOC)

- `dSeries (n : ℕ) := (C(2n+1) - C(2n-1)·X²) · cInverseLogSeries`.
- `coeff_dSeries_zero`: `coeff 0 (dSeries n) = 2(2n+1)`.
  Proof: `unfold dSeries; rw [coeff_zero_eq_constantCoeff]; simp
  [cInverseLogSeries_constantCoeff_eq_two]; ring`.
- `coeff_dSeries_odd`: odd coefficients vanish.
  Proof: distribute via `sub_mul + map_sub + coeff_C_mul +
  coeff_X_pow_mul'`, then `simp [coeff_cInverseLogSeries, h]`, then
  prove `¬ Even (k - 2)` from `¬ Even k` via `⟨a+1, by omega⟩`.
- `coeff_dSeries_two_mul`: closed form `-8(n-i)/((2i+1)(2i-1))` for
  `i ≥ 1`. Proof: same distribute, `if_pos h2i`, evaluate the two
  `cInverseLogSeries` coeffs (both even), cast `(2i ± 1 : ℕ) → ℝ`,
  then `field_simp; ring`.

### Step C.2 — (441d) identity (3 LOC, the strategic shortcut)

```lean
theorem dSeries_mul_cSeries_eq (n : ℕ) :
    dSeries n * cSeries = C(2n+1) - C(2n-1) * X^2 := by
  unfold dSeries
  rw [mul_assoc, cInverseLogSeries_mul_cSeries_eq_one, mul_one]
```

Because `dSeries := (P) · cInverseLogSeries` and `cInverseLogSeries
· cSeries = 1` (cycle 237 (441c)), we get `dSeries · cSeries = P ·
cInverseLogSeries · cSeries = P · 1 = P` trivially. No
coefficient-by-coefficient calculation required. **This was the
key strategic simplification of the cycle.**

### Step C.3 — Sign of d_{2i} (~10 LOC)

```lean
theorem coeff_dSeries_neg (n i : ℕ) (h₁ : 1 ≤ i) (h₂ : i ≤ n - 1) :
    coeff (2*i) (dSeries n) < 0
```

Proof: `rw [coeff_dSeries_two_mul n i h₁]`, then numerator `-8(n -
i) < 0` (since `n - i ≥ 1`) and denominator `(2i+1)(2i-1) > 0`
(since `i ≥ 1`) via `nlinarith`, then `div_neg_of_neg_of_pos`.

### Step C.4 — Strong induction headline (~80 LOC)

```lean
theorem cInverseLog_neg : ∀ n, 1 ≤ n → cInverseLog n < 0
```

Proof structure:
1. `induction n using Nat.strong_induction_on`.
2. Base case `n = 1`: `rw [show n = 1 from by omega]; exact
   cInverseLog_one_neg`. (Note: `interval_cases` not in scope —
   `Mathlib.Tactic.IntervalCases` not imported in
   `Section441B.lean` for cleanliness. Replaced with `omega + rw`.)
3. Inductive step `n ≥ 2`:
   - Extract `coeff (2n) (dSeries n * cSeries) = 0` via
     `dSeries_mul_cSeries_eq` (RHS coeff `(C(2n+1) - C(2n-1)·X²)`
     at index `2n` is `0` for `n ≥ 2` via `coeff_C +
     coeff_C_mul + coeff_X_pow + 2n ≠ 0, ≠ 2`).
   - Expand `PowerSeries.coeff_mul` to get antidiagonal sum.
   - Isolate `(0, 2n)` via `Finset.add_sum_erase`. The `(0, 2n)`
     contribution simp'd via `coeff_dSeries_zero` plus `coeff (2n)
     cSeries = cInverseLog n` (definitional).
   - Isolate `(2, 2n-2)` further via second `Finset.add_sum_erase`.
     This term is `d_2 · cInverseLog (n-1)`, strictly positive
     because both factors negative (the strict-positive witness).
   - Show the remaining double-erased sum is `≥ 0` via
     `Finset.sum_nonneg`, by case analysis on each `(p, q)`:
     * `p` odd ⇒ `coeff p (dSeries n) = 0` (`coeff_dSeries_odd`).
     * `p = 2i` with `i = 0` ⇒ excluded by `hne0` (the `(0, 2n)`
       exclusion). Derive contradiction.
     * `p = 2i` with `i = 1` ⇒ excluded by `hne2` (the `(2, 2n-2)`
       exclusion).
     * `p = 2i` with `i = n` (so `q = 0`) ⇒ `d_{2n} = 0` via
       `coeff_dSeries_two_mul n n; ring` — the term is `0 · _ = 0`.
     * `p = 2i` with `2 ≤ i ≤ n - 1` ⇒ `d_{2i} < 0`
       (`coeff_dSeries_neg`) and `cInverseLog (n - i) < 0` by IH
       (since `1 ≤ n - i ≤ n - 1 < n`). Product positive.
   - Conclude: `hKey : 2(2n+1)·cInverseLog n + (pos) + (≥0) = 0`,
     `2(2n+1) > 0`, so `cInverseLog n < 0` via `nlinarith`.

## Result

**SUCCESS — Phase C fully shipped axiom-clean.**

Cycle 238 new public declarations in `Section441B.lean` (6 new,
in addition to cycle 237's 12):

| Symbol | Kind | Role |
|---|---|---|
| `dSeries` | `noncomputable def` | `(C(2n+1) - C(2n-1)·X²) · cInverseLogSeries` |
| `dSeries_mul_cSeries_eq` | `theorem` | (441d) identity |
| `coeff_dSeries_zero` | `@[simp] lemma` | Constant term `2(2n+1)` |
| `coeff_dSeries_odd` | `lemma` | Odd coefficients vanish |
| `coeff_dSeries_two_mul` | `lemma` | Closed form `-8(n-i)/((2i+1)(2i-1))` |
| `coeff_dSeries_neg` | `theorem` | `d_{2i} < 0` for `1 ≤ i ≤ n-1` |
| `cInverseLog_neg` | `theorem` | **HEADLINE — `lem:441B`** |

All axiom-clean: `[propext, Classical.choice, Quot.sound]`.

File: 312 LOC total (+~130 LOC over cycle 237's 182 LOC).
Compile: 4.7s warm, ~7.1s clean.

Sorry count: 0 (unchanged).

Aristotle: submitted at cycle 238 minute 0 with the
sorry-first structure as safety net; cancelled at minute 12 (3%
complete) once local proofs verified. Free compute well-spent — no
need to consume further.

## Faithfulness check

For each new `def` and `theorem` introduced this cycle:

### `dSeries`

Entity ID and textbook statement (Butcher §441 p. 376, eq.
(441d)):

> "We multiply (441c) by `2n + 1 − (2n − 1)z²`. We find
> `(∑_{i=0}^∞ d_{2i} z^{2i}) · (∑_{i=0}^∞ c_{2i} z^{2i}) = 2n+1 −
> (2n−1)z²`, where, for `i = 1, 2, …, n`, `d_{2i} = 2(2n+1)/(2i+1)
> − 2(2n−1)/(2i−1) = −8(n−i)/((2i+1)(2i−1))`."

Lean: `dSeries (n : ℕ) := (C(2n+1) - C(2n-1)·X²) · cInverseLogSeries`.

This is algebraically equivalent to Butcher's `∑_{i=0}^∞ d_{2i}
z^{2i}` series — proved by computing coefficients in
`coeff_dSeries_zero` (`d_0 = 2(2n+1)`),
`coeff_dSeries_two_mul` (`d_{2i} = -8(n-i)/((2i+1)(2i-1))` for `i ≥
1`, matches Butcher verbatim), and `coeff_dSeries_odd` (odd coeffs
zero, consistent with Butcher's `∑ d_{2i} z^{2i}` having only even
powers). **Captures: same content** (algebraic vs closed-form;
equivalence proved as lemmas).

### `dSeries_mul_cSeries_eq`

Textbook: equation (441d) itself.

Lean: `dSeries n * cSeries = C(2n+1) - C(2n-1)·X²`.
**Captures: same content** (identity (441d) verbatim).

### `coeff_dSeries_zero`, `coeff_dSeries_odd`, `coeff_dSeries_two_mul`

These three lemmas decode the `dSeries` algebraic definition into
Butcher's explicit coefficient formulas:

* `coeff 0 dSeries = 2(2n+1)` = Butcher's implicit `d_0`.
* odd coeffs zero = Butcher's `∑ d_{2i} z^{2i}` only-even-powers.
* `coeff (2i) dSeries = -8(n-i)/((2i+1)(2i-1))` for `i ≥ 1` =
  Butcher's explicit `d_{2i}` formula.

**Captures: same content** (closed-form decoding).

### `coeff_dSeries_neg`

Textbook (Butcher §441 p. 376): "so that `d_{2i} < 0`, for `i = 1,
2, …, n − 1`, and `d_{2n} = 0`."

Lean: `coeff_dSeries_neg (n i : ℕ) (h₁ : 1 ≤ i) (h₂ : i ≤ n - 1) :
coeff (2*i) (dSeries n) < 0`.

**Captures: same content** (the strict negativity claim for `1 ≤ i
≤ n-1`; the `d_{2n} = 0` boundary case is used inside the C.4
proof via `coeff_dSeries_two_mul n n` evaluating to `0` by `ring`).

### `cInverseLog_neg` (headline)

Textbook (Butcher Lemma 441B, p. 376):

> "The coefficients `c_2, c_4, …` are all negative."

Lean: `cInverseLog_neg : ∀ n : ℕ, 1 ≤ n → cInverseLog n < 0`,
where `cInverseLog k := coeff (2k) cSeries` matches Butcher's
`c_{2k}` (re-indexed by halving the textbook subscript: my `n`
corresponds to Butcher's `2n`).

**Captures: same content.** The textbook indexing starts from
`c_2 = c_{2·1}`, which corresponds to `cInverseLog 1` in my
indexing. The condition `1 ≤ n` faithfully captures Butcher's
"c_2, c_4, …" (starting from `c_2`, excluding `c_0 = 1/2 > 0`).

**No tautology**: the conclusion `cInverseLog n < 0` does not
appear as a hypothesis. The hypothesis is `1 ≤ n`.

**No definition smuggling**: `cInverseLog n` is defined (cycle 237)
as `coeff (2n) cSeries` where `cSeries` is the algebraic
PowerSeries inverse of `cInverseLogSeries`. The negativity is a
genuine theorem requiring a non-trivial proof routing through the
(441d) auxiliary `dSeries`.

**No vacuous identity proof**: the proof uses
`Nat.strong_induction_on` with two distinct cases (`n = 1` and `n
≥ 2`), the inductive step extracts and manipulates a power-series
coefficient identity, and the conclusion follows from
`nlinarith` over five non-trivial intermediate inequalities.

**Hypothesis strength**: `1 ≤ n` is the tightest hypothesis
matching Butcher (excludes `n = 0` because `c_0 = 1/2 > 0`).

## Dead ends

1. **`PowerSeries.C ℝ` positional argument**: First wrote
   `PowerSeries.C ℝ (2*n+1)` (positional `ℝ`), got
   `failed to synthesize HAdd ℝ ℕ (Unit →₀ ℕ)`. Fix: `R` is a
   named-implicit; use `PowerSeries.C (R := ℝ)` (matches the
   cycle-237 `PowerSeries.coeff (R := ℝ)` idiom).
2. **`interval_cases` unknown tactic**: Used `interval_cases n` to
   handle the `n = 1` base case but the tactic is not in scope —
   `Mathlib.Tactic.IntervalCases` is not in the import list. Fix:
   `have : n = 1 := by omega; rw [this]`.
3. **`rfl` failed on `(0, 2*n).1 + (0, 2*n).2 = 2 * n`**: The
   `Prod.fst/snd` reduce but `Nat.zero_add` is not definitionally
   firing. Fix: replace `rfl` with `simp` (rewrites via the
   `zero_add` simp lemma).
4. **`field_simp` introduced spurious goal in the i = n case of
   the antidiagonal split**: The closed form `-8(n-n)/((2n+1)(2n-1))
   = 0` requires `ring` not `field_simp`, because the numerator
   `n - n = 0` makes the whole expression `0` algebraically
   without dividing. Fix: drop `field_simp` and use plain `ring`.

## Discovery

1. **Algebraic-vs-closed-form trade-off**: The strategy proposed a
   closed-form conditional definition of `dSeries`. The algebraic
   definition `(C(2n+1) - C(2n-1)·X²) · cInverseLogSeries` is
   *equivalent* but trades a 3-LOC `(441d)` identity proof
   (`mul_assoc + (441c) + mul_one`) for a slightly more involved
   coefficient decoder. Net: shorter and conceptually clearer.
   **General principle**: when a textbook auxiliary is defined as
   the product of known objects, prefer the algebraic definition —
   the multiplicative identity becomes free, and the closed-form
   coefficient lemmas are no harder than they would have been for
   the conditional definition.

2. **Antidiagonal split via double `Finset.add_sum_erase`**: For
   the strong induction step, isolating two specific terms `(0,
   2n)` and `(2, 2n-2)` via two successive applications of
   `Finset.add_sum_erase` worked cleanly. The double-erased
   remainder is then handled by `Finset.sum_nonneg` with a
   case-analysis on parity and index range. This pattern
   generalizes to other "split off the main term + the strict
   witness + bound the rest" power-series-coefficient arguments.

3. **Parity reasoning via `Even` constructor**: To prove `¬ Even
   (k - 2)` from `¬ Even k` (when `k ≥ 2`), use the constructor:
   `fun ⟨a, ha⟩ => h ⟨a + 1, by omega⟩`. Pattern: given `Even (k -
   2) = ⟨a, k - 2 = a + a⟩`, derive `Even k = ⟨a + 1, k = (a+1) +
   (a+1)⟩`.

4. **Stand-alone file pays off**: `Section441B.lean` continued to
   compile in <5s warm and <10s clean throughout the cycle, while
   `Section441.lean` (the GPFS-pathology-blocked sibling) was
   never touched. The cycle 237 decision to bifurcate Phase B/C
   into a stand-alone universal-PowerSeries file paid off in cycle
   238 — the headline `lem:441B` is now closed without ever
   needing `Section441.lean` to compile.

## Suggested next approach

* **`lem:441A` is the dependent claim** (`lem:441B` is a
  dependency of `lem:441A`, per
  `formalization_data/entities/lem_441B.json`'s `dependents`
  list). The natural next target. `lem:441A` is currently blocked
  on the GPFS pathology in `Section441.lean` (Phase C.2 draft, see
  cycle 184 task results). With `lem:441B` now closed and
  axiom-clean, the planner should consider whether a similar
  bifurcation (a `Section441C.lean` or `Section441D.lean`
  stand-alone file) could close any of `lem:441A`'s Phase C
  sub-phases without touching the blocked file.
* **`thm:441C`** is the headline using both `lem:441A` and
  `lem:441B`. Stays blocked until `lem:441A` is closed.
* **§383/§384 group-hom path** (cycles 233–236) — independent
  progress channel; the §441-blocked-by-GPFS pathology does not
  affect it.
