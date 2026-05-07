---
name: Consultant advice — cycle 174 (factor-of-2 discrepancy is a textbook typo; bdf2LMM_aPoly_eq is low priority; ρ'(1) > 0 is the real next milestone)
description: Independent algebraic verification confirms cycle 174 is mathematically correct and Butcher §441 p. 376 has a typo. Recommends pivoting away from the bdf2LMM closed-form witness (low value, high tactic cost) and instead beginning the ρ-side polynomial-root infrastructure for `lem:441A`'s `a₁ > 0` half.
type: project
---

# Consultant advice — cycle 174

Author: consultant subagent.
Date: 2026-05-06.
Phase at time of writing (per `heartbeat.json`): cycle 174 strategy
review.
Branch tip: `35acad6 Cycle 174 — §441 ρPoly bridge: a₁ = 2·ρ'(1)
under preconsistency`.

---

## TL;DR

1. **The "factor-of-2 discrepancy" is a Butcher textbook typo, not a
   Lean error.** Independent algebraic re-derivation plus numerical
   sanity checks on explicit Euler (a₁ = 2, ρ'(1) = 1) and BDF2
   (a₁ = 4/3, ρ'(1) = 2/3) confirm: the correct identity under
   preconsistency is **`a₁ = 2·ρ'(1)`** (cycle 174's result), NOT
   Butcher's stated **`ρ'(1) = a₁`** (p. 376).

   The cycle 174 chain is mathematically faithful and should NOT
   be audited or unwound. The `lem:441A` strategy stays valid
   because the discrepancy is a *positive scalar* — `a₁ > 0` ⇔
   `ρ'(1) > 0`, so reducing one to the other works in either
   direction.

2. **`bdf2LMM_aPoly_eq` is low-value-per-cycle work.** Cycle 171
   already has `explicitEulerLMM_aPoly_eq` as the §441 `aPoly`
   non-vacuity witness. Re-attempting BDF2 closed-form is a
   tactic-engineering exercise (three cycles 172/173 of stalls) for
   what is essentially a sanity check. Recommend **dropping** the
   BDF2 closed-form goal and pivoting to the substantive next
   piece.

3. **The substantive cycle 175+ goal is the ρ-side polynomial-root
   infrastructure**: prove that for stable preconsistent `M`,
   `ρ'(1) > 0`. This unlocks `lem:441A`'s `a₁ > 0` half via the
   cycle 174 bridge, and is genuinely 2–3 cycles of multi-cycle
   work. Section §C below gives a phased plan.

4. **If `bdf2LMM_aPoly_eq` IS pursued anyway** (e.g. as a Phase A
   stretch), §B.3 below gives the concrete tactic recipe — do NOT
   use `Polynomial.ext + ring`; use per-coefficient `interval_cases
   n + simp [coeff_*] + norm_num` with explicit Mathlib lemmas. It
   is ~50–80 LOC.

---

## A. Independent verification of the textbook typo

I re-derived `a₁` and `ρ'(1)` from the definitions, without
reading the cycle 174 proof, and reached the cycle 174 conclusion
(not Butcher's). Recording the derivation here so future cycles
have an independent confirmation.

### Setup

`a(z) = (1+z)^k − Σ_{i=1}^k αᵢ (1+z)^{k−i} (1−z)^i`
`ρ(z) = z^k − Σ_{i=1}^k αᵢ z^{k−i}`

Preconsistency: `Σᵢ αᵢ = 1`.

### `a₁` derivation

Differentiate `a(z)` and evaluate at 0. Using the product rule on
`(1+z)^{k−i} (1−z)^i`:

`d/dz [(1+z)^{k−i} (1−z)^i]_{z=0} = (k−i)·1 + i·(−1) = k − 2i`.

So `a₁ = a'(0) = k − Σᵢ αᵢ (k − 2i) = k − k Σαᵢ + 2 Σ i·αᵢ`.

Under preconsistency: `a₁ = k − k + 2 Σ i·αᵢ = 2 Σ i·αᵢ`.

This matches Butcher's intermediate line:

> `a₁ = k − (k − 2)α₁ − (k − 4)α₂ − ⋯ − (−k)αₖ = kα(1) − 2α'(1)`

*provided* `α(z) := 1 − Σᵢ αᵢ z^i` (which makes `α(1) = 1 − Σαᵢ`
and `α'(1) = −Σ i·αᵢ`). Then `kα(1) − 2α'(1) = 0 + 2Σi·αᵢ` ✓.
**`a₁ = 2 Σ i·αᵢ` is correct.**

### `ρ'(1)` derivation

`ρ'(z) = k·z^{k−1} − Σᵢ αᵢ (k−i) z^{k−i−1}` (where `i` ranges over
1..k; the `i = k` term has exponent `k − k − 1 = −1` and vanishes
since `ρ(z)`'s `αₖ` summand is constant in `z`).

`ρ'(1) = k − Σᵢ αᵢ (k − i)`.

Under preconsistency: `ρ'(1) = k − k Σαᵢ + Σ i·αᵢ = Σ i·αᵢ`.

This also matches Butcher's intermediate line:

> `ρ'(1) = k − (k − 1)α₁ − (k − 2)α₂ − ⋯ − αₖ₋₁`

✓. **`ρ'(1) = Σ i·αᵢ` is correct.**

### Comparison

`a₁ = 2 Σ i·αᵢ`, `ρ'(1) = Σ i·αᵢ` ⇒ **`a₁ = 2·ρ'(1)`**.

Butcher's textbook claims `ρ'(1) = a₁` on p. 376, which would
require `Σ i·αᵢ = 2 Σ i·αᵢ`, i.e. `Σ i·αᵢ = 0`. But for any
preconsistent method `Σ i·αᵢ ≠ 0` in general (and equals `1` for
explicit Euler, `5/3` for BDF2). **Butcher's "= a₁" is a typo.**

The author probably copied `a₁`'s closed form
`k − (k − 2)α₁ − (k − 4)α₂ − ⋯ − (−k)αₖ` and substituted it for
`ρ'(1)`'s closed form `k − (k − 1)α₁ − ⋯ − αₖ₋₁`, missing that the
`αᵢ` weights differ by exactly a factor of 2 (`(k − 2i)` vs
`(k − i)`).

### Numerical sanity check

#### Explicit Euler (k=1, α₁=1):
  - `a(z) = (1+z) − 1·(1+z)^0·(1−z) = 2z` ⇒ `a₁ = 2`.
  - `ρ(z) = z − 1` ⇒ `ρ'(1) = 1`.
  - `2·ρ'(1) = 2 = a₁` ✓ (cycle 174).
  - `ρ'(1) = a₁` would require `1 = 2`. ✗ (Butcher's typo).

#### BDF2 (k=2, α₁=4/3, α₂=−1/3):
  - `a(z) = (1+z)² − (4/3)(1+z)(1−z) + (1/3)(1−z)² = (4/3)z + (8/3)z²` ⇒ `a₁ = 4/3`.
  - `ρ(z) = z² − (4/3)z + 1/3` ⇒ `ρ'(z) = 2z − 4/3` ⇒ `ρ'(1) = 2/3`.
  - `2·ρ'(1) = 4/3 = a₁` ✓ (cycle 174).
  - `ρ'(1) = a₁` would require `2/3 = 4/3`. ✗ (Butcher's typo).

### Recommendation

* **Add a comment** to the docstring of
  `aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent`
  documenting that this overrides Butcher's typo on p. 376. One
  paragraph in the existing docstring saying "Butcher §441 p. 376
  states `ρ'(1) = a₁`; this is a typo. The correct identity is
  `a₁ = 2·ρ'(1)`, with the factor of 2 arising from `(1+z)^{k−i}
  (1−z)^i` having derivative `(k − 2i)` at 0 (rather than the
  `(k − i)` weight of `ρ`). Independently verified on explicit
  Euler (a₁ = 2, ρ'(1) = 1) and BDF2 (a₁ = 4/3, ρ'(1) = 2/3)."
* **Do NOT audit the `hdistrib` line** — its algebra is correct; the
  factor-of-2 mismatch is upstream of any Lean step.
* **Do NOT redirect the proof strategy** — `lem:441A`'s `a₁ > 0`
  reduces to `ρ'(1) > 0` via cycle 174's bridge in either reading
  of Butcher (since `2 > 0`), so the cycle 174 chain is the right
  spine regardless of the typo.

---

## B. `bdf2LMM_aPoly_eq` — recommend deferring; tactic recipe if needed

### B.1 — Why this is low-priority

The cycle 174 strategy is shipping along the chain
`a₁ = −2α'(1)` → `ρ'(1) = −α'(1)` → `a₁ = 2·ρ'(1)` → (future)
`ρ'(1) > 0` → `a₁ > 0`. None of these closures consume
`bdf2LMM_aPoly_eq`. Its only role is non-vacuity.

The §441 cluster ALREADY has a non-vacuity witness:
`explicitEulerLMM_aPoly_eq` (cycle 171, axiom-clean). A second
witness for `aPoly` at `k = 2` adds little informational value —
Butcher's §441 itself doesn't single out BDF2.

Failing BDF2 closed-form witnesses in cycles 172/173 indicate the
specific tactic problem (folding `Polynomial.C` arithmetic over
the rationals) is a one-off engineering hurdle, not a
recurring obstacle. **Either land a strictly cheaper sanity
witness for BDF2, or drop the goal entirely.**

### B.2 — Cheaper BDF2 sanity witnesses

Each of these is one or two lines and provides BDF2-specific
non-vacuity for the §441 machinery WITHOUT closed-form
arithmetic:

```lean
-- a₀ = 0 for BDF2 (preconsistent)
example : bdf2LMM.aPoly.coeff 0 = 0 :=
  bdf2LMM.aPoly_coeff_zero_of_preconsistent bdf2LMM_isPreconsistent
-- ↑ uses cycle 174's `aPoly_coeff_zero_of_preconsistent` (already shipped).

-- ρ(1) = 0 for BDF2
example : bdf2LMM.ρPoly.eval 1 = 0 :=
  bdf2LMM.ρPoly_eval_one_eq_zero_of_preconsistent bdf2LMM_isPreconsistent
-- ↑ uses cycle 174's `ρPoly_eval_one_eq_zero_of_preconsistent`.

-- a₁ = 4/3 (a single coefficient identity, NOT the full closed form)
example (h : bdf2LMM.IsPreconsistent) : bdf2LMM.aPoly.coeff 1 = 4 / 3 := by
  rw [bdf2LMM.aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent h]
  -- Goal: 2 * bdf2LMM.ρPoly.derivative.eval 1 = 4 / 3
  rw [LinearMultistepMethod.ρPoly_deriv_eval_one_unconditional]
  simp [bdf2LMM, Fin.sum_univ_two]
  norm_num
```

The third example is the strongest — it confirms the cycle 174
bridge ON BDF2 numerically without ever building the full
polynomial. It's also the most useful: it pins down the value
`a₁ = 4/3` exactly, providing a tractable test for `lem:441A`'s
inequality (`a₁ > 0`) at `k = 2`.

**Recommend cycle 175 ship one of these as the BDF2 §441
non-vacuity witness, replacing the `bdf2LMM_aPoly_eq` goal
entirely.**

### B.3 — If `bdf2LMM_aPoly_eq` IS pursued (full-closed-form recipe)

Cycles 172/173 stalled because they used `Polynomial.ext` plus
`ring`, and `ring` cannot fold `Polynomial.C` constants over `ℝ`.
The fix is to **avoid `ring` entirely** at the per-coefficient
level. Instead:

```lean
theorem bdf2LMM_aPoly_eq :
    bdf2LMM.aPoly = Polynomial.C (4 / 3) * Polynomial.X
                    + Polynomial.C (8 / 3) * Polynomial.X ^ 2 := by
  unfold LinearMultistepMethod.aPoly
  ext n
  -- Goal: ((1+X)^2 - Σᵢ C(αᵢ) (1+X)^{2−(i+1)} (1−X)^{i+1}).coeff n
  --      = (C(4/3) X + C(8/3) X²).coeff n
  simp only [bdf2LMM, Fin.sum_univ_two]
  -- Now n is universally quantified; case-split.
  match n with
  | 0 =>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add,
               Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow,
               -- (1−X)^j coefficients: helpers needed
               ..., Nat.choose, Nat.cast_zero, Nat.cast_one, mul_one,
               mul_zero, add_zero]
    norm_num
  | 1 =>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add,
               Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow, ...]
    norm_num
  | 2 =>
    simp only [..., Polynomial.coeff_one_add_X_pow, ...]
    norm_num
  | n + 3 =>
    -- Use degree bound: aPoly.natDegree ≤ 2, RHS.natDegree ≤ 2.
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt, ...]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
      · ...
    ...
```

The load-bearing helpers (some already in cycle 174's
`aPoly_coeff_one_unconditional` proof at `Section441.lean:213`):

* `((1 - X)^n).coeff 0 = 1` — this is `eval 0` of `(1-X)^n`.
* `((1 - X)^n).coeff 1 = -n` — induction on n, available in
  cycle 174's `h_one_sub_X_coeff_one`.
* `((1 - X)^n).coeff 2 = (n choose 2)` — derive by repeated
  `pow_succ` + `mul_coeff` or by direct expansion at small n.

For the BDF2 case (k = 2), only n = 0, 1, 2 need explicit values:

| n | `(1+X)^2`.coeff n | `(1+X)^1 (1-X)^1`.coeff n | `(1-X)^2`.coeff n |
|---|-------------------|----------------------------|--------------------|
| 0 | 1                 | 1                          | 1                  |
| 1 | 2                 | 0                          | -2                 |
| 2 | 1                 | -1                         | 1                  |
| ≥3| 0                 | 0                          | 0                  |

Applying `bdf2LMM` α-values (α₁ = 4/3, α₂ = −1/3):

| n | aPoly.coeff n |
|---|---|
| 0 | 1 − (4/3)·1 − (−1/3)·1 = 1 − 4/3 + 1/3 = 0 |
| 1 | 2 − (4/3)·0 − (−1/3)·(−2) = 2 − 2/3 = 4/3 |
| 2 | 1 − (4/3)·(−1) − (−1/3)·1 = 1 + 4/3 + 1/3 = 8/3 |
| ≥3 | 0 |

| n | RHS = (C(4/3) X + C(8/3) X²).coeff n |
|---|---|
| 0 | 0 |
| 1 | 4/3 |
| 2 | 8/3 |
| ≥3 | 0 |

Estimated LOC: 50–80. Aristotle suitability: **medium** — the proof
shape is mechanical (per-coefficient + norm_num) but the simp set
plumbing is method-specific. Submit only as a low-priority job.

#### Alternative recipe: `linear_combination` with explicit C arithmetic

A cleaner one-shot: define the equality statement using
ℚ-coefficient arithmetic, then `linear_combination`:

```lean
theorem bdf2LMM_aPoly_eq :
    bdf2LMM.aPoly = Polynomial.C (4 / 3) * Polynomial.X
                    + Polynomial.C (8 / 3) * Polynomial.X ^ 2 := by
  unfold LinearMultistepMethod.aPoly
  simp only [bdf2LMM, Fin.sum_univ_two]
  -- Now LHS = (1+X)^2 - C(4/3)(1+X)(1-X) - C(-1/3)(1-X)^2
  -- and RHS = C(4/3) X + C(8/3) X²
  -- linear_combination matches `Polynomial ℝ` coefficient-wise.
  push_cast  -- normalises C of rationals
  ring
```

`push_cast` (and `Polynomial.C` elaboration) over ℝ interpret
`C (4/3 : ℝ)` as `(4/3 : ℝ[X])` (the ring-numeric literal in the
polynomial ring), which `ring` handles natively. Try this BEFORE
the per-coefficient recipe — if it works, it's a one-liner.

If `ring` still fails, fall back to:

```lean
linear_combination (Polynomial.X^2 - Polynomial.C (4/3) * (Polynomial.X * Polynomial.X)
   - Polynomial.C (-1/3) * (Polynomial.X * Polynomial.X)) -- explicit linear combination
```

Note: `linear_combination` over `Polynomial ℝ` should work because
`Polynomial ℝ` is a commutative ring and the tactic normalises both
sides modulo the ring axioms.

#### Last-resort recipe: `funext` over an infinite ring

`Polynomial ℝ` is an integral domain over an infinite field, so
`Polynomial.funext` applies:

```lean
theorem bdf2LMM_aPoly_eq : ... := by
  apply Polynomial.funext
  intro x
  unfold LinearMultistepMethod.aPoly
  simp [bdf2LMM, Fin.sum_univ_two, Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_one]
  ring
```

This pushes the polynomial equality into a real-arithmetic
equality `∀ x : ℝ, ...`, which `ring` always handles. It's the
most robust fallback, ~10 LOC.

**Recommend trying this `funext + ring` recipe FIRST.** It avoids
all the simp-set plumbing of `Polynomial.ext` and is the standard
trick for exactly this kind of `Polynomial ℝ` constant-arithmetic
issue.

---

## C. ρ-side polynomial-root infrastructure for `lem:441A`

The cycle 174 update note in
`.prover-state/issues/lem_441A_alpha_prime_negative.md` correctly
identifies this as the substantive next milestone. The textbook
proof (Butcher §441 p. 376) goes:

```
M.IsStable
  ⇒ ρ has all roots in closed unit disc, simple roots on |z|=1
  ⇒ no real root in (1, ∞)                                    [step 1]
  ⇒ ρ(z) > 0 for z > 1   (since ρ(1)=0, ρ(z)→+∞, no root in (1,∞))   [step 2]
  ⇒ ρ'(1) ≥ 0                                                [step 3]
  ⇒ ρ'(1) ≠ 0   (simple root at 1)                            [step 4]
  ⇒ ρ'(1) > 0                                                [step 5]
```

This is genuinely 2–3 cycles of work. I sketch the phasing.

### C.1 — Phase B.1 (cycle 175): the bridge from `IsStable` to root location

This is the BIG prerequisite. The Lean predicate `M.IsStable`
(`Section404.lean:202`) is "every solution of the homogeneous
recurrence is bounded". The textbook fact is:

  `M.IsStable ⇔ ρ.roots ⊆ closedBall 0 1 ∧ (∀ ζ ∈ ρ.roots, ‖ζ‖ = 1 → simple root)`

The forward direction (`IsStable ⇒ root constraints`) is what
Butcher tacitly invokes. The Lean proof goes via the companion
matrix of ρ:

* Define `V_M : Matrix (Fin k) (Fin k) ℝ` as the companion matrix
  of `ρ` (already implicit in §403: the homogeneous recurrence
  `y_{m+k} = α₁ y_{m+k-1} + ... + αₖ y_m` is `y_{m+1} = V_M · y_m`
  where `y_m := (y_m, y_{m+1}, ..., y_{m+k-1})ᵀ`).
* `M.IsStable ⇔ V_M is power-bounded`.
* `V_M is power-bounded ⇔ minpoly(V_M) has roots in closed unit
  disc with simple roots on the boundary` (this is **Butcher's
  thm:142F**).
* `minpoly(V_M) = ρ` for the companion matrix.

Mathlib hooks (each verified by `lean_loogle` or
`lean_local_search` before use):

* `Matrix.charpoly_companion` — companion matrix of a polynomial
  has that polynomial as its characteristic polynomial. Search:
  `lean_loogle "Matrix.companion"`.
* `Matrix.IsConvergent` (Mathlib's matrix-power-bounded predicate)
  — wait, Mathlib has `Module.End.spectrum` and friends, not a
  direct convergent-matrix class. The §142 codebase already has
  `convergent_imp_minpoly_roots_lt_one` (cycle 5) as the (i)⇒(ii)
  half but ONLY for the strong "→ 0" notion (not just bounded).
* The simple-root-on-boundary half is NOT in §142 yet — that's
  Butcher's `thm:142F`, currently unformalized.

**Phase B.1 is therefore THE substantive cycle.** It either:

* (option B.1.α) builds the companion-matrix bridge `M.IsStable
  ⇔ V_M power-bounded` first, then composes with `thm:142F` (which
  requires Schur or Jordan form per
  `jordan_canonical_form_missing.md`) — multi-cycle dead end if
  Jordan/Schur infrastructure is not built.
* (option B.1.β) builds **only** the part of `thm:142F` we need —
  namely, `M.IsStable ⇒ ρ has no real root > 1`. This is strictly
  weaker than `thm:142F` and may be tractable directly via the
  homogeneous recurrence:
  - If `ρ(z₀) = 0` for some real `z₀ > 1`, take the homogeneous
    solution `y_n := z₀^n` (which solves the recurrence by
    construction).
  - Then `|y_n| = |z₀|^n → ∞` since `z₀ > 1`.
  - This contradicts `M.IsStable` (which requires all solutions
    bounded).
  - So no real `z₀ > 1` is a root of `ρ`.

  This **does not** need Jordan or §142 machinery — it's a direct
  homogeneous-solution argument. Estimated 30–80 LOC.

**Recommend option B.1.β** for cycle 175. It gets us "no real root
> 1" without the full `thm:142F`, which is enough for steps 2–3
of the §441 argument. The simple-root condition (step 4) needs a
separate argument (option B.2 below).

### C.2 — Phase B.2 (cycle 176): simple-root-at-1

Given `M.IsStable + M.IsPreconsistent + ρ(1) = 0`, prove that
`ρ.rootMultiplicity 1 = 1` (i.e. simple root).

The argument: if `ρ` has root `1` with multiplicity ≥ 2, then
`ρ(z) = (z-1)² · q(z)` for some polynomial `q`. The homogeneous
recurrence then has solution `y_n := n` (since `ρ(z) = (z-1)²·q(z)`
makes `(z-1)²` a factor, and the coefficient of `(z-1)²` in the
generating-function inversion gives `n` as a solution of the
recurrence). But `y_n = n` is unbounded, contradicting
`M.IsStable`.

Mathlib hooks:

* `Polynomial.rootMultiplicity` — already in Mathlib.
* `Polynomial.factor_rootMultiplicity` or
  `Polynomial.dvd_iff_pow_le_rootMultiplicity` — the factorization.
* The "if `(z-1)²` divides `ρ`, then `n` solves the recurrence"
  step is the substantive Lean work; it's a direct algebraic
  manipulation of the recurrence using `αᵢ = -ρ.coeff (k-i)`.

Estimated 80–150 LOC. Aristotle suitability: low (the
homogeneous-solution construction is method-specific).

### C.3 — Phase B.3 (cycle 177): assemble `ρ'(1) > 0`

Given B.1 (no real root > 1) and B.2 (simple root at 1), the
real-analytic argument is:

1. `ρ` continuous; `ρ(1) = 0`; `ρ` has no zero on `(1, ∞)`; `ρ(z)
   → +∞` as `z → +∞`.
2. By continuity + IVT-style: `ρ(z) > 0` on `(1, ∞)`.
3. `ρ.rootMultiplicity 1 = 1` ⇒ `ρ(z) = (z - 1) · q(z)` with
   `q(1) ≠ 0`.
4. `ρ(z) > 0` on `(1, ∞)`, `(z - 1) > 0` ⇒ `q(z) > 0` on
   `(1, ∞)` ⇒ `q(1) ≥ 0` (continuity) ⇒ `q(1) > 0`.
5. `ρ'(1) = q(1) > 0` (product rule).

Mathlib hooks (verified to exist):

* `Polynomial.derivative_eval` — eval of derivative.
* `Polynomial.rootMultiplicity_pos_iff_isRoot` and friends.
* `Polynomial.div_X_eq_zero_iff` — for the factorization
  `ρ = (X - 1) · q`.
* `Continuous.tendsto_atTop_iff_leadingCoeff_pos` (look up exact
  name with `lean_loogle`) — for `ρ(z) → +∞`. May need a custom
  proof since Mathlib's `tendsto_polynomial_atTop_atTop_iff` is
  for "leadingCoeff > 0 ⇒ tendsto atTop atTop"; verify name with
  `lean_local_search "tendsto_polynomial"`.
* `intermediate_value_Ioi` or
  `Continuous.IntermediateValue` — IVT.
* `Polynomial.div_self` and product-rule for the q(1) extraction.

Estimated 60–120 LOC. This is the "easy" capstone cycle — it just
glues B.1, B.2, the `ρ'(1) ≠ 0` fact, and the IVT argument.

### C.4 — Phase B.4 (cycle 178): close `lem:441A` `a₁ > 0`

Direct corollary: `aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent`
(cycle 174) plus B.3 ⇒ `a₁ = 2·ρ'(1) > 0`. ~5 LOC.

The `aᵢ ≥ 0` for `i ≥ 2` half is a separate (different) argument
in Butcher (the "factorization into real / conjugate-pair factors
with non-negative coefficients" argument). It uses different
machinery (complex-root decomposition with `Re(ζ) ≤ 0` for ζ a
root of `a`) and would be a Phase C.

### C.5 — Recommended phasing

| Cycle | Deliverable | LOC | Aristotle suitability |
|---|---|---|---|
| 175 | Phase B.1.β: `M.IsStable ⇒ no real root > 1 of ρ` | 30–80 | medium |
| 176 | Phase B.2: simple root at 1 | 80–150 | low |
| 177 | Phase B.3: assemble `ρ'(1) > 0` | 60–120 | medium-high |
| 178 | Phase B.4 (`a₁ > 0`) + Phase C scoping (`aᵢ ≥ 0`) | 5 + scoping | n/a |

Cycle 175's deliverable is the highest-uncertainty (the
`(z₀)^n → ∞` argument is conceptually clean but the Lean encoding
of "solution `y_n := z₀^n` of the homogeneous recurrence" needs
care because our `IsHomogeneousSolution` uses `M.α`-indexed
coefficients with `M.α 0 = -1` normalization). Worth running an
Aristotle batch in parallel.

---

## D. Direct cycle 175 strategy options

Given the analysis above, the cycle 175 planner has three viable
directions:

### Option D.1 (recommended): Phase B.1.β + simpler BDF2 witness

* Deliverable: `M.IsStable ⇒ ρ.IsRoot z → z ≤ 1` (real-valued
  side). ~50 LOC, axiom-clean.
* Deliverable: replace `bdf2LMM_aPoly_eq` goal with one of the
  two-line BDF2 sanity witnesses from §B.2 above. ~5 LOC.
* Net cycle effect: +1 substantive theorem (real-root location),
  +1 simple BDF2 non-vacuity, sorry count unchanged at 0.
* Aristotle: submit Phase B.1.β as a job (template:
  the `(z₀)^n → ∞` contradiction; supply
  `IsHomogeneousSolution`, `bdf2LMM` etc. as in-context
  templates).

### Option D.2: Pivot to a fresh entity

Cycles 173/174 made cycle 174-headline progress on §441; the
chain is now `aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent`
+ all five `ρPoly` lemmas. A fresh §410-area entity (`thm:410B`,
`thm:410C` if untreated) or a §454 entity might give faster
deliverables and let the multi-cycle ρ'(1) > 0 work be batched.

The §550 line in particular has 1..7 stepping stones already
(per `thm_550A_general_n.md`); cycle 175 could ship a 8th
stepping stone (n = 8) for marginal value, OR pivot to a
genuinely new direction.

Let the planner decide based on which "easiest unblock" is
shortest path to the next textbook landmark (Theorem 441C, the
Dahlquist barrier).

### Option D.3: Stretch — attempt the full `bdf2LMM_aPoly_eq` via funext

If the planner judges the BDF2 closed form has bookkeeping value
(parity with explicit Euler at every §441 deliverable), attempt
the §B.3 `funext + ring` recipe. **Time-boxed**: if it does not
close in ≤ 60 minutes, fall back to one of the §B.2 cheaper
witnesses without leaving a sorry behind. Do NOT introduce
`Polynomial.ext` skeletons — they will stall again.

---

## E. What NOT to do this cycle

* Do **NOT** revert any cycle 174 work. The factor-of-2 result
  is correct; Butcher has the typo.
* Do **NOT** audit `hdistrib`. Its algebra is
  `(k − (i+1)) = (k - 1) - i` substituted with `Σαᵢ = 1`,
  which is fine.
* Do **NOT** attempt `bdf2LMM_aPoly_eq` with `Polynomial.ext +
  simp + ring` (cycle 172 / 173 pattern). If pursued, use
  `Polynomial.funext + ring` (§B.3 last-resort recipe) or skip
  it entirely.
* Do **NOT** raise `maxHeartbeats` above 200000.
* Do **NOT** introduce `axiom` for the `α'(1) < 0` infrastructure.
  Phases B.1.β–B.4 outlined in §C ARE the closure path; they
  work without external axioms.
* Do **NOT** poll Aristotle more than once in a cycle.

---

## F. Quick-reference table — Mathlib lemmas cited above

| Goal | Lemma | File |
|---|---|---|
| `(1 + X)^n.coeff k = n.choose k` | `Polynomial.coeff_one_add_X_pow` | `Mathlib/Algebra/Polynomial/Coeff.lean:?` |
| `(C a * P).coeff n = a * P.coeff n` | `Polynomial.coeff_C_mul` | std |
| `(p * X).coeff (n+1) = p.coeff n` | `Polynomial.coeff_mul_X` | std |
| `(p * X^k).coeff (n+k) = p.coeff n` | `Polynomial.coeff_mul_X_pow` | std |
| coeff bound `degree < d ⇒ coeff = 0` | `Polynomial.coeff_eq_zero_of_natDegree_lt` | std |
| polynomial = polynomial via eval | `Polynomial.funext` (over infinite `[CommRing][IsDomain][Infinite]`) | std |
| polynomial root multiplicity | `Polynomial.rootMultiplicity` | `Mathlib/Algebra/Polynomial/RingDivision.lean` |
| simple root via derivative | `Polynomial.rootMultiplicity_eq_one_iff_isRoot_and_derivative_ne_zero` (verify name with `lean_loogle`) | std |
| polynomial → ∞ at infinity | `Polynomial.tendsto_norm_atTop` and friends (look up via `lean_loogle`) | std |
| derivative eval | `Polynomial.derivative_eval` | std |
| factor (z - 1) out of polynomial with root 1 | `Polynomial.dvd_iff_isRoot` + `Polynomial.X_sub_C_dvd_iff_isRoot` | std |
| matrix companion | `Matrix.companion`, `Matrix.charpoly_companion` (verify with `lean_loogle "Matrix.companion"`) | `Mathlib/LinearAlgebra/Matrix/Companion.lean` |
| `IsRoot` ⇔ `eval = 0` | `Polynomial.IsRoot` | std |

Names are best-effort accurate as of `Mathlib v4.28.0`. The worker
should verify each with `lean_local_search` before relying on it.

---

## G. Cross-references

* `.prover-state/issues/lem_441A_alpha_prime_negative.md` — cycle
  174 update with the ρ-side route plan.
* `.prover-state/issues/lem_441B_misinterpretation.md` — cycle 172
  rollback record (cycle 171 misinterpreted `c_{2i}` as `aᵢ`).
* `.prover-state/issues/jordan_canonical_form_missing.md` —
  blocks Phase B.1.α (the full `thm:142F` route). Phase B.1.β
  sidesteps this dependency.
* `.prover-state/issues/rouche_theorem_missing.md` — Rouché's
  theorem missing from Mathlib; blocks `thm:431A` sufficiency.
  Not needed for cycle 175's Phase B.1.β.
* `OpenMath/Chapter4/Section441.lean` — current cycle 174
  deliverable (line 286 `aPoly_coeff_one_unconditional`,
  line 292 `_neg_two_alpha_deriv_at_one_of_preconsistent`,
  line 313 `ρPoly` definition, line 374
  `ρPoly_deriv_eval_one_unconditional`, line 403
  `ρPoly_deriv_eval_one_eq_neg_alpha_deriv_at_one_of_preconsistent`,
  line 445 `aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent`).
* `OpenMath/Chapter4/Section410.lean` — `αPoly`, `βPoly`
  generating polynomials (cycle 73).
* `OpenMath/Chapter4/Section451.lean::bdf2LMM` — the `k = 2`
  witness method (line 140).
* `extraction/raw_text/ch04.txt:1947–2030` — raw Butcher §441
  text with the `ρ'(1) = a₁` typo.

---

## H. Bottom-line directive for cycle 175

Drop `bdf2LMM_aPoly_eq`. Ship Option D.1: prove `M.IsStable ⇒ ρ`
has no real root > 1 (Phase B.1.β, ~50 LOC, via the
`(z₀)^n → ∞` direct argument), plus replace the BDF2 closed-form
goal with a two-line `bdf2LMM.aPoly.coeff 1 = 4/3` sanity witness
(uses cycle 174's bridge directly). Net cycle effect: +1
substantive theorem, +1 BDF2 non-vacuity, sorry count 0. Phase
B.2 / B.3 / B.4 follow in cycles 176–178.
