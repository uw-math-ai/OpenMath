# Cycle 076 strategy

## Status snapshot

* Cycle 075 closed `thm:410B` (`Section410.lean:430`) and landed
  the §410B order-condition cluster. Section410.lean has 0 sorries.
* Progress: 45/175. The §410 cluster has 2 of 4 entities done
  (`thm:410A`, `thm:410B`); `thm:410C` and `thm:410D` are open.
* No pending Aristotle results.
* No sorry's anywhere in `OpenMath/`.
* No Aristotle results to incorporate.

## Priority 0 — Target: `thm:410C` (Order condition via generating functions, (ρ, σ) form)

**Why this and not `thm:410D`?** Cycle 075's worker recommended
`thm:410D` next, framing it as ~1 packaging cycle. On inspection
that's too optimistic: `thm:410D` requires PowerSeries composition
with `log(1+z)` (substitute `z ↦ -log(1+z)` into our `genFn`), and
Mathlib's `PowerSeries.subst` is non-trivial to use even when it
applies. `thm:410C` is the *true* packaging cycle: it's the
forward-sign (ρ, σ) restatement of `thm:410B`, achievable by
multiplying our existing `genFn M` by the unit power series
`exp(kz)`. Single cycle. Closes another §410 entity.

`thm:410D` then becomes natural for cycle 077, after the §410
infrastructure is fully bidirectional.

### Textbook statement (`entities/thm_410C.json`)

> A linear multistep method (ρ, σ) has order p if and only if
> `ρ(exp(z)) − z σ(exp(z)) = O(z^{p+1})`.

where ρ(z), σ(z) are the (ρ, σ)-form generating polynomials —
i.e. the reverse-degree-`k` polynomials of α(z), β(z):

```
ρ(z) = z^k - α_1 z^{k-1} - ⋯ - α_k = z^k · α(1/z)    [Butcher's α with α_0 = 1]
σ(z) = β_0 z^k + β_1 z^{k-1} + ⋯ + β_k = z^k · β(1/z)
```

(Butcher's α_0 = 1 corresponds to `M.α 0 = -1` after the sign flip
in the §404 normalisation; under our normalisation, the αPoly we
defined in cycle 074 already IS Butcher's α(z), see Section410.lean
header.)

### The load-bearing identity

```
ρ(exp(z)) - z σ(exp(z)) = exp(kz) · genFn M
                        = exp(kz) · (αPoly M (exp(-z)) - z βPoly M (exp(-z)))
```

**Verification on explicit Euler (k=1, so exp(kz) = exp(z)):**

* `ρ(z) = z - 1`, `σ(z) = 1` (standard for explicit Euler).
* `ρ(exp(z)) - z σ(exp(z)) = exp(z) - 1 - z = z²/2 + z³/6 + ⋯`.
* `genFn = (1 - exp(-z)) - z exp(-z) = z - z²/2 + z³/6 - ⋯ - z + z² - z³/2 + ⋯
         = z²/2 - z³/3 + ⋯`.
* `exp(z) · genFn = (1 + z + z²/2 + ⋯)(z²/2 - z³/3 + ⋯)
                  = z²/2 + z³(1/2 - 1/3) + ⋯ = z²/2 + z³/6 + ⋯`. ✓

So the identity holds, and `exp(kz)` is a unit (constant term 1)
in `PowerSeries ℝ`, so multiplying by it preserves "vanishes for all
`j ≤ p`". This reduces `thm:410C` to `thm:410B` plus the algebra.

## Approach (concrete plan)

Edit only `OpenMath/Chapter4/Section410.lean`. Do NOT touch
`Section404.lean` (the cycle 075 cross-namespace pattern stays
in place — see lines 388–414 of Section410.lean).

### D1: define `expPS` (forward exponential power series)

```lean
/-- The formal power series `exp(z) = Σ_n z^n / n!`. Defined
directly via `PowerSeries.mk` to avoid `Algebra ℚ ℝ` requirements
of `PowerSeries.exp`. -/
noncomputable def expPS : PowerSeries ℝ :=
  PowerSeries.mk fun n => 1 / (Nat.factorial n : ℝ)
```

### D2: define `expKzPS` (the unit `exp(kz)`)

```lean
/-- The formal power series `exp(k z) = Σ_n k^n z^n / n!`. -/
noncomputable def expKzPS (k : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk fun n => (k : ℝ) ^ n / (Nat.factorial n : ℝ)
```

Sanity helper: `expKzPS 0 = 1` (one-line `simp` proof) — useful for
edge cases in the unit lemma.

### D3: define `ρPoly`, `σPoly`

```lean
/-- **Butcher §410 ρ-polynomial.** `ρ(z) = z^k · α(1/z)` is the
reverse polynomial of α. With our `α(z) = 1 - Σ_{i=1}^k α_i z^i`,
this gives `ρ(z) = z^k - Σ_{i=1}^k α_i z^{k-i}`. -/
noncomputable def ρPoly {k : ℕ} (M : LinearMultistepMethod k) :
    Polynomial ℝ :=
  Polynomial.X ^ k -
    ∑ i : Fin k,
      Polynomial.C (M.α i.succ) * Polynomial.X ^ (k - (i.val + 1))

/-- **Butcher §410 σ-polynomial.** `σ(z) = z^k · β(1/z) = Σ_{i=0}^k β_i z^{k-i}`. -/
noncomputable def σPoly {k : ℕ} (M : LinearMultistepMethod k) :
    Polynomial ℝ :=
  ∑ i : Fin (k + 1), Polynomial.C (M.β i) * Polynomial.X ^ (k - i.val)
```

Witness lemmas (mirror cycle 074's `αPoly_explicitEuler`,
`βPoly_explicitEuler`):

```lean
theorem ρPoly_explicitEuler : ρPoly explicitEulerLMM = X - 1 := by
  unfold ρPoly; simp [explicitEulerLMM]
theorem σPoly_explicitEuler : σPoly explicitEulerLMM = 1 := by
  unfold σPoly; simp [explicitEulerLMM, Fin.sum_univ_succ]
```

### D4: define `genFnForward`

```lean
/-- **(ρ, σ)-form generating function (forward sign).**
`genFnForward M = ρ(exp(z)) - z σ(exp(z))`. -/
noncomputable def genFnForward {k : ℕ} (M : LinearMultistepMethod k) :
    PowerSeries ℝ :=
  (Polynomial.aeval expPS) (ρPoly M)
    - PowerSeries.X * (Polynomial.aeval expPS) (σPoly M)
```

### D5: prove the unit-equivalence (`genFnForward_eq_expKzPS_mul_genFn`)

This is the load-bearing lemma. The two natural routes:

* **Route A (preferred — match cycle 075's `thm_410A` style)**: prove
  the coefficient identity `coeff j (genFnForward M) = (k^? · ⋯)` by
  unfolding `ρPoly`, `σPoly`, applying `map_sub`/`map_sum`, and using
  the cycle 074 `coeff_aeval_C_X_pow` lemma per monomial. Then show
  `coeff j (expKzPS k · genFn M)` equals the same thing via
  `PowerSeries.coeff_mul` and the closed-form `coeff j (expKzPS k)
  = k^j / j!`.
* **Route B**: prove the polynomial reverse identity
  `ρPoly M = X^k * (αPoly M).reflect k` (or similar), then show
  `aeval expPS (P.reflect k) = expKzPS k * aeval expNegPS P` for
  any P with degree ≤ k. This is cleaner conceptually but the Mathlib
  lemma `Polynomial.aeval_reflect` may not exist as stated — would
  need to derive it.

**Recommend Route A.** Direct coefficient unfolding worked for
`thm_410A` in cycle 074 and is the well-trodden path. Aristotle is
likely to handle the algebraic-equality core if we batch it right.

State the identity in a way that lets the proof be modular:

```lean
/-- **§410C unit equivalence.** `ρ(exp(z)) - z σ(exp(z)) = exp(kz) · genFn M`. -/
theorem genFnForward_eq_expKzPS_mul_genFn {k : ℕ}
    (M : LinearMultistepMethod k) :
    genFnForward M = expKzPS k * genFn M := by
  ext j
  -- LHS = coeff j (αPoly M(expPS) - X · βPoly_reverse(expPS))
  -- RHS = Σ_{i+l=j} k^i/i! · (genFn M).coeff l
  -- Reduce both to the same closed-form polynomial in k, j.
  sorry
```

If Route A's `ext j` proof is heavy, decompose into:
* `coeff_genFnForward` — closed form for `coeff j (genFnForward M)`,
  analogous to `thm_410A`.
* `coeff_expKzPS_mul_genFn` — closed form for the RHS via Cauchy
  product.
* The main lemma equates them.

### D6: the bridge to `HasOrderAtLeast`

```lean
/-- **Multiplication by `expKzPS k` preserves vanishing of low coefficients.**
Since `expKzPS k` has constant term 1 (a unit), `coeff j (expKzPS k · g) = 0
for all j ≤ p` iff `coeff j g = 0 for all j ≤ p`. -/
theorem coeff_expKzPS_mul_eq_zero_iff {k : ℕ} (g : PowerSeries ℝ) (p : ℕ) :
    (∀ j ≤ p, (PowerSeries.coeff (R := ℝ) j) (expKzPS k * g) = 0)
      ↔ (∀ j ≤ p, (PowerSeries.coeff (R := ℝ) j) g = 0) := by
  -- Forward: induct on j ≤ p. coeff 0 (expKzPS k · g) = 1 · g.coeff 0,
  -- coeff (j+1) is g.coeff (j+1) + sum of terms involving smaller g.coeff's,
  -- which all vanish by IH.
  -- Reverse: if all g coeffs ≤ p vanish, the Cauchy product sum is 0.
  sorry
```

Then the main theorem:

```lean
/-- **Butcher §410 Theorem 410C ((ρ, σ)-form order condition).** -/
theorem thm_410C {k : ℕ} (M : LinearMultistepMethod k) (p : ℕ) :
    M.HasOrderAtLeast p
      ↔ ∀ j ≤ p, (PowerSeries.coeff (R := ℝ) j) (genFnForward M) = 0 := by
  rw [thm_410B]
  rw [genFnForward_eq_expKzPS_mul_genFn]
  exact (coeff_expKzPS_mul_eq_zero_iff (genFn M) p).symm
```

(The `rw` plumbing may want a small reshuffle; the conceptual core is
`thm:410B` + unit equivalence + unit preservation.)

### D7: witnesses

* `explicitEulerLMM_genFnForward_O_z2` — at `j = 0, 1`, the forward
  generating function vanishes (consistency restated forward).
* `explicitEulerLMM_hasOrderAtLeast_one_via_410C` — repackage cycle 075's
  `explicitEulerLMM_hasOrderAtLeast_one` through `thm_410C`. (1-line
  via `(thm_410C _ _).mpr`.)

## Aristotle batch (submit at start of cycle, ~30 min sleep)

Submit a self-contained `cycle_076_410C.lean` to Aristotle covering:

1. `expPS_coeff` — `(PowerSeries.coeff j) expPS = 1 / j!` (1-liner;
   parallel to `expNegPS_coeff` in cycle 073).
2. `expKzPS_coeff` — `(PowerSeries.coeff j) (expKzPS k) = k^j / j!`.
3. `coeff_aeval_C_X_pow_expPS` — analog of cycle 074's
   `coeff_aeval_C_X_pow` but at `expPS` instead of `expNegPS`:
   `coeff j (aeval expPS (C c · X^m)) = c · m^j / j!`.
4. `expPS_pow` — closed form `expPS^m = PowerSeries.mk fun n => m^n / n!`
   (induction on m; mirror of cycle 074's `expNegPS^m` proof).
5. `coeff_expKzPS_mul_eq_zero_iff` (D6 bridge).

Routes 1–4 are almost mechanical re-derivations of cycle 073/074 results
with sign change `(-1)^? → 1`. Route 5 is the bridge lemma; if Aristotle
struggles, fall back to manual proof via induction on `j ≤ p`.

The substantive identity `genFnForward_eq_expKzPS_mul_genFn` (D5) is
NOT a great Aristotle target because it's a structural/inductive proof
across the polynomial sums, not a pure premise-selection win. Prove it
manually using cycle 075's `thm_410A` pattern (case j = 0; case j = j' + 1
with `map_sub`/`map_sum` push-throughs).

## What NOT to try

* **Don't** tackle `thm:410D` this cycle. It needs PowerSeries composition
  (substitute `log(1+z)`) plus invertibility of substitution; Mathlib's
  `PowerSeries.subst` works but is heavy. After thm:410C lands, cycle 077
  can take it on with the full §410 forward/backward equivalence in hand.
* **Don't** use `Mathlib.PowerSeries.exp` — it requires `Algebra ℚ R`
  which complicates the substitution lemmas. Reuse cycle 073's pattern of
  defining `expPS`/`expKzPS` directly via `PowerSeries.mk`. (Cycle 074's
  `expNegPS` is right there at `Section410.lean:139`.)
* **Don't** use `Polynomial.reverse` — for our αPoly, `natDegree` may
  be < k if `M.α k = 0`, which makes `reverse` inconsistent. Define
  `ρPoly`, `σPoly` explicitly via summation as in D3 above.
  (`Polynomial.reflect` is the degree-aware version, but a direct
  definition is clearer for this size.)
* **Don't** try to refactor `genFn` to use the forward sign. Cycle 074
  and 075 are committed to the backward-sign convention; changing it
  would break `thm:410A`/`thm:410B`/the bridge lemmas. Define
  `genFnForward` as a separate object and derive its relationship to
  `genFn`.
* **Don't** put `genFnForward` or `ρPoly`/`σPoly` under `Section404`'s
  namespace. Keep them in §410 (the type `LinearMultistepMethod` lives
  in §404 but our generating-function objects are §410-specific).
  `M.HasOrderAtLeast` lives in §404 (cycle 075's design); follow that
  pattern (already done — don't break it).
* **Don't** raise `maxHeartbeats`. If `genFnForward_eq_expKzPS_mul_genFn`
  is heavy, decompose into per-coefficient closed forms (analog of
  `thm_410A` + a Cauchy-product sum lemma) instead of one big `ext j; simp`.
* **Don't** introduce `axiom`/`constant`. If `coeff_expKzPS_mul_eq_zero_iff`
  resists, fall back to a strong-induction proof on `j ≤ p`; the unit
  property of `expKzPS k` (constant term 1, hence multiplicatively
  invertible in `PowerSeries`) is the essential fact.

## Faithfulness check (worker MUST run before commit)

For `genFnForward`:
* Textbook statement: `ρ(exp(z)) − z σ(exp(z))` (statement_text of
  `thm:410C`).
* Lean statement: `aeval expPS (ρPoly M) - X · aeval expPS (σPoly M)`.
* Captures: same content (substitution at `expPS` is the formal
  power-series version of `_(exp(z))`).

For `ρPoly`, `σPoly`:
* Textbook: ρ(z) = z^k - α_1 z^{k-1} - ⋯ - α_k, σ(z) = β_0 z^k + ⋯ + β_k
  (Butcher §410, p. 351, in (ρ, σ) notation, with Butcher's α_0 = 1).
* Lean: matches D3 above.
* Note: Butcher's α_0 = 1 corresponds to our `M.α 0 = -1`; the sign
  is absorbed in the `αPoly = 1 - Σ ...` definition (cycle 074
  Section410 header). Our `αPoly` IS Butcher's α(z), so our `ρPoly`
  IS Butcher's ρ(z) = z^k · α(1/z).

For `thm_410C`:
* Textbook: "[α, β] LMM has order p iff ρ(exp(z)) - z σ(exp(z)) = O(z^{p+1})".
* Lean: `M.HasOrderAtLeast p ↔ ∀ j ≤ p, coeff j (genFnForward M) = 0`.
* Captures: same content. The `O(z^{p+1})` is the standard formal
  power-series ⇔ "first p+1 coefficients vanish" (same encoding choice
  as `thm_410B`).

For `genFnForward_eq_expKzPS_mul_genFn`:
* This is a derived algebraic identity, not a textbook entity. Tautology
  check: PASS — neither side syntactically equals a hypothesis.
* Identity check: the proof unfolds both sides and identifies them
  via Cauchy product algebra. Substantive.

## Pre-commit final checks

* `lake env lean OpenMath/Chapter4/Section410.lean` — clean compile.
* `#print axioms thm_410C` — must be `[propext, Classical.choice, Quot.sound]`.
  If `sorryAx` shows up, run `lake build OpenMath.Chapter4.Section410`
  to refresh `.olean` (per cycle 072 lesson).
* `lean_status.json::thm:410C` → `formalized`, with `lean_file` and
  `lean_symbol` fields populated.
* `plan.md::thm:410C` from `[ ]` to `[x]`. Bump progress 45 → 46.

## Suggested follow-on for cycle 077

`thm:410D` — log-form `α((1+z)⁻¹) − log(1+z)·β((1+z)⁻¹) = O(z^{p+1})`.
With cycle 076's `expPS`/`expKzPS` infrastructure landing, the natural
approach is to define:

* `logOnePlusPS` — `Σ_{n≥1} (-1)^{n-1} z^n / n`.
* `oneOverOnePlusPS` — `Σ_n (-1)^n z^n` (geometric).

and prove the substitution identity that under the formal identity
`exp(-log(1+z)) = (1+z)^{-1}`, the cycle 075/076 results transfer.

This is a 1–2 cycle deliverable and closes the §410 cluster.

## Cycle deliverable bar

Minimum acceptable: D1–D4 land (definitions + witnesses) and the
unit-equivalence sub-lemma `genFnForward_eq_expKzPS_mul_genFn` is
stated as `sorry`-first, with at least 2 of the Aristotle-batched
sub-lemmas (D6 bridge, expPS coefficient lemma) closed. Issue file
documents what blocks the main `thm_410C`.

Target: full closure of `thm:410C` with 0 sorries and standard axioms.

If the unit-equivalence proof balloons (>200 lines or `maxHeartbeats`
trouble), decompose along the cycle 074 `thm_410A` pattern: per-coeff
closed form + α-side identity + β-side identity + ring/algebra
finisher.
