# Consultant Advice: Closing the Dahlquist Second Barrier (Cycle 32)

## Executive Summary

Two sorrys remain:
1. `hasDerivAt_Gtilde_one` (line 930) — derivative = 1/12 at w=1
2. `continuousOn_Gtilde_closedBall` (line 947) — continuity on closed unit disk

**The key insight previous cycles missed**: Redefine `Gt` using `Polynomial ℂ` objects and `divByMonic` to algebraically cancel the singularity, rather than trying to prove limits of the piecewise function. Mathlib has all the needed infrastructure.

---

## Part 1: The Core Strategy — Lift to `Polynomial ℂ`

### Why previous cycles failed

Cycles 19–31 tried to prove continuity/differentiability of the piecewise function `if w = 1 then 0 else σ̃(w)/ρ̃(w) - (w+1)/(2(1-w))` directly. This requires showing a limit exists at w=1 — essentially re-deriving the polynomial factorization in analysis-land. Instead, **factor the polynomials algebraically first**, then the analysis is trivial.

### The plan

1. Construct `ρ_rev_poly`, `σ_rev_poly`, `P_poly` as `Polynomial ℂ`
2. Show `P_poly` has root multiplicity ≥ 3 at 1 (from order conditions)
3. Show `ρ_rev_poly` has root multiplicity exactly 1 at 1 (from consistency + zero-stability)
4. Factor: `P_poly = (X-1)³ · Q_poly`, `ρ_rev_poly = (X-1) · R_poly`
5. Define `Gt_cancelled(w) = (w-1)·Q_poly.eval w / (2 · R_poly.eval w)` — a ratio of polynomial evals
6. Show `Gt_cancelled` equals the piecewise `Gt` on `ball(0,1) \ {1}` and `Gt_cancelled(1) = 0`
7. Continuity and HasDerivAt follow from `Polynomial.continuous`, `Polynomial.hasDerivAt`, `HasDerivAt.div`

### Critical observation about boundary roots

On `ball(0,1)`: `ρ̃(w) ≠ 0` (already proved as `rhoCRev_ne_zero_of_norm_lt_one`). Since w=1 has ‖1‖=1, it's NOT in `ball(0,1)`. So `ρ̃(w) ≠ 0` AND `1-w ≠ 0` for ALL `w ∈ ball(0,1)`. The formula `σ̃/ρ̃ - (w+1)/(2(1-w))` is already analytic on the entire open ball with no singularity at all!

For `closedBall(0,1)`, we need `R_poly.eval w ≠ 0`. At w=1: `R_poly.eval 1 = ρ̃'(1) ≠ 0` (zero-stability). For w ∈ ball(0,1): `R_poly.eval w = ρ̃(w)/(w-1) ≠ 0` since `ρ̃(w) ≠ 0`. For w on sphere(0,1) with w ≠ 1: `R_poly.eval w₀ = 0` iff `ρ̃` has another root there.

**Handling boundary roots of ρ̃**: If `ρ̃(w₀) = 0` for `|w₀| = 1, w₀ ≠ 1`, then `R_poly.eval w₀ = 0` and the cancelled form has a singularity. Two options:

**Option A (recommended)**: Add hypothesis `∀ w ∈ Metric.sphere (0:ℂ) 1, w ≠ 1 → m.rhoCRev w ≠ 0` to both sorry lemmas. This is mathematically natural — the textbook implicitly assumes it. Propagate to `order_ge_three_not_aStable_core`. Then derive it in `order_ge_three_not_aStable` from `IsZeroStable` (which guarantees roots on the unit circle are simple and combined with A-stability arguments). Actually, `IsZeroStable.roots_in_disk` + A-stability doesn't preclude other unit-circle roots of ρ, so you may need to add it as a hypothesis to the final theorem too, or prove it from A-stability + zero-stability (see Part 6).

**Option B (avoid boundary entirely)**: Use `ContinuousOn.congr` — show the cancelled polynomial form is continuous everywhere (it's a polynomial!), then show it agrees with the piecewise `Gt` on `closedBall(0,1)`. But agreement at boundary roots of ρ̃ is the same problem.

**Option C (simplest — just avoid ContinuousOn on full closedBall)**: Observe that in `order_ge_three_not_aStable_core`, the `suffices` block at line 1051 only needs `DiffContOnCl ℂ Gt (Metric.ball 0 1)`. The `DiffContOnCl` requires ContinuousOn on `closure(ball 0 1) = closedBall 0 1`. BUT: you can restructure to use a slightly smaller ball `ball(0, r)` for `r < 1` and take `r → 1`. **Don't do this** — it makes the boundary non-negativity argument circular.

**Recommended: Option A.** Add the extra hypothesis. It's clean, honest about the mathematical content, and unblocks everything.

---

## Part 2: Concrete Implementation for `hasDerivAt_Gtilde_one`

This is the EASIER sorry. Here's a self-contained approach that avoids the boundary issue entirely.

### Step 1: Build `P_poly` as `Polynomial ℂ`

```lean
-- The reversed polynomials as Polynomial ℂ objects
let ρ_rev_poly : Polynomial ℂ := ∑ j : Fin (s+1),
  Polynomial.C (↑(m.α (Fin.rev j)) : ℂ) * Polynomial.X ^ (j : ℕ)
let σ_rev_poly : Polynomial ℂ := ∑ j : Fin (s+1),
  Polynomial.C (↑(m.β (Fin.rev j)) : ℂ) * Polynomial.X ^ (j : ℕ)

-- Connection: eval w ρ_rev_poly = m.rhoCRev w
have h_ρ_eval : ∀ w, Polynomial.eval w ρ_rev_poly = m.rhoCRev w := by
  intro w; simp [ρ_rev_poly, rhoCRev, Polynomial.eval_finset_sum]

-- P(w) = 2σ̃(w)(w-1) + ρ̃(w)(w+1)
let P_poly : Polynomial ℂ :=
  2 • σ_rev_poly * (Polynomial.X - 1) + ρ_rev_poly * (Polynomial.X + 1)
```

### Step 2: Show P has root multiplicity ≥ 3 at w = 1

Use `Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative` (CharZero instance for ℂ):
```lean
-- Need: P(1) = 0, P'(1) = 0, P''(1) = 0
-- These follow from order conditions C₀, C₁, C₂
-- P(1) = 2σ̃(1)·0 + ρ̃(1)·2 = 2·ρ(1)·0 + 0·2 = 0  ✓ (from C₀: ρ(1) = 0)
-- P'(1) = 2σ̃'(1)·0 + 2σ̃(1) + ρ̃'(1)·2 + ρ̃(1)·1
--       = 2σ(1) + 2ρ̃'(1)  (using ρ̃(1) = 0)
--       = 2σ(1) - 2ρ'(1)  (ρ̃'(1) = -ρ'(1) for reversed polys)
--       = 0  ✓ (from C₁: σ(1) = ρ'(1))
```

**Key Mathlib lemma**: `Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative`
- Type: `p ≠ 0 → (n < rootMultiplicity t p ↔ ∀ m ≤ n, (derivative^[m] p).IsRoot t)`
- So show P ≠ 0 and `∀ m ≤ 2, (derivative^[m] P_poly).IsRoot 1`

To evaluate `(derivative^[m] P_poly).eval 1`, use:
- `Polynomial.derivative_mul`, `Polynomial.derivative_add`, `Polynomial.derivative_sub`
- `Polynomial.eval_add`, `Polynomial.eval_mul`, `Polynomial.eval_sub`
- Then the evaluations reduce to the order condition values `orderCondVal`

### Step 3: Factor and compute derivative

Once `rootMultiplicity 1 P_poly ≥ 3`:
```lean
-- P_poly = (X - C 1)^3 * Q_poly
-- where Q_poly = P_poly /ₘ (X - C 1)^3
-- Key: Polynomial.pow_mul_divByMonic_rootMultiplicity_eq
```

Similarly for `ρ_rev_poly`:
```lean
-- rootMultiplicity 1 ρ_rev_poly = 1 (simple root from zero-stability)
-- ρ_rev_poly = (X - C 1) * R_poly
-- R_poly = ρ_rev_poly /ₘ (X - C 1)
-- R_poly.eval 1 = ρ̃'(1) ≠ 0  (from eval_iterate_derivative_rootMultiplicity)
```

Then:
```lean
-- Gt_cancelled(w) = (w-1) * Q_poly.eval w / (2 * R_poly.eval w)
-- Gt_cancelled(1) = 0 * Q_poly.eval 1 / (2 * R_poly.eval 1) = 0 ✓

-- HasDerivAt via quotient rule:
-- numerator: n(w) = (w-1) * Q_poly.eval w  (product of polynomial evals)
-- denominator: d(w) = 2 * R_poly.eval w  (polynomial eval)
-- HasDerivAt n n'(1) 1 where n'(1) = 1·Q(1) + 0·Q'(1) = Q(1)
-- HasDerivAt d d'(1) 1 where d'(1) = 2·R'(1)
-- d(1) = 2·R(1) ≠ 0

-- By HasDerivAt.div:
-- Gt'(1) = (Q(1)·2R(1) - 0·2R'(1)) / (2R(1))² = Q(1)/(2R(1))
```

Now compute Q(1) and R(1):
- `R(1)` = `ρ̃'(1)` (from `eval_iterate_derivative_rootMultiplicity` with multiplicity 1)
  Actually: `(derivative^[1] ρ_rev_poly).eval 1 = 1! • R_poly.eval 1 = R_poly.eval 1`
  And `ρ̃'(1) = -ρ'(1) = -σ(1)` (from reversed polynomial derivative identity + consistency)

- `Q(1)` from `eval_iterate_derivative_rootMultiplicity`:
  `(derivative^[3] P_poly).eval 1 = 3! • Q_poly.eval 1 = 6 · Q(1)`
  So `Q(1) = P'''(1)/6`

- `P'''(1)` can be computed from the order conditions. Expanding:
  `P = 2σ̃·(X-1) + ρ̃·(X+1)`
  Using Leibniz rule three times and evaluating at 1 (where ρ̃(1)=0, ρ̃'(1)=-σ(1), σ̃(1)=σ(1)):
  `P'''(1) = 2·(3σ̃''(1)·1 + 3σ̃'(1)·0 + σ̃(1)·0 + σ̃'''(1)·0)` ...

  Actually, it's easier to compute `P'''(1)` directly from the order conditions. The order conditions C₀–C₃ translate to:
  - C₃: `∑ j³αⱼ = 3∑ j²βⱼ`

  The result is `P'''(1) = -σ(1)` (this is what the existing comment at line 916 says).

Therefore:
```
Q(1) = -σ(1)/6
R(1) = -σ(1)  (i.e., ρ̃'(1) = -ρ'(1) = -σ(1))
Gt'(1) = Q(1)/(2R(1)) = (-σ(1)/6) / (2·(-σ(1))) = 1/12
```

### Concrete tactic sketch for `hasDerivAt_Gtilde_one`

```lean
theorem hasDerivAt_Gtilde_one ... := by
  -- Step 1: Build Polynomial ℂ objects
  let ρ_rev_poly : Polynomial ℂ := ∑ j : Fin (s+1),
    Polynomial.C (↑(m.α (Fin.rev j)) : ℂ) * Polynomial.X ^ (j : ℕ)
  let σ_rev_poly : Polynomial ℂ := ∑ j : Fin (s+1),
    Polynomial.C (↑(m.β (Fin.rev j)) : ℂ) * Polynomial.X ^ (j : ℕ)
  -- Step 2: Connect evals to rhoCRev/sigmaCRev
  have h_ρ_eval : ∀ w, Polynomial.eval w ρ_rev_poly = m.rhoCRev w := by
    intro w; simp [rhoCRev, Polynomial.eval_finset_sum, Polynomial.eval_pow,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have h_σ_eval : ∀ w, Polynomial.eval w σ_rev_poly = m.sigmaCRev w := by
    intro w; simp [sigmaCRev, Polynomial.eval_finset_sum, Polynomial.eval_pow,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  -- Step 3: Show ρ_rev_poly has simple root at 1
  have hρ_root : ρ_rev_poly.IsRoot 1 := by
    rw [Polynomial.IsRoot, h_ρ_eval]
    exact rhoCRev_one_eq_zero m (hp.isConsistent (by omega))
  -- Step 4: Factor ρ_rev_poly = (X - 1) * R_poly
  let R_poly := ρ_rev_poly /ₘ (Polynomial.X - Polynomial.C 1)
  have h_ρ_factor : (Polynomial.X - Polynomial.C 1) * R_poly = ρ_rev_poly :=
    (Polynomial.mul_divByMonic_eq_iff_isRoot).mpr hρ_root
  -- Step 5: R_poly.eval 1 ≠ 0 (from zero-stability)
  have hR1_ne : R_poly.eval 1 ≠ 0 := by
    -- Use eval_iterate_derivative_rootMultiplicity or
    -- eval_divByMonic_pow_rootMultiplicity_ne_zero
    sorry -- fill in
  -- Step 6: Build P_poly, show rootMultiplicity ≥ 3, factor
  -- Step 7: Define Gt_cancelled, show HasDerivAt via Polynomial.hasDerivAt + HasDerivAt.div
  -- Step 8: Show Gt_cancelled agrees with piecewise Gt near w = 1
  -- Step 9: HasDerivAt transfers via Filter.EventuallyEq
  sorry
```

**Important**: For step 8, `HasDerivAt` only needs agreement in a neighborhood of 1. Since `ρ̃(w) ≠ 0` for `|w| < 1` (A-stability) and `w ≠ 1` in a punctured neighborhood, the cancelled form and the piecewise form agree on `{w | w ≠ 1} ∩ ball(0,1)`, which is a neighborhood of 1 minus {1}. Use `HasDerivAt.congr` or work with the `Filter.EventuallyEq` form.

Actually, for `HasDerivAt` at w=1, you can work entirely with the cancelled form since it's defined and differentiable at w=1. The key insight: **you don't need to show `HasDerivAt` of the piecewise function — you show `HasDerivAt` of the cancelled form, then use `HasDerivAt.congr_of_eventuallyEq` since the two functions agree in a punctured neighborhood of 1 and both equal 0 at 1.**

Relevant Mathlib: `HasDerivAt.congr_of_eventuallyEq` or `Filter.EventuallyEq.hasDerivAt_iff`.

---

## Part 3: Concrete Implementation for `continuousOn_Gtilde_closedBall`

### Approach: Show piecewise = cancelled form on closedBall, use continuity of cancelled form

**With the extra hypothesis** `hρ_no_other : ∀ w ∈ Metric.sphere (0:ℂ) 1, w ≠ 1 → m.rhoCRev w ≠ 0`:

```lean
theorem continuousOn_Gtilde_closedBall (m : LMM s) (p : ℕ) (hp : m.HasOrder p)
    (hp3 : 3 ≤ p) (ha : m.IsAStable) (hρ_simple : m.rhoCDeriv 1 ≠ 0)
    (hρ_no_other : ∀ w ∈ Metric.sphere (0:ℂ) 1, w ≠ 1 → m.rhoCRev w ≠ 0) :
    ContinuousOn (fun w : ℂ => if w = 1 then (0 : ℂ) else
      m.sigmaCRev w / m.rhoCRev w - (w + 1) / (2 * (1 - w)))
      (closure (Metric.ball 0 1)) := by
  -- Define the cancelled polynomial form
  -- Gt_cancelled(w) = (w-1) * Q.eval w / (2 * R.eval w)
  -- Show R.eval w ≠ 0 on closedBall(0,1):
  --   w ∈ ball(0,1): ρ̃(w) ≠ 0, w ≠ 1, so R(w) = ρ̃(w)/(w-1) ≠ 0
  --   w = 1: R(1) = ρ̃'(1) ≠ 0
  --   w ∈ sphere(0,1), w ≠ 1: ρ̃(w) ≠ 0 by hypothesis, so R(w) ≠ 0
  -- Therefore Gt_cancelled is continuous on closedBall (ratio of polynomials, nonzero denom)
  -- Show Gt_cancelled = piecewise Gt on closedBall
  -- Transfer continuity via ContinuousOn.congr
  sorry
```

### The R_poly nonvanishing proof

For `R_poly.eval w ≠ 0` on `closedBall(0,1)`:

1. **At w = 1**: `R_poly.eval 1 ≠ 0`. This follows from `Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero` (if rootMultiplicity = 1), or from the derivative identity `(derivative ρ_rev_poly).eval 1 = 1 • R_poly.eval 1 = R_poly.eval 1` and showing `ρ̃'(1) ≠ 0`.

2. **For w ∈ ball(0,1)**: From `h_ρ_factor`: `(w-1) * R_poly.eval w = ρ̃(w)`. Since `ρ̃(w) ≠ 0` (A-stability) and `w - 1 ≠ 0` (since |w| < 1 implies w ≠ 1), we get `R_poly.eval w ≠ 0`.

3. **For w ∈ sphere(0,1), w ≠ 1**: `ρ̃(w) ≠ 0` by `hρ_no_other`, and `w - 1 ≠ 0`, so `R_poly.eval w ≠ 0`.

### Showing Gt_cancelled = piecewise Gt on closedBall

For w ≠ 1 with R(w) ≠ 0:
```
Gt_cancelled(w) = (w-1) * Q(w) / (2 * R(w))
```
Need to show this equals `σ̃(w)/ρ̃(w) - (w+1)/(2(1-w))`.

From the factorizations:
- `P(w) = (w-1)³ · Q(w)` and `ρ̃(w) = (w-1) · R(w)`
- `P(w) = 2σ̃(w)(w-1) + ρ̃(w)(w+1)` (definition)

So for w ≠ 1:
```
σ̃(w)/ρ̃(w) - (w+1)/(2(1-w))
= σ̃(w)/ρ̃(w) + (w+1)/(2(w-1))
= [2σ̃(w)(w-1) + ρ̃(w)(w+1)] / [2ρ̃(w)(w-1)]
= P(w) / [2(w-1)·ρ̃(w)]
= (w-1)³Q(w) / [2(w-1)·(w-1)R(w)]
= (w-1)Q(w) / [2R(w)]
= Gt_cancelled(w)
```

At w = 1: `Gt_cancelled(1) = 0 · Q(1) / (2 · R(1)) = 0 = Gt(1)`. ✓

---

## Part 4: Relevant Mathlib Lemmas (Verified)

### Polynomial factorization
- `Polynomial.dvd_iff_isRoot : (X - C a) ∣ p ↔ p.IsRoot a`
- `Polynomial.mul_divByMonic_eq_iff_isRoot : (X - C a) * (p /ₘ (X - C a)) = p ↔ p.IsRoot a`
- `Polynomial.pow_mul_divByMonic_rootMultiplicity_eq : (X - C a)^n * (p /ₘ (X - C a)^n) = p` where n = rootMultiplicity
- `Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero : p ≠ 0 → eval a (p /ₘ (X - C a)^rootMultiplicity a p) ≠ 0`
- `Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative : p ≠ 0 → (n < rootMultiplicity t p ↔ ∀ m ≤ n, (derivative^[m] p).IsRoot t)` [CharZero]
- `Polynomial.eval_iterate_derivative_rootMultiplicity : (derivative^[rootMultiplicity t p] p).eval t = (rootMultiplicity t p).factorial • (p /ₘ (X - C t)^rootMultiplicity t p).eval t`
- `Polynomial.derivative_rootMultiplicity_of_root [CharZero] : p.IsRoot t → derivative.rootMultiplicity t = rootMultiplicity t p - 1`
- `Polynomial.mul_divByMonic_cancel_left : q.Monic → q * p /ₘ q = p`

### Polynomial analysis
- `Polynomial.hasDerivAt : HasDerivAt (fun x => eval x p) (eval x (derivative p)) x`
- `Polynomial.differentiable : Differentiable 𝕜 (fun x => eval x p)`
- `Polynomial.continuous : Continuous (fun x => eval x p)`
- `Polynomial.eval_mul : eval x (p * q) = eval x p * eval x q`
- `Polynomial.eval_add`, `Polynomial.eval_sub`, `Polynomial.eval_pow`

### Calculus
- `HasDerivAt.div : HasDerivAt c c' x → HasDerivAt d d' x → d x ≠ 0 → HasDerivAt (c/d) ((c'*d x - c x*d')/(d x)^2) x`
- `HasDerivAt.mul`, `HasDerivAt.sub`, `HasDerivAt.const_mul`
- `ContinuousOn.div : ContinuousOn f s → ContinuousOn g s → (∀ x ∈ s, g x ≠ 0) → ContinuousOn (f/g) s`
- `ContinuousOn.congr : ContinuousOn f s → EqOn g f s → ContinuousOn g s`

### DiffContOnCl
- `DiffContOnCl.mk : DifferentiableOn 𝕜 f s → ContinuousOn f (closure s) → DiffContOnCl 𝕜 f s`

---

## Part 5: Step-by-Step Implementation Plan

### Phase 1: Infrastructure (new helper lemmas)

1. **`rhoCRev_as_polynomial`**: Define `ρ_rev_poly : Polynomial ℂ` and prove `∀ w, eval w ρ_rev_poly = m.rhoCRev w`.

2. **`sigmaCRev_as_polynomial`**: Same for σ̃.

3. **`P_poly_def`**: Define `P_poly = 2 • σ_rev_poly * (X - 1) + ρ_rev_poly * (X + 1)` and show `eval w P_poly = m.modifiedNumeratorC_rev w` (or just relate to the raw formula).

4. **`P_poly_rootMultiplicity_ge_three`**: Show `3 ≤ rootMultiplicity 1 P_poly` using `lt_rootMultiplicity_iff_isRoot_iterate_derivative`. This requires proving `(derivative^[m] P_poly).eval 1 = 0` for m = 0, 1, 2, which reduces to the order conditions C₀, C₁, C₂.

5. **`rho_rev_rootMultiplicity_one`**: Show `rootMultiplicity 1 ρ_rev_poly = 1`. Root at 1 (consistency), not root of derivative at 1 (zero-stability: ρ̃'(1) ≠ 0).

### Phase 2: Factor and define cancelled form

6. **Factor**: Use `pow_mul_divByMonic_rootMultiplicity_eq` to get `(X-1)^3 * Q_poly = P_poly` and `(X-1) * R_poly = ρ_rev_poly`.

7. **`R_poly_eval_one_ne_zero`**: From `eval_divByMonic_pow_rootMultiplicity_ne_zero` or from the derivative identity.

8. **Define** `Gt_cancelled : ℂ → ℂ := fun w => (w - 1) * Q_poly.eval w / (2 * R_poly.eval w)`

9. **`Gt_cancelled_eq_Gt`**: Show `∀ w ∈ closedBall 0 1, Gt_cancelled w = Gt w` (assuming `hρ_no_other` for boundary points).

### Phase 3: Prove the two sorrys

10. **`continuousOn_Gtilde_closedBall`**: `Gt_cancelled` is continuous on `closedBall` (numerator polynomial continuous, denominator polynomial continuous and nonzero), transfer via `ContinuousOn.congr`.

11. **`hasDerivAt_Gtilde_one`**: `HasDerivAt Gt_cancelled (1/12) 1` from `Polynomial.hasDerivAt` + `HasDerivAt.div` + `HasDerivAt.mul`. Then transfer to piecewise `Gt` via `HasDerivAt.congr_of_eventuallyEq` (they agree on `ball(0,1) \ {1}` ∪ {1}).

### Phase 4: Compute the derivative value

The derivative at w=1:
```
Gt_cancelled(w) = n(w) / d(w)
n(w) = (w-1) * Q_poly.eval w
d(w) = 2 * R_poly.eval w

n(1) = 0, n'(1) = Q(1) (product rule: 1·Q(1) + 0·Q'(1))
d(1) = 2·R(1), d'(1) = 2·R'(1)

Gt'(1) = (n'(1)·d(1) - n(1)·d'(1)) / d(1)²
       = Q(1)·2R(1) / (2R(1))²
       = Q(1) / (2·R(1))
```

From `eval_iterate_derivative_rootMultiplicity`:
- `(derivative^[3] P_poly).eval 1 = 6 • Q_poly.eval 1`
- `(derivative^[1] ρ_rev_poly).eval 1 = 1 • R_poly.eval 1`

So `Q(1) = P'''(1)/6` and `R(1) = ρ̃'(1)`.

Need to compute `P'''(1)`:
- From the definition and order conditions, `P'''(1) = -σ(1)`.
- And `R(1) = ρ̃'(1) = -ρ'(1) = -σ(1)`.
- So `Gt'(1) = (-σ(1)/6) / (2·(-σ(1))) = 1/12`. ✓

Computing `P'''(1)` in Lean: use `Polynomial.derivative_mul`, `Polynomial.derivative_add`, etc., or compute `(derivative^[3] P_poly).eval 1` directly. The evaluation will involve sums over `Fin (s+1)` that reduce to order condition values.

---

## Part 6: On the Extra Hypothesis `hρ_no_other`

Can we derive `∀ w ∈ sphere(0,1), w ≠ 1 → ρ̃(w) ≠ 0` from A-stability + zero-stability?

**Claim**: For A-stable methods, if ρ(ζ₀) = 0 with |ζ₀| = 1 and ζ₀ ≠ 1, then σ(ζ₀) = 0 (so σ̃/ρ̃ has a removable singularity, not a pole).

**Proof sketch**: At z = 0, ρ(ζ₀) - 0·σ(ζ₀) = 0, so ζ₀ is a root of the stability polynomial at z=0. Zero-stability says this root is simple. For small z with Re(z) < 0, the perturbed root ζ(z) ≈ ζ₀ + z·σ(ζ₀)/ρ'(ζ₀) must satisfy |ζ(z)| ≤ 1. If σ(ζ₀) ≠ 0, then dζ/dz|_{z=0} = σ(ζ₀)/ρ'(ζ₀) ≠ 0, and the root moves. The constraint |ζ(z)| ≤ 1 for ALL Re(z) ≤ 0 means the root cannot move outward in any direction — but z can point in any direction in the left half-plane, so dζ/dz must be zero. Contradiction unless σ(ζ₀) = 0.

**More precisely**: For z = εe^{iφ} with cos(φ) ≤ 0 and ε small:
```
|ζ₀ + εe^{iφ}·σ(ζ₀)/ρ'(ζ₀)|² ≤ 1
```
Expanding: `|ζ₀|² + 2ε·Re(e^{iφ}·σ(ζ₀)/ρ'(ζ₀)·conj(ζ₀)) + O(ε²) ≤ 1`
Since |ζ₀| = 1: `2ε·Re(e^{iφ}·σ(ζ₀)·conj(ζ₀)/ρ'(ζ₀)) ≤ O(ε²)`
Dividing by ε → 0: `Re(e^{iφ}·σ(ζ₀)·conj(ζ₀)/ρ'(ζ₀)) ≤ 0` for ALL φ with cos(φ) ≤ 0.

Let `c = σ(ζ₀)·conj(ζ₀)/ρ'(ζ₀)`. We need `Re(e^{iφ}·c) ≤ 0` for all φ in [π/2, 3π/2]. But `Re(e^{iφ}·c) = |c|·cos(φ + arg(c))`. As φ ranges over [π/2, 3π/2], `cos(φ + arg(c))` takes both positive and negative values (unless |c| = 0). So c = 0, i.e., σ(ζ₀) = 0.

**This means**: with A-stability + zero-stability, σ and ρ share all unit-circle roots except possibly ζ=1. So σ̃/ρ̃ has removable singularities at other unit-circle roots of ρ̃, and the **Lean junk value** σ̃(w₀)/ρ̃(w₀) = 0/0 = 0 in Lean. But (w₀+1)/(2(1-w₀)) ≠ 0, so Gt(w₀) ≠ 0, while the cancelled form Gt_cancelled(w₀) would give a finite value.

**Problem**: Even with σ(ζ₀) = 0, the piecewise function Gt(w₀) = 0 - (w₀+1)/(2(1-w₀)) (Lean junk), while the true limit is σ̃'(w₀)/ρ̃'(w₀) - (w₀+1)/(2(1-w₀)). These don't match → Gt is NOT continuous at w₀.

**Therefore: you cannot avoid the extra hypothesis.** The piecewise definition of Gt gives wrong values at other unit-circle roots of ρ̃ (because of Lean's 0/0=0 convention). You MUST either:

(a) Add `hρ_no_other` as a hypothesis, OR
(b) Redefine Gt to use the cancelled polynomial form everywhere (not just at w=1), OR
(c) Add more cases to the piecewise definition to handle other boundary roots.

**Recommendation: Option (b) — redefine Gt in `order_ge_three_not_aStable_core`** to use `Gt_cancelled` directly. Then:
- The DifferentiableOn proof (lines 1146-1173) needs updating to use the new definition
- The boundary non-negativity proof (lines 1178-1204) needs a new argument showing `Gt_cancelled(w) = σ(w⁻¹)/ρ(w⁻¹) - (w+1)/(2(1-w))` for w on the sphere with ρ̃(w) ≠ 0, plus separate handling when ρ̃(w) = 0

**Actually, the simplest approach**: Keep `hρ_no_other` AND prove it from A-stability + zero-stability using the argument above. This is a standalone lemma:

```lean
theorem IsAStable.rhoCRev_ne_zero_of_norm_one (m : LMM s) (ha : m.IsAStable)
    (hzs : m.IsZeroStable) (w : ℂ) (hw : ‖w‖ = 1) (hw1 : w ≠ 1) :
    m.rhoCRev w ≠ 0
```

The proof is non-trivial (perturbation argument) but feasible. Alternatively, just add it as a hypothesis and move on — the mathematical content of the theorem is unchanged.

---

## Part 7: Priority Ordering

1. **First**: Prove `hasDerivAt_Gtilde_one` — it's self-contained and doesn't need boundary analysis. Use the polynomial factorization approach with `Polynomial.hasDerivAt` + `HasDerivAt.div` + `HasDerivAt.congr_of_eventuallyEq`.

2. **Second**: Prove `continuousOn_Gtilde_closedBall` with the extra hypothesis `hρ_no_other` added.

3. **Third** (if needed): Prove `hρ_no_other` from A-stability + zero-stability, or propagate the hypothesis.

---

## Part 8: Alternative — Submit to Aristotle

The polynomial factorization + derivative computation is highly algebraic. Consider submitting both sorry lemmas to Aristotle with:
- The polynomial definitions
- The connection lemmas (eval = rhoCRev/sigmaCRev)
- The order conditions and zero-stability hypothesis
- The specific Mathlib lemma names listed above

Aristotle may handle the bookkeeping more efficiently than manual proof.
