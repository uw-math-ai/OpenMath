# Consultant Advice: Breaking the 16-Cycle Deadlock on the Dahlquist Barrier

## Executive Summary

After 16 cycles of failed manual polynomial infrastructure, the approach must fundamentally change. The two remaining sorrys (`hasDerivAt_Gtilde_one` at line 930, `continuousOn_Gtilde_closedBall` at line 947) both stem from the same root cause: proving properties of a removable singularity in the piecewise function `Gt`.

**The key insight**: Don't try to prove properties of the piecewise function. Instead, **redefine Gt using a cancelled polynomial form** that has no singularity at all, then show it agrees with the piecewise definition where needed. This transforms the problem from complex analysis (limits, removable singularities) into pure algebra (polynomial factorization via Mathlib's `Polynomial` API).

---

## Part 1: Why All Previous Approaches Failed

Cycles 19–34 attempted to prove `ContinuousOn` and `HasDerivAt` for:
```lean
fun w => if w = 1 then 0 else σ_rev w / ρ_rev w - (w + 1) / (2 * (1 - w))
```

This requires showing that the limit as `w → 1` exists and equals 0 (for continuity) and computing the derivative at `w = 1` (for `HasDerivAt`). Both require L'Hôpital-type arguments on the combined fraction, which is a 0/0 form at `w = 1`. The cycles kept building infrastructure (reversed polynomial derivatives, boundary lemmas) but never completed the limit computation because:

1. **Working at the function level is wrong.** The functions `σ_rev`, `ρ_rev` are defined as `ℂ → ℂ` sums, not as `Polynomial ℂ` objects. Without the `Polynomial` API, you can't use `divByMonic` to algebraically cancel `(X - 1)` factors.

2. **The piecewise definition creates artificial difficulty.** At `w = 1`, the function uses an `if` branch. Proving `HasDerivAt` of an `if`-defined function requires `Filter.EventuallyEq` gymnastics that are harder than the underlying math.

3. **Boundary roots of ρ̃ were never addressed.** The `ContinuousOn` on `closedBall(0,1)` requires handling points on `sphere(0,1)` where `ρ̃(w) = 0` (other unit-circle roots of ρ̃). Previous cycles never resolved this.

---

## Part 2: The Right Mathematical Argument

### Step 1: Rewrite as a single fraction

For `w ≠ 1` with `ρ̃(w) ≠ 0`:
```
Gt(w) = σ̃(w)/ρ̃(w) - (w+1)/(2(1-w))
      = σ̃(w)/ρ̃(w) + (w+1)/(2(w-1))
      = [2σ̃(w)(w-1) + ρ̃(w)(w+1)] / [2ρ̃(w)(w-1)]
      = P(w) / D(w)
```
where `P(w) = 2σ̃(w)(w-1) + ρ̃(w)(w+1)` and `D(w) = 2ρ̃(w)(w-1)`.

### Step 2: Factor using order conditions

**P has a triple zero at w = 1:**
- P(1) = 2σ̃(1)·0 + ρ̃(1)·2 = 0·2 + 0·2 = 0 ✓ (C₀: ρ(1) = 0)
- P'(1) = 2σ̃'(1)·0 + 2σ̃(1) + ρ̃'(1)·2 + ρ̃(1) = 2σ(1) + 2ρ̃'(1) = 2σ(1) - 2ρ'(1) = 0 ✓ (C₁: σ(1) = ρ'(1), and ρ̃'(1) = -ρ'(1))
- P''(1) = 0 ✓ (from C₂)

So P(w) = (w-1)³ · Q(w) for some polynomial Q.

**ρ̃ has a simple zero at w = 1:**
- ρ̃(1) = ρ(1) = 0 ✓ (consistency)
- ρ̃'(1) = -ρ'(1) ≠ 0 ✓ (zero-stability)

So ρ̃(w) = (w-1) · R(w) for some polynomial R with R(1) = ρ̃'(1) ≠ 0.

**Cancel:**
```
Gt(w) = (w-1)³Q(w) / [2(w-1)²R(w)] = (w-1)Q(w) / [2R(w)]
```

This last expression is a **ratio of polynomial functions** that is well-defined at w = 1 (evaluating to 0·Q(1)/(2R(1)) = 0), with denominator R(w) ≠ 0 on the open ball (since ρ̃ ≠ 0 on ball(0,1) and w ≠ 1 there, so R(w) = ρ̃(w)/(w-1) ≠ 0) and at w = 1 (since R(1) ≠ 0).

### Step 3: Derivative computation

```
Gt(w) = n(w)/d(w)  where  n(w) = (w-1)·Q(w),  d(w) = 2R(w)
```

At w = 1:
- n(1) = 0, n'(1) = Q(1) (product rule: 1·Q(1) + 0·Q'(1))
- d(1) = 2R(1), d'(1) = 2R'(1)

By quotient rule: Gt'(1) = (Q(1)·2R(1) - 0·2R'(1)) / (2R(1))² = Q(1)/(2R(1))

Now: Q(1) = P'''(1)/6 (since P = (w-1)³Q → P'''(1) = 6Q(1)) and R(1) = ρ̃'(1) = -ρ'(1) = -σ(1).

P'''(1) = -σ(1) (computed from the order conditions C₁, C₂, C₃ — see Part 5 below).

Therefore: Gt'(1) = (-σ(1)/6) / (2·(-σ(1))) = 1/12. ✓

---

## Part 3: The Boundary Root Issue

**Problem**: `ContinuousOn Gt (closedBall 0 1)` requires continuity at boundary points `w₀ ∈ sphere(0,1)` where `ρ̃(w₀) = 0` (i.e., other unit-circle roots of ρ). The cancelled form `(w-1)Q(w)/(2R(w))` still has `R(w₀) = 0` at such points.

**There are three solutions, in order of preference:**

### Solution A: Prove R(w) ≠ 0 on all of closedBall(0,1)

R(w₀) = 0 iff ρ̃(w₀) = 0 and w₀ ≠ 1. For |w₀| < 1, this can't happen (already proved: `rhoCRev_ne_zero_of_norm_lt_one`). At w₀ = 1, R(1) = ρ̃'(1) ≠ 0. For |w₀| = 1 with w₀ ≠ 1, we need to show ρ̃(w₀) ≠ 0.

**Claim**: For an A-stable, zero-stable method, ρ has no unit-circle roots other than ζ = 1.

**Proof**: Suppose ρ(ζ₀) = 0 with |ζ₀| = 1, ζ₀ ≠ 1. By zero-stability, ζ₀ is a simple root of ρ. For small z with Re(z) ≤ 0, the stability polynomial ρ(ζ) - zσ(ζ) has a root ζ(z) near ζ₀ with ζ(z) ≈ ζ₀ + z·σ(ζ₀)/ρ'(ζ₀). A-stability requires |ζ(z)| ≤ 1 for all Re(z) ≤ 0. Writing c = σ(ζ₀)/ρ'(ζ₀), we need Re(z·c·conj(ζ₀)) ≤ 0 for all z with Re(z) ≤ 0 (from the first-order expansion of |ζ(z)|² ≤ 1). Since z ranges over the closed left half-plane, e^{iφ}·c·conj(ζ₀) must point into the closed left half-plane for all φ ∈ [π/2, 3π/2], which forces c·conj(ζ₀) = 0, hence σ(ζ₀) = 0.

But if σ(ζ₀) = 0 too, then ρ̃(w₀) = 0 and σ̃(w₀) = 0 where w₀ = ζ₀⁻¹. The piecewise Gt(w₀) = 0/0 - (w₀+1)/(2(1-w₀)) in Lean (junk value from 0/0 = 0), while the actual limit is σ̃'(w₀)/ρ̃'(w₀) - (w₀+1)/(2(1-w₀)). These don't match, so the piecewise function is NOT continuous there.

**However**: In the cancelled form `(w-1)Q(w)/(2R(w))`, if R(w₀) = 0 then the numerator (w₀-1)Q(w₀) also involves the common factor. But proving this requires further polynomial cancellation.

**Better approach**: The perturbation argument shows σ(ζ₀) = 0. Then ρ̃(w₀) = 0 and σ̃(w₀) = 0 means P(w₀) = 2·0·(w₀-1) + 0·(w₀+1) = 0. So P is divisible by (w-w₀) just as ρ̃ is. The cancellation works: Q has at least the same multiplicity of root at w₀ as R does, so (w-1)Q/R is actually analytic at w₀.

**Practical recommendation**: Prove the standalone lemma:
```lean
theorem IsAStable.rhoC_ne_zero_of_unit_circle_ne_one (m : LMM s)
    (ha : m.IsAStable) (hzs : m.IsZeroStable)
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) (hne : ζ ≠ 1) (hρ : m.rhoC ζ = 0) : False
```
This would give ρ̃(w) ≠ 0 for all |w| = 1 with w ≠ 1, hence R(w) ≠ 0 on closedBall, making `ContinuousOn` trivial.

The proof is non-trivial (perturbation + A-stability), but it's a clean, standalone lemma worth having. **If time-constrained, use Solution B instead.**

### Solution B: Add the hypothesis (simplest, fastest)

Add `(hρ_no_other : ∀ ζ : ℂ, m.rhoC ζ = 0 → ‖ζ‖ = 1 → ζ = 1)` as a hypothesis to `hasDerivAt_Gtilde_one` and `continuousOn_Gtilde_closedBall`. Then derive it in `order_ge_three_not_aStable` from A-stability + zero-stability (using the perturbation argument above, or leaving that as a separate lemma).

This keeps the sorry-closure focused on the polynomial algebra rather than the perturbation theory.

### Solution C: Redefine Gt using the cancelled form everywhere

Replace the piecewise definition entirely:
```lean
let Gt : ℂ → ℂ := fun w => (w - 1) * Q_poly.eval w / (2 * R_poly.eval w)
```
This avoids the boundary root issue because at points where R = 0, Lean gives 0 for the division, and the function may not be literally continuous there. But you can prove continuity on `closedBall(0,1) \ {bad points}` and handle bad points separately.

**Verdict**: Solution A is best but hardest. Solution B is pragmatic. Solution C requires restructuring the existing proof.

---

## Part 4: Concrete Implementation Strategy

### Recommended approach: Use `Polynomial ℂ` with `divByMonic`

**Phase 1: Lift to Polynomial ℂ**

```lean
-- Step 1: Define the reversed polynomials as actual Polynomial ℂ objects
let ρ_rev_poly : Polynomial ℂ := ∑ j : Fin (s+1),
  Polynomial.C (↑(m.α (Fin.rev j)) : ℂ) * Polynomial.X ^ (j : ℕ)

-- Step 2: Prove eval matches the function definition
have h_ρ_eval : ∀ w, ρ_rev_poly.eval w = m.rhoCRev w := by
  intro w; simp [rhoCRev, Polynomial.eval_finset_sum, Polynomial.eval_pow,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
```

**Phase 2: Prove root multiplicity**

```lean
-- Step 3: ρ_rev_poly has root at 1
have hρ_root : ρ_rev_poly.IsRoot 1 := by
  rw [Polynomial.IsRoot, h_ρ_eval]; exact rhoCRev_one_eq_zero m hcons

-- Step 4: Factor out (X - 1)
let R_poly := ρ_rev_poly /ₘ (Polynomial.X - Polynomial.C 1)
have h_ρ_factor : ρ_rev_poly = (Polynomial.X - Polynomial.C 1) * R_poly := by
  rw [Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hρ_root]

-- Step 5: R_poly.eval 1 ≠ 0
-- This requires connecting ρ_rev_poly.derivative.eval 1 to R_poly.eval 1
-- Key identity: if p = (X - C a) * q, then p.derivative.eval a = q.eval a
-- Proof: p' = q + (X - C a) * q', so p'(a) = q(a) + 0 = q(a)
```

**Phase 3: Build P_poly and prove triple root**

```lean
-- P_poly = 2 * σ_rev_poly * (X - 1) + ρ_rev_poly * (X + 1)
-- Need: P_poly.eval 1 = 0, (derivative P_poly).eval 1 = 0,
--       (derivative (derivative P_poly)).eval 1 = 0

-- Use Polynomial.IsRoot and derivative chain
-- Or use: Polynomial.rootMultiplicity_le_iff / lt_rootMultiplicity_iff
```

**Phase 4: Define cancelled form and prove the two sorrys**

```lean
-- Q_poly = P_poly /ₘ (X - 1)^3
-- Gt_cancelled(w) = (w-1) * Q_poly.eval w / (2 * R_poly.eval w)

-- HasDerivAt: use Polynomial.hasDerivAt + HasDerivAt.mul + HasDerivAt.div
-- ContinuousOn: use Polynomial.continuous + ContinuousOn.div (with R ≠ 0 on closedBall)
```

---

## Part 5: Computing P'''(1) = -σ(1)

This is the critical algebraic computation. Here's the derivation:

P(w) = 2σ̃(w)(w-1) + ρ̃(w)(w+1)

Using Leibniz rule for higher derivatives:
- P''' = 2[σ̃'''(w-1) + 3σ̃''·1 + 3σ̃'·0 + σ̃·0] + [ρ̃'''(w+1) + 3ρ̃''·1 + 3ρ̃'·0 + ρ̃·0]

At w = 1:
- P'''(1) = 2[σ̃'''(1)·0 + 3σ̃''(1)] + [ρ̃'''(1)·2 + 3ρ̃''(1)]
- P'''(1) = 6σ̃''(1) + 2ρ̃'''(1) + 3ρ̃''(1)

The reversed polynomial derivatives at w = 1 relate to order condition sums:

For a polynomial f(w) = ∑ cⱼ wʲ, the k-th derivative at 1 is:
- f(1) = ∑ cⱼ
- f'(1) = ∑ j·cⱼ
- f''(1) = ∑ j(j-1)cⱼ
- f'''(1) = ∑ j(j-1)(j-2)cⱼ

For ρ̃(w) = ∑ α_{s-j} wʲ (using reversed coefficients):
- ρ̃(1) = ∑ αⱼ = 0  (C₀)
- ρ̃'(1) = ∑ j·α_{s-j} = ∑ (s-k)·αₖ = s·∑αₖ - ∑k·αₖ = -ρ'(1) = -σ(1)
- ρ̃''(1) = ∑ j(j-1)α_{s-j} = ... (expressible via order conditions)

For σ̃(w) = ∑ β_{s-j} wʲ:
- σ̃(1) = ∑ βⱼ = σ(1) = ρ'(1)
- σ̃'(1) = ∑ j·β_{s-j} = s·∑βⱼ - ∑k·βₖ = s·σ(1) - ∑k·βₖ

The order conditions (V_q = 0 for q ≤ p) give:
- V₀ = ∑ αⱼ = 0 (i.e., ρ(1) = 0)
- V₁ = ∑ j·αⱼ - ∑ βⱼ = 0 (i.e., ρ'(1) = σ(1))
- V₂ = ∑ j²·αⱼ - 2∑ j·βⱼ = 0
- V₃ = ∑ j³·αⱼ - 3∑ j²·βⱼ = 0

**Rather than computing P'''(1) symbolically from the general case**, a cleaner approach in Lean is:

1. Show `rootMultiplicity 1 P_poly ≥ 3` using `Polynomial.lt_rootMultiplicity_iff` (or the iterated derivative characterization).
2. This requires showing `P_poly.eval 1 = 0`, `(derivative P_poly).eval 1 = 0`, `(derivative (derivative P_poly)).eval 1 = 0`.
3. Each evaluation reduces to sums over coefficients, which simplify using the order conditions.

Then `Q_poly.eval 1 = (derivative^[3] P_poly).eval 1 / 6` (from the iterated derivative formula at the root).

And `P'''(1) / 6 = Q(1)`, combined with `R(1) = ρ̃'(1) = -σ(1)`, gives:
```
Gt'(1) = Q(1) / (2R(1))
```

To show this equals 1/12, we need `Q(1) = -σ(1)/6` and `R(1) = -σ(1)`, giving:
```
Gt'(1) = (-σ(1)/6) / (2·(-σ(1))) = (-σ(1)/6) / (-2σ(1)) = 1/12
```

---

## Part 6: Key Mathlib Lemmas

### Polynomial factorization (critical path)
- `Polynomial.IsRoot` : `p.IsRoot a ↔ p.eval a = 0`
- `Polynomial.dvd_iff_isRoot` : `(X - C a) ∣ p ↔ p.IsRoot a`
- `Polynomial.mul_divByMonic_eq_iff_isRoot` : factoring out a root
- `Polynomial.rootMultiplicity` : the multiplicity of a root
- `Polynomial.pow_rootMultiplicity_dvd` : `(X - C a)^rootMultiplicity a p ∣ p`
- `Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero` : quotient nonzero at root
- Iterated derivative characterization: if charZero, `n < rootMultiplicity t p ↔ ∀ m ≤ n, (derivative^[m] p).IsRoot t`

### Polynomial calculus
- `Polynomial.hasDerivAt` : `HasDerivAt (fun x => eval x p) (eval x (derivative p)) x`
- `Polynomial.differentiable` : polynomials are differentiable
- `Polynomial.continuous_eval` : polynomials are continuous
- `Polynomial.eval_mul`, `Polynomial.eval_add`, `Polynomial.eval_sub`
- `Polynomial.eval_pow`, `Polynomial.eval_C`, `Polynomial.eval_X`

### Calculus for the quotient
- `HasDerivAt.div` : quotient rule for `HasDerivAt`
- `HasDerivAt.mul` : product rule
- `ContinuousOn.div` : `ContinuousOn f s → ContinuousOn g s → (∀ x ∈ s, g x ≠ 0) → ContinuousOn (f/g) s`
- `HasDerivAt.congr_of_eventuallyEq` : transfer `HasDerivAt` across locally equal functions

### DiffContOnCl
- `DiffContOnCl.mk` : construct from `DifferentiableOn` + `ContinuousOn` on closure

---

## Part 7: Concrete Proof Sketch for `hasDerivAt_Gtilde_one`

```lean
theorem hasDerivAt_Gtilde_one ... := by
  -- 1. Build Polynomial ℂ objects for ρ̃ and σ̃
  -- 2. Prove ρ̃_poly has simple root at 1, factor as (X-1)·R_poly
  -- 3. Build P_poly = 2·σ̃_poly·(X-1) + ρ̃_poly·(X+1)
  -- 4. Show P_poly has rootMultiplicity ≥ 3 at 1 (using order conditions)
  -- 5. Factor P_poly = (X-1)³·Q_poly
  -- 6. Define Gt_cancelled(w) = (w-1)·Q_poly.eval w / (2·R_poly.eval w)
  -- 7. Show HasDerivAt Gt_cancelled (1/12) 1 via:
  --    - HasDerivAt for (w-1)·Q.eval w at w=1: derivative = Q(1) (product rule)
  --    - HasDerivAt for 2·R.eval w at w=1: derivative = 2·R'.eval 1
  --    - HasDerivAt.div gives (Q(1)·2R(1) - 0·2R'(1))/(2R(1))² = Q(1)/(2R(1))
  -- 8. Compute Q(1)/(2R(1)):
  --    - Q(1) = P'''(1)/6 (from iterated derivative at root of multiplicity ≥ 3)
  --    - R(1) = ρ̃'(1) (from derivative of factored polynomial)
  --    - The ratio equals 1/12 using order conditions
  -- 9. Transfer to piecewise function via HasDerivAt.congr_of_eventuallyEq
  --    Key: the cancelled form and piecewise form agree on ball(1, δ) \ {1} for some δ,
  --    and both equal 0 at w=1. Use nhds_within filter.
  sorry
```

**The crucial step 9**: `HasDerivAt f c x` depends only on `f` in a neighborhood of `x`. Since `Gt_cancelled` and the piecewise `Gt` agree on `ball(0,1)` (where both denominators are nonzero), and `ball(0,1)` is a neighborhood of `1` (wait — `1 ∉ ball(0,1)` since `‖1‖ = 1`!), this doesn't directly work.

**CRITICAL OBSERVATION**: `1 ∈ closedBall(0,1)` but `1 ∉ ball(0,1)`. However, `ball(0,1)` IS a member of the nhds filter of 1 in the subspace topology? No — 1 is on the boundary.

**The fix**: The two functions agree on `{w | w ≠ 1}`, which contains a **punctured** neighborhood of 1. But `HasDerivAt` at 1 only requires agreement in a full neighborhood. Since both functions equal 0 at w = 1, and agree on `{w | w ≠ 1}`, they agree everywhere. So they're literally the same function!

Wait — not quite. The piecewise function at `w ≠ 1` is `σ_rev w / ρ_rev w - (w + 1) / (2 * (1 - w))`, and the cancelled form is `(w-1) * Q_poly.eval w / (2 * R_poly.eval w)`. These are equal when `ρ_rev w ≠ 0` and `w ≠ 1`, which holds on `ball(0,1)`. And on `ball(0,1)` the point `w = 1` is not present (since `‖1‖ = 1`). So on `ball(0,1)`, the piecewise function never takes the `if w = 1` branch, and equals the formula, which equals the cancelled form.

But `ball(0,1)` is NOT a neighborhood of `1` in ℂ! So we can't use `HasDerivAt.congr_of_eventuallyEq` with this set.

**Resolution**: Use the **real line** approach. Consider the restriction of `Gt` to the real interval `(0, 2)`. The function `t ↦ Gt(t)` for real `t` near 1 has:
- For `t ∈ (0, 1)`: `Gt(t)` = the formula (ρ̃(t) ≠ 0 since |t| < 1, and t ≠ 1)
- For `t = 1`: `Gt(1) = 0`
- For `t ∈ (1, 2)`: `Gt(t)` = the formula (ρ̃(t) might be zero or nonzero)

Hmm, `HasDerivAt` at `w = 1` in the complex sense requires convergence from all directions, not just along the real line.

**ACTUAL RESOLUTION**: The cancelled form `Gt_cancelled` is well-defined and differentiable at all points where `R_poly.eval w ≠ 0`, including `w = 1` (since `R(1) ≠ 0`). Prove `HasDerivAt Gt_cancelled (1/12) 1` directly. Then show `Gt = Gt_cancelled` everywhere:
- At `w = 1`: both equal 0.
- At `w ≠ 1`: the algebraic identity `σ̃(w)/ρ̃(w) - (w+1)/(2(1-w)) = (w-1)Q(w)/(2R(w))` holds whenever `ρ̃(w) ≠ 0` and `w ≠ 1`. But on `sphere(0,1)` with `ρ̃(w) = 0`, the piecewise gives `0 - (w+1)/(2(1-w))` while the cancelled form gives `(w-1)Q(w)/(2R(w))` with `R(w) = 0` → `0` in Lean.

If `ρ̃(w₀) = 0` on the sphere, the two functions disagree: piecewise gives `-(w₀+1)/(2(1-w₀))` while cancelled gives `0` (junk). So they're NOT the same function globally.

**BUT**: For `HasDerivAt` at `w = 1`, we only need agreement in a neighborhood of 1. Is there a neighborhood of 1 contained in `{w | ρ̃(w) ≠ 0 ∨ w = 1}`? Yes! Since ρ̃ is continuous, ρ̃(1) = 0 but ρ̃'(1) ≠ 0, so the zeros of ρ̃ near 1 are isolated. The only zero of ρ̃ in some ball around 1 is at 1 itself. So in `ball(1, δ)` for small enough δ, `ρ̃(w) ≠ 0` for `w ≠ 1`. On this punctured ball, the two functions agree, and at `w = 1`, both equal 0. So they agree on `ball(1, δ)`, which is a neighborhood of 1.

Use: `Filter.EventuallyEq.hasDerivAt_iff` — if two functions agree on a neighborhood of a point, they have the same `HasDerivAt` property there.

**To prove the punctured ball equality**: Use `Polynomial.IsRoot` and the fact that a nonzero polynomial has finitely many roots. Since ρ̃ is not identically zero, its roots form a finite set, so there exists δ > 0 such that `ball(1, δ) ∩ {w | ρ̃(w) = 0} = {1}`.

**Mathlib**: `Polynomial.finite_setOf_roots` or use that a nonzero analytic function has isolated zeros.

---

## Part 8: Alternative Approach — Avoid `Polynomial ℂ` Entirely

If constructing `Polynomial ℂ` objects and using `divByMonic` proves too cumbersome in Lean, here's a purely analytic alternative:

### For `hasDerivAt_Gtilde_one`:

Work with the `HasDerivAt` filter directly. The function `Gt` satisfies:
```
Gt(w) - Gt(1) = Gt(w) = σ̃(w)/ρ̃(w) + (w+1)/(2(w-1))   for w near 1, w ≠ 1
```

Combine into a single fraction:
```
Gt(w) = [2σ̃(w)(w-1) + ρ̃(w)(w+1)] / [2ρ̃(w)(w-1)]
```

Now use the fact that both numerator and denominator have `HasDerivAt` at w = 1 (they're polynomial functions). Since the numerator has a triple zero and denominator a double zero, show:

```
Gt(w) = [(w-1)³ · h_num(w)] / [(w-1)² · h_den(w)]  =  (w-1) · h_num(w) / h_den(w)
```

where `h_num`, `h_den` are analytic with `h_den(1) ≠ 0`.

In Lean, this can be done without `Polynomial.divByMonic` by directly defining:
```lean
-- For f analytic with f(a) = 0, define f(w)/(w-a) as a function
-- using the removable singularity theorem or direct construction
```

But this is essentially re-implementing `divByMonic` at the function level, which is harder. **Stick with the `Polynomial ℂ` approach.**

---

## Part 9: Priority and Time Allocation

1. **hasDerivAt_Gtilde_one (70% of effort)**: This is the harder but more self-contained sorry. The proof strategy is clear (polynomial factorization → quotient rule → evaluate at 1). The main risk is the `Polynomial ℂ` construction and the `eval` connection to the function-level definitions.

2. **continuousOn_Gtilde_closedBall (30% of effort)**: Once you have the polynomial infrastructure from (1), this follows from `ContinuousOn.div` + `Polynomial.continuous` + `R_poly ≠ 0` on closedBall. The boundary root issue needs Solution A or B from Part 3.

3. **Submit to Aristotle**: Both sorrys are good candidates. Frame the Aristotle submission as: "Given these polynomial definitions and these lemmas about their roots, prove `HasDerivAt` / `ContinuousOn` using the quotient `(w-1)Q(w)/(2R(w))`."

---

## Part 10: Specific Tactic Hints

### Connecting `Polynomial.eval` to function-level definitions

The biggest practical challenge: showing `ρ_rev_poly.eval w = m.rhoCRev w`.

```lean
-- rhoCRev w = ∑ j, (m.α (Fin.rev j) : ℂ) * w ^ (j : ℕ)
-- ρ_rev_poly = ∑ j, C (m.α (Fin.rev j) : ℂ) * X ^ j
-- eval w ρ_rev_poly = ∑ j, (m.α (Fin.rev j) : ℂ) * w ^ j
-- These should be definitionally equal after unfolding
```

Tactics: `simp [rhoCRev, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]`

### Proving the derivative identity for factored polynomials

If `p = (X - C a) * q`, then `p.derivative.eval a = q.eval a`:
```lean
-- derivative ((X - C a) * q) = q + (X - C a) * q.derivative
-- eval a: q.eval a + 0 = q.eval a
```

Use: `Polynomial.derivative_mul`, `Polynomial.derivative_sub`, `Polynomial.derivative_X`, `Polynomial.derivative_C`

### Order condition evaluations

To show e.g. `P_poly.eval 1 = 0`, expand `P_poly` and use:
```lean
-- P_poly.eval 1 = 2 * σ_rev_poly.eval 1 * (1 - 1) + ρ_rev_poly.eval 1 * (1 + 1)
--               = 2 * σ(1) * 0 + ρ(1) * 2 = 0
simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_C, Polynomial.eval_X, h_σ_eval, h_ρ_eval,
      rhoCRev_one_eq_zero, sigmaCRev_one]
```

### The key `HasDerivAt.div` application

```lean
-- n(w) = (w - 1) * Q.eval w
-- d(w) = 2 * R.eval w
-- n has HasDerivAt at 1:
have hn := (hasDerivAt_id (1 : ℂ)).sub (hasDerivAt_const 1 1) |>.mul
           (Polynomial.hasDerivAt Q_poly 1)
-- After simplification: n'(1) = 1 * Q.eval 1 + 0 * Q.derivative.eval 1 = Q(1)
-- d has HasDerivAt at 1:
have hd := (hasDerivAt_const 1 2).mul (Polynomial.hasDerivAt R_poly 1)
-- d'(1) = 0 * R.eval 1 + 2 * R.derivative.eval 1 = 2R'(1)
-- d(1) = 2 * R.eval 1 ≠ 0
-- HasDerivAt.div gives the quotient rule
```
