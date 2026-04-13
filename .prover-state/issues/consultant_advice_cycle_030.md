# Consultant Advice: Closing the Dahlquist Second Barrier

## Executive Summary

You have two remaining sorrys:
1. `hasDerivAt_Gtilde_one` (line 930) — derivative computation at the removable singularity
2. `continuousOn_Gtilde_closedBall` (line 947) — continuity through the removable singularity

Everything else is done: the minimum principle (`re_nonneg_of_frontier_re_nonneg`), boundary non-negativity, interior negative point extraction, and the final contradiction are all proved. The blockers are purely about the removable singularity at w=1. Here is how to close them.

---

## Part 1: The Mathematical Argument

### Why previous cycles failed

Cycles 19–29 kept trying to prove `ContinuousOn` and `HasDerivAt` by direct limit computation on the piecewise-defined function `Gt(w) = if w = 1 then 0 else σ̃(w)/ρ̃(w) - (w+1)/(2(1-w))`. This requires showing the limit exists and equals 0, which requires knowing the order of vanishing of numerator and denominator — i.e., the polynomial factorization argument. But the factorization was never completed because it requires manipulating `modifiedNumeratorC` as a `Polynomial ℂ` (not just a function ℂ → ℂ) to use `divByMonic` and `rootMultiplicity`.

### The right approach: work with Mathlib Polynomials

The key insight: **don't try to prove continuity/differentiability of the piecewise function directly**. Instead:

1. **Rewrite Gt as a ratio of polynomials with the singularity already cancelled.**
2. **Show the cancelled form equals the piecewise definition away from w=1.**
3. **Deduce continuity and differentiability from the polynomial form.**

Concretely, define:
- `P(w) = 2·σ̃(w)·(w-1) + ρ̃(w)·(w+1)` — this is the "reversed modifiedNumerator"
- `D(w) = 2·ρ̃(w)·(w-1)`

Then for w ≠ 1 with ρ̃(w) ≠ 0:
```
Gt(w) = σ̃(w)/ρ̃(w) - (w+1)/(2(1-w))
      = σ̃(w)/ρ̃(w) + (w+1)/(2(w-1))
      = [2σ̃(w)(w-1) + ρ̃(w)(w+1)] / [2ρ̃(w)(w-1)]
      = P(w) / D(w)
```

Now the order conditions give P(1) = P'(1) = P''(1) = 0 (triple zero), and D has a double zero at w=1. So `P(w) = (w-1)³ · Q(w)` and `D(w) = 2(w-1)² · R(w)` where R(w) = (w-1)⁻¹ρ̃(w) · 1 ... Actually, more precisely: ρ̃(1) = ρ(1) = 0, so ρ̃(w) = (w-1)·R̃(w) for some polynomial R̃ with R̃(1) = ρ̃'(1) ≠ 0. Then D(w) = 2(w-1)²R̃(w), and:

```
Gt(w) = P(w)/D(w) = (w-1)³Q(w) / [2(w-1)²R̃(w)] = (w-1)Q(w) / [2R̃(w)]
```

This last expression **(w-1)Q(w)/(2R̃(w))** is a well-defined rational function at w=1 (evaluating to 0), is continuous everywhere R̃ ≠ 0 (which includes the closed unit ball), and is differentiable there.

### The key point

**You should define `Gt` not as the piecewise function, but as the cancelled rational function `(w-1)·Q(w)/(2·R̃(w))`**, and then prove it equals the original piecewise definition on ball(0,1). This immediately gives continuity and differentiability with no removable singularity argument needed.

---

## Part 2: Concrete Proof Strategy

### Strategy A: Use Mathlib `Polynomial` (Recommended)

Lift everything to `Polynomial ℂ`:

```
-- Define the polynomials as actual Polynomial ℂ objects
let ρ_poly : Polynomial ℂ := ∑ j : Fin (s+1), Polynomial.C (m.α (Fin.rev j) : ℂ) * Polynomial.X ^ (j : ℕ)
let σ_poly : Polynomial ℂ := ∑ j : Fin (s+1), Polynomial.C (m.β (Fin.rev j) : ℂ) * Polynomial.X ^ (j : ℕ)

-- P(w) = 2σ̃(w)(w-1) + ρ̃(w)(w+1)
let P_poly := 2 • σ_poly * (Polynomial.X - 1) + ρ_poly * (Polynomial.X + 1)

-- Factor out (X - 1)² from P (uses rootMultiplicity ≥ 3, factor out 2)
-- The key Mathlib lemma:
-- Polynomial.pow_mul_divByMonic_rootMultiplicity_eq :
--   (X - C a) ^ rootMultiplicity a p * (p /ₘ (X - C a) ^ rootMultiplicity a p) = p
```

Then use:
- `Polynomial.dvd_iff_isRoot` : `(X - C 1) ∣ P_poly ↔ P_poly.IsRoot 1`
- Show `P_poly.IsRoot 1` from `modifiedNumeratorC_one` (already proved)
- Show the derivative vanishes using the order ≥ 2 condition
- Show the second derivative vanishes using the order ≥ 3 condition

For the derivative/evaluation conditions at w=1, use:
- `Polynomial.eval_iterate_derivative_rootMultiplicity` — evaluating iterated derivatives at roots
- `Polynomial.rootMultiplicity_le_iff` — characterizing root multiplicity via derivative vanishing

Factor ρ̃ similarly:
```
-- ρ̃ has simple root at 1 (from rhoCRev_one_eq_zero + rhoCDeriv ≠ 0)
let R_poly := ρ_poly /ₘ (Polynomial.X - 1)
-- Then ρ_poly = (X - 1) * R_poly  (by mul_divByMonic_cancel from root)
-- R_poly.eval 1 = ρ̃'(1) ≠ 0
```

Define the cancelled function:
```
let Gt_cancelled : ℂ → ℂ := fun w =>
  (w - 1) * P_cancelled.eval w / (2 * R_poly.eval w)
```

where `P_cancelled = P_poly /ₘ (X - 1)^2`.

This function is:
- A ratio of polynomial functions with R_poly.eval nonzero on closedBall(0,1) ∖ {1} (from `rhoCRev_ne_zero_of_norm_lt_one` and A-stability boundary argument)
- Actually, R_poly.eval is nonzero on the *entire closed ball* (since ρ̃ has a simple zero at 1, R̃(1) ≠ 0, and ρ̃ has no other zeros in the closed ball)
- Therefore Gt_cancelled is polynomial/polynomial with nonzero denominator: continuous and differentiable everywhere on closedBall(0,1)

### Strategy B: Use the Removable Singularity Theorem (Shorter but harder)

Mathlib has `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`:
> If f is differentiable on a punctured neighborhood of c and continuous at c, then f is analytic at c.

You already have:
- `DifferentiableOn ℂ Gt (Metric.ball 0 1)` — proved at line 1144–1173
- Need: `ContinuousAt Gt 1`

To show `ContinuousAt Gt 1`, you'd use `Filter.Tendsto` and show `Gt w → 0` as `w → 1`. This is the L'Hôpital argument (triple zero / double zero → 0). But proving this limit in Lean is essentially the same work as Strategy A.

**Verdict: Strategy A is more mechanical and better suited to Lean.**

### Strategy C: Use `MeromorphicAt` (Most elegant)

The function `w ↦ σ̃(w)/ρ̃(w) - (w+1)/(2(1-w))` is meromorphic at w=1 (ratio of polynomials). Use:
- `MeromorphicAt` — definition: ∃ n, AnalyticAt ℂ (fun z => (z - 1)^n • f z) 1
- `MeromorphicAt.analyticAt` — meromorphic + continuous at point → analytic

The meromorphic part is automatic (rational function of polynomials). For continuity, you still need the limit, which brings you back to Strategy A.

---

## Part 3: Relevant Mathlib Lemmas

### Polynomial factorization (critical path)
- `Polynomial.dvd_iff_isRoot` : `(X - C a) ∣ p ↔ p.IsRoot a`
- `Polynomial.pow_mul_divByMonic_rootMultiplicity_eq` : `(X - C a)^n * (p /ₘ (X - C a)^n) = p` where n = rootMultiplicity
- `Polynomial.mul_divByMonic_eq_iff_isRoot` : `(X - C a) * (p /ₘ (X - C a)) = p ↔ p.IsRoot a`
- `Polynomial.rootMultiplicity_mul` : multiplicativity of root multiplicity
- `Polynomial.eval_iterate_derivative_rootMultiplicity` : iterated derivative at root

### Polynomial differentiability/continuity
- `Polynomial.differentiable` : `Differentiable ℂ (fun x => eval x p)` — polynomials are globally differentiable
- `Polynomial.continuous_aeval` : `Continuous (fun x => aeval x p)` — polynomials are continuous

### Rational function differentiability
- `DifferentiableAt.div` : quotient of differentiable functions (nonzero denominator)
- `ContinuousAt.div` : quotient of continuous functions (nonzero denominator)
- `DifferentiableOn.div` : on a set

### DiffContOnCl construction
- `DiffContOnCl.mk` : construct from `DifferentiableOn` + `ContinuousOn` on closure
- `Differentiable.diffContOnCl` : globally differentiable → DiffContOnCl on any set
- `DifferentiableOn.diffContOnCl_ball` : if differentiable on open set containing closedBall

### HasDerivAt for quotients
- `HasDerivAt.div` : `HasDerivAt f f' x → HasDerivAt g g' x → g x ≠ 0 → HasDerivAt (f/g) ((f'*g x - f x*g')/g x^2) x`
- `Polynomial.hasDerivAt` : `HasDerivAt (fun x => p.eval x) (p.derivative.eval x) x`

### Maximum principle (already used)
- `Complex.norm_le_of_forall_mem_frontier_norm_le` — you already have this wrapped as `re_nonneg_of_frontier_re_nonneg`

---

## Part 4: Concrete Implementation Plan

### Step 1: Prove the order conditions for P(w) at w=1

You need P(1) = P'(1) = P''(1) = 0 where P(w) = 2σ̃(w)(w-1) + ρ̃(w)(w+1).

**P(1) = 0**: Already essentially `modifiedNumeratorC_one` composed with the reversed polynomial identity at w=1.

**P'(1) = 0**: Differentiate P = 2σ̃(w-1) + ρ̃(w+1):
  P'(w) = 2σ̃'(w)(w-1) + 2σ̃(w) + ρ̃'(w)(w+1) + ρ̃(w)
  P'(1) = 2σ̃(1) + ρ̃'(1)·2 + ρ̃(1) = 2σ(1) + 2ρ̃'(1)

From the order ≥ 2 condition (C₂: ∑j²αⱼ = 2∑jβⱼ), this equals 0. You'll need to prove the C₂ identity for the reversed polynomials. The key relationship: ρ̃'(1) = ∑ j·α_{s-j} = (by substituting k=s-j) ∑ (s-k)·αₖ = s·∑αₖ - ∑k·αₖ = -∑k·αₖ = -ρ'(1) = -σ(1). So P'(1) = 2σ(1) + 2(-σ(1)) = 0. ✓

**P''(1) = 0**: Similar but uses C₃. Work this out on paper first.

### Step 2: Factor P and ρ̃ as Polynomial ℂ

Option A (simplest — avoid `Polynomial` entirely):

Instead of working with `Polynomial ℂ`, define the cancelled form **directly as a function** and prove the algebraic identity:

```lean
-- Define: for w ≠ 1, Gt(w) = σ̃(w)/ρ̃(w) - (w+1)/(2(1-w))
-- The combined fraction has numerator P(w) = 2σ̃(w)(w-1) + ρ̃(w)(w+1)
-- and denominator D(w) = 2ρ̃(w)(w-1).
--
-- Key identity: P(w) = (w-1)² · P₂(w) where P₂ is a polynomial.
-- (This uses P(1) = P'(1) = 0, which come from C₀ and C₁ of the reversed polynomials.)
-- Actually, from order ≥ 3, P(w) = (w-1)³ · Q(w).
-- And D(w) = 2(w-1)²R̃(w) since ρ̃(w) = (w-1)R̃(w).
-- So Gt(w) = (w-1)Q(w) / (2R̃(w)).
```

To avoid `Polynomial ℂ`, use the *functional* Taylor expansion approach:

```lean
-- For a polynomial p with p(1) = 0, define p₁(w) = p(w)/(w-1) as:
noncomputable def divByLinear (p : ℂ → ℂ) : ℂ → ℂ := fun w =>
  if w = 1 then 0 else p w / (w - 1)
```

But this re-introduces the piecewise definition problem. So you really should use `Polynomial ℂ`.

Option B (recommended):

Actually construct ρ̃, σ̃ as `Polynomial ℂ` objects and use `divByMonic`:

```lean
-- Construct ρ_rev_poly : Polynomial ℂ
let ρ_rev_poly : Polynomial ℂ := ∑ j : Fin (s+1),
  Polynomial.C (↑(m.α (Fin.rev j)) : ℂ) * Polynomial.X ^ (j : ℕ)

-- Show ρ_rev_poly.eval w = m.rhoCRev w (for all w)
-- This is definitional modulo unfolding.

-- Show ρ_rev_poly.IsRoot 1 (from rhoCRev_one_eq_zero)
-- Factor: ρ_rev_poly = (X - 1) * R_poly  where R_poly = ρ_rev_poly /ₘ (X - C 1)
-- Then R_poly.eval 1 ≠ 0 (from rhoCDeriv condition)

-- Similarly for P_poly: show rootMultiplicity 1 P_poly ≥ 3
-- Factor: P_poly = (X - 1)^3 * Q_poly
```

### Step 3: Prove `continuousOn_Gtilde_closedBall`

Once you have the cancelled form `(w-1)·Q(w)/(2·R̃(w))`:
- Numerator `(w-1)·Q(w)` is a polynomial → continuous everywhere
- Denominator `2·R̃(w)` is a polynomial → continuous everywhere
- Denominator is nonzero on closedBall(0,1):
  - R̃(1) = ρ̃'(1) ≠ 0 (from `hρ_simple` and `rhoCRev_one_eq_zero` + derivative relationship)
  - For w ≠ 1 in closedBall: R̃(w) = ρ̃(w)/(w-1), and ρ̃(w) ≠ 0 for |w| < 1 (from `rhoCRev_ne_zero_of_norm_lt_one`). On the boundary |w| = 1 with w ≠ 1: ρ̃(w) ≠ 0 iff ρ(w⁻¹) ≠ 0. Since |w⁻¹| = 1 and w⁻¹ ≠ 1, and ρ has no unit-circle roots other than 1 (from A-stability: if ρ(ζ) = 0 and |ζ| = 1, then ζ is a root of the stability polynomial for z = 0, but zero-stability only guarantees simple root at ζ = 1... **WAIT: this is the textbook's implicit assumption that ρ has no other unit-circle roots.**

  **CRITICAL ISSUE**: The proof requires ρ̃(w) ≠ 0 for |w| = 1, w ≠ 1. This means ρ(ζ) ≠ 0 for |ζ| = 1, ζ ≠ 1. This is NOT implied by A-stability alone! A-stability says that roots of ρ(ζ) - zσ(ζ) are in |ζ| ≤ 1 for Re(z) ≤ 0. At z = 0 this gives roots of ρ in |ζ| ≤ 1, but there could be other unit-circle roots.

  **Resolution**: Zero-stability (`hρ_simple : m.rhoCDeriv 1 ≠ 0`) gives a simple root at 1, but we also need the root condition. However, looking more carefully:

  For the *boundary* Re(Gt) ≥ 0 argument (part (c) of the construction), the code at lines 1178–1204 handles w ∈ sphere(0,1) with w ≠ 1 by using `E_nonneg_re_unit_circle`, which requires `m.rhoC z⁻¹ ≠ 0` and handles the case `m.rhoC z⁻¹ = 0` separately (Re = 0 ≥ 0). So the *boundary non-negativity* is fine even if ρ has other unit-circle roots.

  For *continuity* and *DiffContOnCl*, the issue is: does Gt extend continuously to unit-circle points where ρ̃(w) = 0 (i.e., where ρ(w⁻¹) = 0, w ≠ 1)? If ρ̃(w₀) = 0 for some |w₀| = 1, then σ̃(w₀)/ρ̃(w₀) is undefined, and (w₀+1)/(2(1-w₀)) is finite (assuming w₀ ≠ 1), so Gt(w₀) is undefined.

  **THIS IS THE REAL BLOCKER FROM CYCLE 24**: "textbook proof implicitly assumes ρ has no unit-circle roots except ζ=1."

  **Solution approaches**:

  a) **Add the hypothesis**: The cleanest fix is to add a hypothesis that ρ has no other unit-circle roots, or equivalently that the method is "regular" in the sense of Iserles. For the textbook's purposes, this is fine because the Dahlquist barrier is about convergent methods, which are zero-stable, which means all roots of ρ on the unit circle are simple — but they can still exist!

  b) **Weaken DiffContOnCl**: Instead of requiring DiffContOnCl on all of ball(0,1), only require it on a slightly smaller ball or on ball(0,1) minus the other unit-circle roots of ρ. But this breaks the minimum principle application.

  c) **Use the stronger zero-stability condition**: The standard root condition for convergent methods says all roots of ρ satisfy |ζ| ≤ 1, and those with |ζ| = 1 are simple. If ζ₀ is a simple root of ρ on the unit circle with ζ₀ ≠ 1, then σ(ζ₀)/ρ(ζ₀) has a simple pole, and (ζ₀+1)/(2(ζ₀-1)) is finite. So Gt has a simple pole at w₀ = ζ₀⁻¹ on the unit circle. This means Gt is NOT continuous on the closed ball, so DiffContOnCl fails.

  **Therefore**: The proof as stated requires either (i) ρ has no unit-circle roots other than 1, or (ii) a modified argument that avoids DiffContOnCl on the full closed ball.

  **The correct resolution** is approach (ii): use the fact that Re(Gt) ≥ 0 *in the distributional/boundary limit sense* via the Poisson integral formula (which Mathlib doesn't have), OR:

  **BEST RESOLUTION**: Observe that if ρ(ζ₀) = 0 for some ζ₀ on the unit circle with ζ₀ ≠ 1, then because the method is A-stable, σ(ζ₀) must also be 0 (otherwise Re(σ/ρ) would blow up, contradicting the A-stability non-negativity condition). So σ̃/ρ̃ has removable singularities at all unit-circle roots of ρ̃ other than 1. This works! Specifically:

  If ρ̃(w₀) = 0 with |w₀| = 1, w₀ ≠ 1:
  - ρ(w₀⁻¹) = 0 with |w₀⁻¹| = 1
  - By A-stability, ∀ε > 0, Re(σ(ζ)/ρ(ζ)) ≥ 0 for ζ near w₀⁻¹ with |ζ| > 1 (or rather, for all ζ on the unit circle with ρ(ζ) ≠ 0)
  - The cross-energy `Re(σ·conj(ρ)) ≥ 0` on the unit circle shows that σ and ρ cannot have "opposite" behavior
  - Actually, the argument is: if ρ has a simple zero at ζ₀ (from zero-stability) and σ(ζ₀) ≠ 0, then σ/ρ has a simple pole at ζ₀ on the unit circle. But Re(σ/ρ) ≥ 0 at nearby points on the unit circle, and a simple pole on the circle would make Re(σ/ρ) oscillate ±∞, contradiction. So σ(ζ₀) = 0.
  - Therefore σ̃(w₀) = 0 too, and σ̃/ρ̃ has a removable singularity.

  **Even better**: We don't actually need σ̃/ρ̃ to be continuous at other unit-circle roots, because the proof only needs DiffContOnCl on **ball(0,1)** (open ball), and ContinuousOn on **closure(ball(0,1)) = closedBall(0,1)**. The sphere is part of the closure. But the DiffContOnCl only requires:
  1. DifferentiableOn on ball(0,1) — already proved, since ρ̃ ≠ 0 on the open ball
  2. ContinuousOn on closedBall(0,1)

  For ContinuousOn on the closedBall, we need Gt to be continuous at every point of closedBall. At unit-circle points w₀ where ρ̃(w₀) = 0: we need Gt(w₀) to be well-defined and the function to be continuous there. This requires the cancelled form.

  **Simplification**: For the cancelled form `(w-1)Q(w)/(2R̃(w))`, we need R̃(w) ≠ 0 on the closed ball. R̃ = ρ̃/(w-1), so R̃(w₀) = 0 iff ρ̃(w₀) = 0 and w₀ ≠ 1. But wait — R̃ is defined as a polynomial (ρ̃ divided by (X-1) in the polynomial ring), so R̃(w₀) = 0 iff (w₀ - 1) | R̃ iff (w₀ - 1)² | ρ̃. Since ρ̃ has only simple roots on the unit circle (zero-stability), ρ̃ cannot have (w₀-1)² as a factor. So R̃ might still have zeros at other unit-circle roots of ρ̃.

  Hmm, R̃(w₀) = ρ̃(w₀)/(w₀ - 1) as a limit (or polynomial quotient). If ρ̃(w₀) = 0 and w₀ ≠ 1, then indeed R̃(w₀) could be zero (R̃ = ρ̃ /ₘ (X - 1), and ρ̃ has root at w₀, so R̃ has root at w₀).

  **Revised approach**: Include all the (w-1) factors from P in the cancellation. Since ρ̃(w) = (w-1)R̃(w) and P has triple zero at w=1:

  ```
  Gt = P/(2ρ̃(w-1)) = P/[2(w-1)²R̃]
  ```

  Factor P = (w-1)³ · Q, so Gt = (w-1)Q/(2R̃). Now R̃ might have roots on the unit circle. But we can *further* cancel: at each unit-circle root w₀ of R̃ (i.e., each root of ρ̃ other than 1), σ̃ also vanishes there (by the A-stability argument above), so P(w₀) = 2σ̃(w₀)(w₀-1) + ρ̃(w₀)(w₀+1) = 0, and P has at least as many roots at w₀ as ρ̃ does. So (w-1)Q/(2R̃) has removable singularities at those points too.

  **Cleanest path**: Forget about trying to show R̃ ≠ 0 everywhere. Instead, use the analytic removable singularity theorem: the function Gt is meromorphic on ball(0,1) (ratio of polynomials, with ρ̃ ≠ 0 on ball minus 1, and removable at 1 by the triple/double zero). Actually, ρ̃ IS nonzero on the entire open ball (from `rhoCRev_ne_zero_of_norm_lt_one`), so σ̃/ρ̃ is analytic on ball(0,1), and (w+1)/(2(1-w)) is analytic on ball(0,1) (since w=1 is on the boundary, not inside). Wait — w=1 has |w|=1, so it's NOT in ball(0,1). So the denominator 1-w ≠ 0 for all w ∈ ball(0,1).

  **CONCLUSION**: On ball(0,1), BOTH ρ̃(w) ≠ 0 (proved!) AND 1-w ≠ 0 (trivially). So Gt = σ̃/ρ̃ - (w+1)/(2(1-w)) is ALREADY a ratio of analytic functions with nonzero denominators on ball(0,1). It's analytic on ball(0,1).

  The only issue is continuity on the **boundary** (closedBall). But you don't need ContinuousOn on all of closedBall for DiffContOnCl! Wait, yes you do — that's the definition: DiffContOnCl = DifferentiableOn on U + ContinuousOn on closure(U).

  **THE BREAKTHROUGH**: You don't need to prove ContinuousOn on the full closedBall. You only need it on closure(ball(0,1)) = closedBall(0,1). At boundary points w with |w| = 1 and w ≠ 1: Gt is defined by the formula (if branch for w ≠ 1). The formula involves σ̃(w)/ρ̃(w) - (w+1)/(2(1-w)). If ρ̃(w) = 0, this is problematic. BUT: the boundary non-negativity (part c) handles this case by defining Gt(w) via the if-else (and Gt is continuous at such w from the interior if the limit exists).

  **FINAL RESOLUTION**: Redefine Gt differently. Instead of using the raw σ̃/ρ̃ formula at w ≠ 1, use the **cancelled polynomial form everywhere**:

  ```lean
  let Gt : ℂ → ℂ := fun w => (w - 1) * Q_poly.eval w / (2 * R_poly.eval w)
  ```

  where Q_poly and R_poly are polynomial quotients. This is continuous and differentiable wherever R_poly ≠ 0. The question is: is R_poly nonzero on closedBall(0,1)?

  Actually, I think the fundamental issue is simpler than I've been making it. Let me reconsider.

  **R̃ = ρ̃ /ₘ (X - 1) as a polynomial**. R̃(w) = 0 for some w ∈ closedBall iff ρ̃ has a root at w ≠ 1 in closedBall, OR ρ̃ has a double root at 1. By zero-stability, ρ has a simple root at 1, so ρ̃ has a simple root at 1 (since ρ̃(1) = ρ(1) = 0 and ρ̃'(1) relates to ρ'(1)). So ρ̃ has no double root at 1, meaning R̃(1) ≠ 0.

  For w ∈ ball(0,1), w ≠ 1: ρ̃(w) ≠ 0 (from `rhoCRev_ne_zero_of_norm_lt_one`), so R̃(w) = ρ̃(w)/(w-1) ≠ 0.

  For w on sphere(0,1), w ≠ 1: ρ̃(w) might be 0. In that case R̃(w) = ρ̃(w)/(w-1) = 0/(w-1) = 0. Wait, no. R̃ is a polynomial, not the pointwise quotient. R̃ is `ρ_poly /ₘ (X - C 1)`, which is well-defined as a polynomial. If ρ̃ = (X-1) · R̃ as polynomials, then at any point w: ρ̃(w) = (w-1) · R̃(w). If ρ̃(w₀) = 0 and w₀ ≠ 1, then R̃(w₀) = 0.

  So R̃ might have zeros on the unit circle. **To avoid this**, you'd need to show that ρ has no roots on the unit circle other than 1. This is NOT given by zero-stability or A-stability in general.

  **ALTERNATIVE: Avoid the closedBall boundary entirely.**

  Key observation: `re_nonneg_of_frontier_re_nonneg` needs `DiffContOnCl ℂ Gt U` where U = ball(0, r) for some r slightly bigger than 1, IF Gt is analytic on a region containing closedBall(0,1). But Gt may have poles on the unit circle.

  **ACTUAL BEST APPROACH**: Use DiffContOnCl on ball(0, 1) and the existing proof structure. The issue is: how to prove ContinuousOn on closedBall(0,1)?

  For the cancelled form `(w-1)Q(w)/(2R̃(w))`, if R̃ has zeros on sphere(0,1), then ContinuousOn fails at those points (Gt would have 0/0 form). BUT: P and D both vanish at those points (since P has the factor ρ̃), so it's *still* a removable singularity.

  **Practical solution: keep cancelling.** Factor out ALL common factors of the numerator polynomial `(w-1)Q` and the denominator polynomial `2R̃`. Since both are polynomials over ℂ (algebraically closed), we can write them as `(w-1)Q = c₁ · ∏(w - rᵢ)` and `R̃ = c₂ · ∏(w - sⱼ)`. Any common root can be cancelled. The resulting ratio has no common roots, hence the denominator is nonzero wherever the original function was finite.

  But this is getting very complicated for Lean.

  **PRAGMATIC SOLUTION: Use `ContinuousOn` of the original piecewise Gt by proving the limit exists at w=1.**

  For boundary points w with |w| = 1 and w ≠ 1: Gt is given by the formula, which is continuous as long as ρ̃(w) ≠ 0 and 1-w ≠ 0. If ρ̃(w₀) = 0 for some w₀ on the unit circle with w₀ ≠ 1, then Gt is undefined at w₀ (the if-else gives the formula, which divides by zero).

  **BUT WAIT**: Look at the definition of Gt at line 1141-1142:
  ```lean
  let Gt : ℂ → ℂ := fun w =>
    if w = 1 then 0 else σ_rev w / ρ_rev w - (w + 1) / (2 * (1 - w))
  ```

  If ρ_rev(w₀) = 0 for w₀ ≠ 1, then `σ_rev w₀ / ρ_rev w₀` = `σ_rev w₀ / 0` which in Lean is `0` (division by zero gives 0 in Lean!). And `(w₀ + 1) / (2 * (1 - w₀))` is well-defined since w₀ ≠ 1. So Gt(w₀) = 0 - (w₀+1)/(2(1-w₀)). This is a *specific* value, just not the "right" one mathematically.

  So in Lean, Gt is actually well-defined everywhere (division by zero = 0). The question is just whether it's continuous.

  **For ContinuousOn**: At points where ρ̃ ≠ 0 and w ≠ 1, the formula is continuous. At w = 1, you need to show the limit of the formula is 0. At other points w₀ where ρ̃(w₀) = 0 (on the boundary), you'd need to show the limit of the formula as w → w₀ equals 0 - (w₀+1)/(2(1-w₀)) = -(w₀+1)/(2(1-w₀)). This should follow from the continuity of σ̃/ρ̃ * ... actually, σ̃/ρ̃ → 0/0 → 0 in Lean's junk-value convention. In real analysis σ̃/ρ̃ might go to ∞. So the ContinuousOn proof would fail at such boundary points.

  **THEREFORE**: If there are other unit-circle roots of ρ̃, the current definition of Gt does NOT give a continuous function on closedBall. The proof needs modification.

  **TWO WAYS FORWARD**:

  1. **Add hypothesis**: `∀ w ∈ Metric.sphere 0 1, w ≠ 1 → m.rhoCRev w ≠ 0` (no other unit-circle roots). This follows from the root condition of zero-stability: roots on the unit circle must be simple roots of ρ. But A-stability for z=0 gives ρ's roots in |ζ| ≤ 1. Combined with zero-stability's "simple root at 1", we need the *full* root condition: all roots of ρ on the unit circle are simple. This IS part of zero-stability, but it doesn't prevent other simple roots. So this hypothesis is genuinely additional. **However**: for methods that are both A-stable AND zero-stable, having another root ζ₀ on the unit circle with ρ(ζ₀) = 0 and σ(ζ₀) ≠ 0 would give |σ(ζ₀)/ρ(ζ₀)| = ∞, contradicting the stability function being bounded. More carefully: A-stability says for every z with Re(z) ≤ 0, all roots of ρ - zσ have |ζ| ≤ 1. At z = 0 this just says roots of ρ are in the disk. But at z → 0⁻ (negative real), the perturbed roots ζ(z) satisfy ρ(ζ) = zσ(ζ), so ζ ≈ ζ₀ + z·σ(ζ₀)/ρ'(ζ₀) + ... If σ(ζ₀) ≠ 0, these perturbed roots exist and move. The constraint |ζ(z)| ≤ 1 for all Re(z) ≤ 0 requires the root to stay in the disk. Since ζ₀ is on the boundary, the derivative condition gives Re(dζ/dz) ≤ 0 in the outward direction, which constrains σ(ζ₀)/ρ'(ζ₀). This is consistent with σ(ζ₀) ≠ 0. So we cannot prove ρ has no other unit-circle roots from A-stability alone.

  2. **Shrink the ball**: Work with ball(0, r) for r < 1 slightly less than 1. Then closedBall(0,r) ⊂ ball(0,1), and ρ̃ ≠ 0 on closedBall(0,r). The minimum principle applies. Then let r → 1 at the end. This works! The argument:
     - For r < 1: Gt is analytic on ball(0,r) and continuous on closedBall(0,r) (no singularities there, since ρ̃ ≠ 0 in ball(0,1) and w ≠ 1 in closedBall(0,r) if r < 1). So DiffContOnCl ✓.
     - Re(Gt) ≥ 0 on sphere(0,r): Need to show this. By the maximum principle applied to the *entire* ball(0,1), we'd need... wait, this is circular.

     Actually, this doesn't work directly because you don't have Re(Gt) ≥ 0 on sphere(0,r) for r < 1. You only know it on sphere(0,1). So the minimum principle on ball(0,r) doesn't help.

  3. **Use the Poisson integral representation**: Not available in Mathlib.

  4. **Redefine Gt on the boundary**: At boundary points where ρ̃ = 0, define Gt to be the correct limit value (the cancelled form). This means a more complex piecewise definition. The cancelled form value at such points is 0 (since both σ̃ and ρ̃ vanish, and (w+1)/(2(1-w)) has a finite value, but σ̃/ρ̃ has a limit). Actually, if both σ̃ and ρ̃ vanish at w₀, then σ̃(w)/ρ̃(w) → σ̃'(w₀)/ρ̃'(w₀) by L'Hôpital (if simple zeros). So the limit of Gt is σ̃'(w₀)/ρ̃'(w₀) - (w₀+1)/(2(1-w₀)).

  **SIMPLEST FIX**: Prove that if ρ̃(w₀) = 0 for |w₀| = 1, w₀ ≠ 1, then σ̃(w₀) = 0 too, AND redefine Gt at those points using the cancelled form. Then prove ContinuousOn of the modified Gt.

  This is getting complex. Let me propose the most practical path.

---

## Part 5: Recommended Approach (Minimal Changes)

### For `continuousOn_Gtilde_closedBall` (the harder sorry):

**Step 1**: Prove σ̃(w₀) = 0 whenever ρ̃(w₀) = 0 for |w₀| = 1 (from A-stability + cross-energy non-negativity).

**Step 2**: Build the polynomial P(w) = 2σ̃(w)(w-1) + ρ̃(w)(w+1) as `Polynomial ℂ`. Show P(1) = 0 and P'(1) = 0 (from order ≥ 2). This gives P = (X-1)²·P₂ for some polynomial P₂.

**Step 3**: Similarly ρ̃ = (X-1)·R̃. So Gt = (X-1)²P₂ / [2(X-1)²R̃] = P₂/(2R̃). But this only requires dividing the (w-1)² factors. Then Gt = P₂(w)/(2R̃(w)) wherever R̃(w) ≠ 0.

Wait, that's only (w-1)²/(w-1)² = 1 power cancelled if we have P = (w-1)²P₂ and D = 2(w-1)²R̃. Then Gt = P₂/(2R̃), which is analytic wherever R̃ ≠ 0. At w=1: Gt(1) = P₂(1)/(2R̃(1)). We need this to be 0 (to match the piecewise definition). From order ≥ 3: P has a triple zero at 1, so P₂(1) = 0. Therefore Gt(1) = 0. ✓

At other boundary roots of ρ̃: R̃(w₀) = 0. We still need P₂(w₀) = 0 for the ratio to extend continuously. P₂ = P/(X-1)². P(w₀) = 2σ̃(w₀)(w₀-1) + ρ̃(w₀)(w₀+1) = 0 + 0 = 0 (since both σ̃ and ρ̃ vanish). So (X-1) | P, which we already knew. Does (w₀ - something) | P₂? Not obvious without more work.

**ACTUALLY THE CLEANEST APPROACH**: Prove everything on ball(0,1) only (not the closure), and handle the boundary via the existing boundary non-negativity proof which already works.

Look at the structure: `re_nonneg_of_frontier_re_nonneg` takes `DiffContOnCl ℂ f U`. This requires ContinuousOn on closure(U). But the theorem is called with U = ball(0,1), and the proof already handles boundary non-negativity separately (lines 1178–1204). So we truly need ContinuousOn on closedBall(0,1).

**PRAGMATIC APPROACH FOR LEAN**: Factor the problem differently. Instead of trying to make one function work on all of closedBall, do:

1. Show `Gt` is differentiable on ball(0,1) — ALREADY DONE (lines 1146–1173).
2. Show `Gt` is continuous on ball(0,1) — follows from differentiability.
3. For the boundary: use `DiffContOnCl.mk_ball` which needs `ContinuousOn Gt (closedBall 0 1)`. The key issue.

**FOR THE LEAN PROOF, HERE IS THE ACTUAL MINIMAL PATH**:

The function `Gt` as currently defined (line 1141-1142) satisfies:
- `w ∈ ball(0,1)` implies `w ≠ 1` (since ‖1‖ = 1 ≥ 1), so `Gt(w) = σ̃(w)/ρ̃(w) - (w+1)/(2(1-w))`.
- This is a ratio of continuous functions with nonzero denominators on ball(0,1).
- It's continuous on ball(0,1). ✓

For boundary: `w ∈ sphere(0,1)`:
- If `w ≠ 1`: `Gt(w) = σ̃(w)/ρ̃(w) - (w+1)/(2(1-w))` (Lean: if ρ̃(w)=0 then first term = 0 by junk value).
- If `w = 1`: `Gt(w) = 0`.

ContinuousOn at boundary points w₀ with w₀ ≠ 1 and ρ̃(w₀) ≠ 0: the formula is a ratio of continuous functions, continuous. ✓

ContinuousOn at w₀ on boundary with ρ̃(w₀) = 0 (other roots of ρ̃): This is genuinely hard because Gt(w) → σ̃'(w₀)/ρ̃'(w₀) - (w₀+1)/(2(1-w₀)) but Gt(w₀) = 0 - (w₀+1)/(2(1-w₀)) in Lean. These are different! So Gt is NOT continuous at such points.

**THEREFORE**: Either redefine Gt, or prove ρ̃ has no other roots on sphere(0,1).

### To prove ρ̃ has no other unit-circle roots (if possible):

A-stability says: for every z with Re(z) ≤ 0, all roots of ρ(ζ) - zσ(ζ) satisfy |ζ| ≤ 1.

Suppose ρ(ζ₀) = 0 with |ζ₀| = 1, ζ₀ ≠ 1. Can we derive a contradiction?

At z = 0: ρ(ζ₀) = 0 ✓ (no contradiction).
At z = -ε (small): ρ(ζ) + εσ(ζ) = 0 has a root near ζ₀. By implicit function theorem: ζ(ε) ≈ ζ₀ - ε·σ(ζ₀)/ρ'(ζ₀). For |ζ(ε)| ≤ 1, we need d|ζ|²/dε ≤ 0 at ε = 0. This gives Re(ζ₀·conj(σ(ζ₀)/ρ'(ζ₀))) ≤ 0. This is a constraint but not a contradiction.

So we CANNOT prove ρ has no other unit-circle roots from A-stability.

### Therefore: REDEFINE Gt

**Define Gt using the polynomial cancelled form**:

```lean
-- P₂ = P /ₘ (X - 1)² where P = 2σ̃(X-1) + ρ̃(X+1)
-- R̃ = ρ̃ /ₘ (X - 1)
-- Gt(w) = P₂(w) / (2 · R̃(w))   if R̃(w) ≠ 0
-- Gt(w) = 0                       if R̃(w) = 0 (junk case, but Lean handles it)
```

Actually in Lean, just define:
```lean
let Gt : ℂ → ℂ := fun w => P₂_poly.eval w / (2 * R_poly.eval w)
```

This is well-defined everywhere (Lean gives 0 when denominator = 0). It equals the original formula wherever ρ̃(w) ≠ 0 and w ≠ 1. For the DiffContOnCl proof:

- DifferentiableOn on ball(0,1): P₂_poly.eval is differentiable, 2 * R_poly.eval is differentiable and nonzero on ball(0,1) (since R_poly.eval = ρ̃/(w-1) ≠ 0 there, because ρ̃ ≠ 0 on ball(0,1) and w ≠ 1). ✓
- ContinuousOn on closedBall(0,1): P₂_poly.eval is continuous. 2 * R_poly.eval is continuous. At points where R_poly.eval ≠ 0: ratio is continuous. At points where R_poly.eval = 0: Lean gives Gt = 0 (junk). Need to show this is continuous.

Hmm, if R_poly has roots on the boundary, Gt = P₂/(2R̃) has junk value 0 there, and nearby Gt → P₂(w₀)/(2·0) = ∞ or finite depending on whether P₂(w₀) = 0 too. If P₂(w₀) = 0, then it's 0/0 → 0 in Lean but the limit depends on orders of vanishing. NOT automatically continuous.

**I THINK THE RIGHT ANSWER IS**:

Use `Polynomial.gcd` to cancel all common factors, or better yet, avoid the closedBall issue entirely by:

**APPROACH: Use the Cauchy integral formula instead of the maximum principle.**

The Cauchy integral formula gives: for f analytic on ball(0,1) and continuous on closedBall(0,1):
```
f(w) = (1/2πi) ∮ f(ζ)/(ζ-w) dζ
```

If Re(f(ζ)) ≥ 0 on the circle, then... actually you still need continuity on the boundary.

**FINAL RECOMMENDATION: Add the hypothesis that ρ has no unit-circle roots other than 1, or that ρ̃ ≠ 0 on sphere(0,1) \ {1}.**

This is mathematically natural: the Dahlquist barrier in the textbook applies to methods where ρ has roots only at 1 on the unit circle (which holds for all practical A-stable methods like BDF-1, BDF-2, trapezoidal rule). The textbook proof implicitly assumes this. Adding it as a hypothesis is correct and avoids a massive detour.

Alternatively, derive it from A-stability + zero-stability + order ≥ 3 if possible. But I suspect you can't in general.

**Simplest fix**: add `(hρ_no_other : ∀ w ∈ Metric.sphere (0:ℂ) 1, w ≠ 1 → m.rhoCRev w ≠ 0)` to the hypotheses of `continuousOn_Gtilde_closedBall` and `hasDerivAt_Gtilde_one`, and propagate up to `order_ge_three_not_aStable_core`. Then derive this hypothesis from the `IsZeroStable` definition (which should include the root condition that only ζ=1 is a root on the circle, or more commonly, that the root condition holds).

---

## Part 6: For `hasDerivAt_Gtilde_one` (the other sorry)

This is actually easier once you have the polynomial form. With Gt(w) = P₂(w)/(2R̃(w)):

```lean
-- Gt = P₂/(2R̃) is a ratio of polynomials
-- HasDerivAt is given by the quotient rule:
-- Gt'(w) = (P₂'·2R̃ - P₂·2R̃') / (2R̃)² = (P₂'·R̃ - P₂·R̃') / (2R̃²)
-- At w = 1: Gt'(1) = (P₂'(1)·R̃(1) - P₂(1)·R̃'(1)) / (2R̃(1)²)
--         = (P₂'(1)·R̃(1) - 0) / (2R̃(1)²)    [since P₂(1) = 0 from order ≥ 3]
--         = P₂'(1) / (2R̃(1))
```

Then compute P₂'(1) and R̃(1) from the order conditions:
- R̃(1) = ρ̃'(1) (derivative of ρ̃ at 1, since ρ̃ = (X-1)R̃ → ρ̃'(1) = R̃(1))
- P₂'(1) = P'''(1)/6 (since P = (X-1)²·P₂, so P''' = 2·P₂' + 4(X-1)P₂'' + (X-1)²P₂''', giving P'''(1) = 2P₂'(1)... wait, let me recompute)

Actually: P = (X-1)³·Q (triple zero, not double). So P₂ = (X-1)·Q. Then:
- Gt = (X-1)Q/(2R̃) = P₂/(2R̃) where P₂ = (X-1)Q
- Gt(1) = 0 ✓
- Gt'(1) = ((X-1)Q)'(1)/(2R̃(1)) = (Q(1) + 0)/(2R̃(1)) = Q(1)/(2R̃(1))

And Q(1) = P'''(1)/6 (from P = (X-1)³Q → P'''(1) = 6Q(1)).

P'''(1) can be computed from the order conditions. The result should be -σ(1).
R̃(1) = ρ̃'(1) = -ρ'(1) (from the reversed polynomial derivative identity).

So Gt'(1) = (-σ(1))/(6 · 2 · (-ρ'(1))) = σ(1)/(12ρ'(1)) = 1/12 (since σ(1) = ρ'(1)).

**Lean approach**: Use `HasDerivAt.div` (quotient rule) applied to the polynomial quotient form, then evaluate at w=1.

Key Mathlib lemma: `HasDerivAt.div : HasDerivAt f f' x → HasDerivAt g g' x → g x ≠ 0 → HasDerivAt (f / g) ((f' * g x - f x * g') / g x ^ 2) x`

---

## Part 7: Concrete Tactic Suggestions

### For polynomial factorization:
```lean
-- Show P has root at 1
have hP1 : P_poly.IsRoot 1 := by
  rw [Polynomial.IsRoot]; simp [P_poly]; -- unfold and use modifiedNumeratorC_one

-- Factor out (X - 1)
have hfact : (Polynomial.X - Polynomial.C 1) * (P_poly /ₘ (Polynomial.X - Polynomial.C 1)) = P_poly :=
  (Polynomial.mul_divByMonic_eq_iff_isRoot _).mpr hP1
```

### For HasDerivAt of polynomial eval:
```lean
-- Polynomial.hasDerivAt : HasDerivAt (fun x => p.eval x) (p.derivative.eval x) x
have h := Polynomial.hasDerivAt p (1 : ℂ)
```

### For ContinuousOn of polynomial eval:
```lean
-- Polynomial.continuous_aeval gives continuity
have := (Polynomial.continuous_eval₂ (RingHom.id ℂ) p).continuousOn
```

---

## Summary of Recommendations

1. **Redefine Gt** using the polynomial cancelled form `P₂/(2R̃)` or `(w-1)Q/(2R̃)`. This eliminates the removable singularity at w=1 entirely.

2. **Handle other boundary roots of ρ̃** by either:
   - Adding a hypothesis (simplest), or
   - Proving σ̃ also vanishes there and further cancelling, or
   - Redefining Gt at those points using the limit value

3. **For `hasDerivAt_Gtilde_one`**: Use the quotient rule `HasDerivAt.div` on the polynomial form.

4. **For `continuousOn_Gtilde_closedBall`**: Once Gt is defined as a ratio of polynomials with nonzero denominator on closedBall, use `ContinuousAt.div` + `Polynomial.continuous_eval`.

5. **Key Mathlib lemmas to use**:
   - `Polynomial.mul_divByMonic_eq_iff_isRoot` for factoring out roots
   - `Polynomial.hasDerivAt` for derivatives of polynomial eval
   - `HasDerivAt.div` for quotient rule
   - `DifferentiableOn.div` + `Polynomial.differentiable` for DiffContOnCl
   - `Polynomial.continuous_aeval` for continuity

6. **Consider submitting to Aristotle**: The polynomial factorization + derivative computation is highly algebraic and well-suited to automated provers. Submit the individual sorry lemmas.
