# Issue: SDIRK3 A-stability polynomial inequality needs SOS decomposition

## Blocker
The polynomial inequality `sdirk3_poly_ineq` (SDIRK3.lean:334) times out with `nlinarith`.
This is the LAST sorry blocking SDIRK3 from being sorry-free.

## Context
Goal: Show |N(z)|² ≤ |D(z)|² for Re(z) ≤ 0, where:
- N(z) = 1 + (1-3λ)z + (1/2-3λ+3λ²)z²  (degree 2 numerator)
- D(z) = (1-λz)³  (degree 3 denominator)
- λ = sdirk3Lambda satisfying 6λ³-18λ²+9λ-1 = 0, λ ∈ (2/5, 1/2)

The inequality is degree 6 in (x, y) with coefficients involving λ up to λ⁶.

## What was tried
1. Direct `nlinarith` with cubic identity + squared witnesses: TIMEOUT at 200000 heartbeats
2. Decomposition into sub-lemmas with pre-computed L-power identities: TIMEOUT
3. Polynomial factoring via Python CAS:
   - Verified that x does NOT factor out of |D|²-|N|²
   - At x=0: diff = y⁴·(-(3λ-1/2)(λ-1/2)) + y⁶·λ⁶ ≥ 0 ✓
   - The y² coefficient in diff(0,y) is exactly 0 (algebraic identity: 3λ²-a²+2b=0)
   - Reducing via cubic gives a polynomial in (x,y,λ,λ²) that's NOT manifestly non-negative

## Mathematical analysis

### Key algebraic identities (proven)
- a = 1-3λ, b = 1/2-3λ+3λ²
- |a| < 1 and |b| < 1 for λ ∈ (2/5, 1/2)  ← proven as `sdirk3_num_coeff1_abs_lt`, `sdirk3_num_coeff2_abs_lt`
- 3λ²-a²+2b = 0  (the y² coefficient in diff(x=0) vanishes identically)
- 3λ⁴-b² = -(3λ-1/2)(λ-1/2) > 0  (y⁴ coefficient after cubic reduction)

### Structure of diff = |D|²-|N|²
After reducing by cubic identity (replacing λ³ = (18λ²-9λ+1)/6):
- diff(0,y) = y⁴·c₄ + y⁶·c₆  where c₄, c₆ > 0 at λ = sdirk3Lambda
- diff(x,y) = x·Q(x,y,λ) + diff(0,y)  where Q is a ~30-term polynomial
- For x ≤ 0: need x·Q ≥ 0 (i.e., Q ≤ 0) AND diff(0,y) ≥ 0

### Why nlinarith fails
The reduced polynomial has ~30 terms in (x, y, λ, λ²). nlinarith must find a
sum-of-squares decomposition of a degree-6 polynomial with parametric coefficients.
This exceeds the 200000 heartbeat budget.

## Possible solutions

### A: Explicit SOS decomposition (most promising)
Find specific polynomials f₁,...,fₖ and g₁,...,gₘ such that:
  diff = Σᵢ fᵢ² + (-x)·Σⱼ gⱼ² + cubic·S
This can be found using an SOS solver (e.g., DSOS/SDSOS in Julia, or SAGE).
The proof then becomes:
```lean
have key : diff = f₁² + ... + (-x)·g₁² + ... := by linear_combination ... * hcubic
linarith [sq_nonneg f₁, ..., mul_nonneg (neg_nonneg.mpr hx) (sq_nonneg g₁), ...]
```

### B: Polyrith (if available with SOS backend)
Try `polyrith` which uses Positivstellensatz certificates.

### C: Break into x=0 and x<0 cases
1. x=0: prove directly (y⁴·c₄ + y⁶·c₆ ≥ 0)
2. x<0: use continuity + compactness argument, or MVT
   (diff is a polynomial, diff(0,y) ≥ 0, and ∂diff/∂x(0,y) = Q(0,y,...) has known sign)

### D: Matrix norm approach
Express |R(z)| ≤ 1 via R(z) = 1 + z·bᵀ(I-zA)⁻¹e and use properties of resolvent.

## Submitted to Aristotle
Project ID: 32aa0177-e8ec-4fc8-b5f6-59a6bd161392 (submitted cycle 77)
