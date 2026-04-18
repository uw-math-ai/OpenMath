# Cycle 118 Results

## Worked on
Order arrow infrastructure (def:355A) and concrete arrow direction theorems (partial thm:355B) in `OpenMath/OrderStars.lean`.

## Approach
1. Added order arrow definitions: `orderWeb`, `IsUpArrowDir`, `IsDownArrowDir`
2. Proved structural properties: mutual exclusivity of up/down arrows, connection to order star regions
3. Proved `mem_orderWeb_zero` (origin on web when R(0)=1)
4. Proved concrete arrow direction instances for three classical methods:
   - **Forward Euler** (R(z)=1+z, p=1, C=1/2>0): down arrows at θ=0 and θ=π
   - **Backward Euler** (R(z)=(1-z)⁻¹, p=1, C=-1/2<0): up arrows at θ=0 and θ=π
   - **Trapezoidal rule** (R(z)=(1+z/2)/(1-z/2), p=2, C=-1/12<0): up arrow at θ=0
5. Key mathematical tools used:
   - `Real.add_one_lt_exp`: exp(t) > 1+t for t≠0
   - `Real.one_sub_lt_exp_neg`: 1-t < exp(-t) for t≠0
   - `Real.exp_bound'` with n=3: Taylor upper bound for the trapezoidal case

## Result
**SUCCESS** — 0 sorry's. All 5 new theorems + 3 new definitions fully proved.

### New definitions added
| Symbol | Description |
|--------|-------------|
| `orderWeb` | Locus where φ(z)=R(z)exp(-z) is real and positive |
| `IsUpArrowDir` | Up-arrow direction at origin (‖φ‖>1 near 0) |
| `IsDownArrowDir` | Down-arrow direction at origin (‖φ‖<1 near 0) |

### New theorems proved
| Symbol | Statement |
|--------|-----------|
| `not_isUpArrowDir_and_isDownArrowDir` | Up and down are mutually exclusive |
| `isUpArrowDir_subset_orderStarPlus` | Up arrows land in 𝒜⁺ |
| `isDownArrowDir_subset_orderStarMinus` | Down arrows land in 𝒜⁻ |
| `mem_orderWeb_zero` | Origin on web when R(0)=1 |
| `forwardEuler_isDownArrowDir_zero` | Forward Euler: θ=0 down arrow |
| `forwardEuler_isDownArrowDir_pi` | Forward Euler: θ=π down arrow |
| `backwardEulerR` (def) + `backwardEulerR_zero` | Backward Euler stability fn |
| `backwardEuler_isUpArrowDir_zero` | Backward Euler: θ=0 up arrow |
| `backwardEuler_isUpArrowDir_pi` | Backward Euler: θ=π up arrow |
| `trapezoidalR` (def) + `trapezoidalR_zero` | Trapezoidal stability fn |
| `trapezoidal_key_ineq` | exp(t) < (2+t)/(2-t) for 0<t≤1/4 |
| `trapezoidal_isUpArrowDir_zero` | Trapezoidal: θ=0 up arrow |

## Dead ends
None — all planned proofs went through cleanly.

## Discovery
- `Real.exp_bound'` with `n=3` is a powerful tool for Padé-type inequalities: it gives `exp(x) ≤ 1 + x + x²/2 + 4x³/18` for `0 ≤ x ≤ 1`, which is tight enough for the trapezoidal inequality.
- The pattern for arrow direction proofs is: (1) simplify the complex norm to real, (2) use `orderStar_norm_eq` or `norm_mul` + `Complex.norm_exp`, (3) reduce to a real inequality, (4) apply exponential bounds.
- For θ=π, use `Complex.exp_pi_mul_I` to get `exp(iπ) = -1`.

## Suggested next approach
1. **General Theorem 355B**: The concrete instances demonstrate the pattern. The general theorem needs the hypothesis `R z = exp z - C * z^(p+1) + g z` with `g = O(z^{p+2})`, which requires Asymptotics API. Consider formalizing the general statement with the asymptotic hypothesis and proving it using the same `exp_bound'` technique.
2. **More arrow directions**: Prove trapezoidal arrows at θ=2π/3 and θ=4π/3, and extend to Gauss-Legendre.
3. **Ehle wedge connections**: Connect arrow directions to A-stability: show that for forward Euler, down arrows at θ=0 and θ=π correctly predict non-A-stability (𝒜⁻ on the real axis near 0 in both directions).
4. **Priority 2/3 from strategy**: Consider Theorem 355F (A-stability criterion via order stars) and rooted tree infrastructure.

## Aristotle jobs
Submitted 3 jobs (will be available for cycle 119):
- `b4baac00`: Forward Euler arrows
- `db97dccf`: Backward Euler arrows
- `e53627ef`: Trapezoidal arrow
