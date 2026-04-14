# Cycle 77 Results

## Worked on
- `sdirk3_stiffDecay` sorry in SDIRK3.lean (was at line ~258)
- `sdirk3_poly_ineq` sorry in SDIRK3.lean (was at line ~247)

## Approach

### sdirk3_stiffDecay (SUCCESS)
Followed the SDIRK2 stiff decay proof template:
1. Added helper lemmas `sdirk3_num_coeff1_abs_lt` and `sdirk3_num_coeff2_abs_lt` proving |1-3λ| < 1 and |1/2-3λ+3λ²| < 1
2. Bounded |N(x)| = |1 + ax + bx²| ≤ 1 + |a||x| + |b|x² < 1 + |x| + x² ≤ 3x² for x ≤ -2
3. Bounded |D(x)| = (1-λx)³ ≥ (λ(-x))³ for x ≤ 0
4. Concluded |R(x)| ≤ 3/(λ³(-x)) → 0 as x → -∞
5. Used `push_cast; ring` for cast arithmetic, `nlinarith` for inequalities

### sdirk3_poly_ineq (BLOCKED)
1. Attempted direct `nlinarith` with cubic identity and squared witnesses — TIMEOUT at 200000 heartbeats
2. Attempted decomposition with pre-computed L-power identities — TIMEOUT
3. Python CAS analysis revealed: x does NOT factor out of |D|²-|N|², the polynomial has ~30 terms after cubic reduction, and the y² coefficient vanishes identically via 3λ²-a²+2b=0
4. Submitted to Aristotle (project 32aa0177-e8ec-4fc8-b5f6-59a6bd161392) — still IN_PROGRESS at 6%

## Result
- **sdirk3_stiffDecay**: SUCCESS — sorry eliminated
- **sdirk3_poly_ineq**: BLOCKED — needs SOS decomposition, Aristotle still working

## Dead ends
- `nlinarith` with any combination of witnesses times out on the degree-6 polynomial inequality
- Polynomial factoring: x doesn't divide |D|²-|N|², so can't simplify by canceling x
- `set L := sdirk3Lambda` + `push_cast; ring` interaction: `set` creates opaque definitions that `push_cast` can't see through; had to use direct references

## Discovery
- The SDIRK2 stiff decay template generalizes cleanly to SDIRK3: same structure (bound numerator degree < denominator degree, use coefficient bounds)
- For degree-6 polynomial inequalities with parametric coefficients, nlinarith needs an explicit SOS decomposition — the search space is too large for the heartbeat budget
- Key identity: 3λ²-a²+2b = 0 (the y² cross-term vanishes identically), which means the diff at x=0 starts at y⁴

## Suggested next approach
1. Check Aristotle result for poly_ineq (project 32aa0177)
2. If Aristotle fails: use an external SOS solver (DSOS/SDSOS in Julia, or SAGE) to find the explicit decomposition, then encode it as `have : diff = f₁² + (-x)·g₁² + ... := by linear_combination ... * hcubic` followed by `linarith [sq_nonneg ...]`
3. Alternative: split into x=0 case (easy: y⁴·c₄ + y⁶·c₆ ≥ 0) and x<0 case (use monotonicity or MVT argument)
