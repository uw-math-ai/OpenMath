# Cycle 104 Results

## Worked on
Theorem 351B (A-Stability Criterion): closed all remaining sorry's in `OpenMath/AStabilityCriterion.lean`.

## Approach
1. **Phase 1**: Verified the file from cycle 103 (necessity direction + sorry-first sufficiency structure) compiled.
2. **Phase 2**: Submitted 5 Aristotle jobs for the remaining sorry's:
   - `isBigO_neg_ratFunc_rhp` (O(exp) growth bound for PhragmenLindelof)
   - `isBoundedUnder_neg_ratFunc_real` (bounded on positive reals)
   - `aStable_of_nonvanishing_and_ePoly_nonneg` (full sufficiency direction)
   - `aStable_with_nonvanishing_iff` (iff characterization)
   - `ePoly_nonneg_of_aStable` helper
3. Incorporated Aristotle results:
   - The **full sufficiency** Aristotle job (`5f59757e`) proved everything self-contained, including both sorry'd lemmas.
   - The standalone **isBoundedUnder** job (`d1ce4502`) also succeeded independently.
   - The standalone **iff** job (`ef6f67c1`) succeeded.
   - Adapted Aristotle's proofs into our file structure, decomposing into helper lemmas:
     - `g_numerator_bound`: upper bound on ‖N(-z)‖
     - `g_denominator_bound`: lower bound on ‖D(-z)‖
     - `g_isBigO_one`: combining bounds to show O(1)
     - `g_bounded_real`: limit-at-infinity argument for IsBoundedUnder

## Result
**SUCCESS** — Theorem 351B is fully formalized with zero sorry's. All theorems verified with only standard axioms (propext, Classical.choice, Quot.sound).

### Theorems proved (all in `OpenMath/AStabilityCriterion.lean`):
- `ePoly` — E-function definition
- `evalImag` — imaginary axis evaluation
- `evalImag_ne_zero_of_poles_rhp` — denominator nonvanishing
- `ePoly_nonneg_of_imag_axis_bound` — pointwise E ≥ 0 from |N/D| ≤ 1
- `ePoly_nonneg_of_aStable` — necessity (explicit nonvanishing)
- `ePoly_nonneg_of_aStable_and_poles_rhp` — necessity (pole-location)
- `norm_div_le_one_of_ePoly_nonneg` — converse pointwise bound
- `diffContOnCl_neg_ratFunc_rhp` — DiffContOnCl for PhragmenLindelof
- `isBigO_neg_ratFunc_rhp` — growth condition
- `isBoundedUnder_neg_ratFunc_real` — bounded on reals
- `aStable_of_nonvanishing_and_ePoly_nonneg` — sufficiency direction
- `aStable_with_nonvanishing_iff` — full iff characterization

## Dead ends
1. **`Polynomial.isBigO_cobounded_of_degree_le`**: Loogle reported it exists but it's NOT in our Mathlib version. Only `Polynomial.isBigO_atTop_of_degree_le` exists (requires `LinearOrder`/`IsStrictOrderedRing` — works for ℝ but not ℂ).
2. **Direct manual proof of isBigO**: Attempted leading coefficient analysis manually but hit API issues with `Nat.sub_ne_zero_of_lt`, `pow_le_pow_right₀` type mismatches, etc.
3. **Pasting Aristotle's isBoundedUnder proof directly**: API mismatches when the standalone proof was pasted into our file (different `open` declarations, name resolution).

## Discovery
- Aristotle excels at self-contained proofs. The full-sufficiency job that proved everything at once was the most useful — it had internal consistency.
- The decomposition into `g_numerator_bound` / `g_denominator_bound` / `g_isBigO_one` keeps each lemma under reasonable heartbeat limits.
- Some Aristotle proofs use `set_option maxHeartbeats 800000`. The `g_bounded_real` lemma (limit-at-infinity for rational functions) is the most expensive — future work should decompose it further.

## Suggested next approach
- Theorem 351B is complete. Move on to the next target in the plan (Theorem 352A or rooted tree infrastructure per strategy).
- The `g_bounded_real` lemma uses 800000 heartbeats — a future cleanup cycle should decompose it into smaller helpers (e.g., extract the tendsto-zero lemma and the limit-quotient lemma separately).
