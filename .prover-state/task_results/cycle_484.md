# Cycle 484 Results

## Worked on
Adams–Moulton 12-step scalar convergence chain:
- Extended `OpenMath/AdamsMethods.lean` with `LMM.adamsMoulton12 : LMM 12`
  plus `adamsMoulton12_consistent`, `adamsMoulton12_implicit`,
  `adamsMoulton12_order_thirteen`, and `adamsMoulton12_zeroStable`.
- Built the full quantitative convergence chain in
  `OpenMath/LMMAM12Convergence.lean` mirroring the AM11 scalar chain.

## Approach
1. Added the AM12 method object and four headline lemmas in
   `AdamsMethods.lean` using the rational AM12 coefficients with denominator
   `2615348736000` (Lagrange-integration over `[11, 12]`).
2. Wrote the convergence file in four parts:
   - **Taylor helpers (public)**: `iteratedDeriv_fourteen_bounded_on_Icc`,
     `y_fourteenth_order_taylor_remainder` (`M/14! · r¹⁴`), and
     `derivY_thirteenth_order_taylor_remainder` (`M/13! · r¹³`).
   - **Truncation infrastructure**: `am12Coeff` / `am12ExplicitCoeff` /
     `am12Residual`, `IsAM12Trajectory`, `am12Err` / `am12ErrWindow`,
     `am12_localTruncationError_eq`, `am12_one_step_lipschitz`,
     `am12_one_step_error_bound`, and `am12_one_step_error_pair_bound`
     (slackened from `(703604254357/2615348736000)hL ≤ 1/2` to growth
     `104L` with residual coefficient `2`).
   - **Residual algebra (packed-poly)**: private `am12_yPoly13` and
     `am12_dPoly12` helpers, `am12_residual_alg_identity` parameterized over
     fourteen abstract Taylor witnesses, `am12_residual_bound_alg_identity`,
     `am12_residual_fourteen_term_triangle`, and
     `am12_residual_combine_aux` (`|·| ≤ 39099·Mb·h¹⁴`, exact coefficient
     `414541158076267641095141 / 10602754543180800000 ≈ 39097.50`).
   - **Headline chain**: `am12_pointwise_residual_bound`,
     `am12_local_residual_bound` (`C · h¹⁴`), and
     `am12_global_error_bound` (`exp(104L·T)·ε₀ + K·h¹²` for
     `(N+11)·h ≤ T`).
3. Assembled the global theorem through
   `lmm_error_bound_from_local_truncation` at `p = 12`: weakened the
   `h¹⁴` LTE to `h¹³` (per-step `(2C)·h^(p+1) = (2C)·h¹³`) under the
   `h ≤ 1` ceiling, giving output `h^p = h¹²` after Gronwall.

## Result
SUCCESS — both files compile cleanly (`lake env lean OpenMath/AdamsMethods.lean`
and `lake env lean OpenMath/LMMAM12Convergence.lean`). The headline
`LMM.am12_global_error_bound` is now in tree.

## Dead ends
- Initial attempt at `am12_residual_alg_identity` with `subst h{A..N}; ring`
  on fourteen unpacked witnesses blew up the 200K heartbeat budget. Same
  cycle-482 fix applied here: package the y- and derivative-Taylor sums
  into private `am12_yPoly13` / `am12_dPoly12`, restate the witness
  hypotheses in packed form, and `unfold` before `ring`.
- A first generator pass used the wrong Taylor divisors (`13!` and `12!`)
  and the wrong powers (`h¹³` for the y-witnesses, `h¹²` for the
  derivative-witnesses). The correct shape uses
  `M/14! · r¹⁴` for `y_fourteenth_order_taylor_remainder` and
  `M/13! · r¹³` for `derivY_thirteenth_order_taylor_remainder`.
  Recomputing the residual coefficient with these exact divisors gave
  `414541158076267641095141 / 10602754543180800000 ≈ 39097.50` and
  slack `39099`.
- Tried `(p := 13)` in `lmm_error_bound_from_local_truncation`. The
  lemma expects per-step bound `C · h^(p+1)`, so `p = 13` would need
  per-step `h¹⁴` (without weakening). To produce the headline `h¹²`
  output we use `p = 12` and weaken `h¹⁴` to `h¹³`.

## Discovery
- The packed-polynomial witness pattern from cycle 482 (AM11 vector) and
  cycle 483 (AB12 vector) extends cleanly to fourteen-witness scalar
  identities. The `unfold am12_yPoly13 am12_dPoly12; ring` close keeps
  `am12_residual_alg_identity` well within the 200K heartbeat budget.
- `104 = ceil(2·Σ|β_k|)` is the smallest growth constant compatible
  with the implicit half-factor smallness assumption
  `β₁₂·h·L ≤ 1/2` for AM12.
- AM12 LTE coefficient is roughly 2.79× larger than AM11
  (`14003 → 39099`), tracking the textbook expectation for
  the higher-order Adams–Moulton family.

## Suggested next approach
Mirror cycle 484 in finite-dimensional normed spaces by writing
`OpenMath/LMMAM12VectorConvergence.lean` (vector AM12 trajectory predicate,
fourteenth-order vector Taylor helpers, packed-poly residual identity,
pointwise / local / global vector convergence chain). The scalar work in
this cycle established all numerical constants (`104L`, `39099`, slack
`414541158076267641095141 / 10602754543180800000`); the vector mirror
needs only mirror infrastructure plus the vector Taylor helpers.
