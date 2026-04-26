# Cycle 450 Results

## Worked on
Adams–Bashforth 7-step scalar quantitative convergence chain
(`OpenMath/LMMAB7Convergence.lean`), order-7 explicit LMM mirroring the
AB6 scaffold at the next order.

## Approach
1. Promoted three eighth-order Taylor-remainder helpers to public in
   `OpenMath/LMMAM6Convergence.lean`:
   `iteratedDeriv_eight_bounded_on_Icc`,
   `y_eighth_order_taylor_remainder`,
   `derivY_seventh_order_taylor_remainder`.
2. Added `adamsBashforth7 : LMM 7` definition to `AdamsMethods.lean`
   along with `adamsBashforth7_consistent`, `adamsBashforth7_explicit`,
   `adamsBashforth7_order_seven` (interval_cases over q ∈ {0..6}).
3. Built the new file `OpenMath/LMMAB7Convergence.lean` (~1380 lines)
   following the AB6 scaffold scaled up for 7 history samples and 8
   Taylor remainders. Sign convention flips at the oldest term
   (β₀ = +19087/60480) since AB7 has 7 nontrivial β-coefficients vs
   AB6's 6.
4. Key constants: L¹-norm Σ|β_i| = 2600512/60480 = 40633/945
   (≈ 43); residual coefficient = 159970508328/304819200 ≈ 524.8,
   slacked to 525.
5. Used helper-lemma extraction for the heavy `ring` proofs:
   `ab7_residual_alg_identity` (8-term Taylor decomposition),
   `ab7_residual_bound_alg_identity` (combined coefficient identity),
   `ab7_residual_eight_term_triangle` (chained triangle inequality).

## Result
SUCCESS. All three modified files compile cleanly:
- `lake env lean OpenMath/AdamsMethods.lean` (EXIT 0).
- `lake env lean OpenMath/LMMAM6Convergence.lean` (EXIT 0).
- `lake env lean OpenMath/LMMAB7Convergence.lean` (EXIT 0).
- `lake build OpenMath.LMMAB7Convergence OpenMath.AdamsMethods
  OpenMath.LMMAM6Convergence` succeeds (8033 jobs).

The full convergence chain is sorry-free. Headline theorem is
`ab7_global_error_bound`: for Lipschitz `f` and `C^8` exact solution,
`|y_N − y(t₀+Nh)| ≤ exp((40633/945)·L·T)·ε₀ +
T·exp((40633/945)·L·T)·525·M·h^7` (the residual constant is the
slacked combined coefficient times M).

## Dead ends
- First compile of `LMMAB7Convergence.lean` had two issues:
  1. `linarith [this]` in the `hslack` step at line 944 timed out
     (simp inside linarith hit 200000 heartbeats with 16 `set` vars in
     scope). Fixed by replacing with explicit `mul_assoc` rewrites
     plus `mul_le_mul_of_nonneg_right`.
  2. Kernel `whnf` timeout at the `ab7_pointwise_residual_bound`
     theorem boundary (line 704). Fixed by adding two `clear_value`
     calls — one after the 16 abbreviation `set`s for Taylor-remainder
     pieces, and one after the 8 abbreviation `set`s for A..H. With
     the let-defs erased, the kernel no longer has to whnf-reduce
     them when type-checking the calc block.
- Initial `simp [Fin.val_zero]` / `simp [Fin.val_one]` /
  `simp [Fin.val_two]` at lines 1192/1195/1198 emitted unused-simp-arg
  warnings; replaced with bare `simp`.
- `ring` at line 113 emitted a `Try this: ring_nf` info hint
  (the goal needed normalization but ring's eq-decision was OK
  enough to finish via fallback). Switched to `ring_nf` for a
  clean compile.

## Discovery
- For LMM convergence chains at order ≥ 7, the kernel `whnf` budget
  becomes a real concern. The `clear_value` trick (after `set` to
  introduce abbreviations) erases the let-bindings without losing
  the variable, dramatically reducing kernel WHNF cost. AB6 didn't
  need this; AB7 does because of the extra two abbreviations and
  the larger combined-coefficient identity. Worth using
  preemptively for AM7 / BDF8+ chains.
- `linarith` is fragile when many `set` vars are in scope —
  prefer explicit `mul_assoc` + `mul_le_mul_of_nonneg_right` for the
  slack step rather than letting `linarith` normalize things itself.

## Suggested next approach
- Vector lift of AB7 (mirror cycle 425's AB6 vector lift) — mostly
  mechanical port via `ab7Iter` and `‖·‖` in place of `|·|`.
- Adams–Moulton 7 quantitative convergence (implicit, order 8) —
  the `localTruncationError_leading_bound` template plus the
  predictor–corrector machinery from cycle 446 should apply.
- Continue the BDF tower (BDF3 scalar quantitative), reusing the
  BDF2 blueprint from cycle 449.
