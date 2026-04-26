# Formalization Plan

## Textbook
*A First Course in the Numerical Analysis of Differential Equations* — Arieh Iserles (Cambridge, 2nd edition)

## Status Key
- [x] Formalized (0 sorry)
- [ ] Not started
- [~] In progress

## Chapter 1: Multistep Methods

### 1.1 The Picard–Lindelöf Theorem and Euler Method
- [x] **Definition 110A**: Lipschitz condition in second variable (`OpenMath/PicardLindelof.lean`)
- [x] **Theorem 110C**: Picard–Lindelöf existence and uniqueness (`OpenMath/PicardLindelof.lean`)
  - [x] Uniqueness via Gronwall (`PicardLindelof.unique`)
  - [x] Continuous dependence on initial data (`PicardLindelof.continuous_dependence`)
  - [x] Perturbation bound (`PicardLindelof.perturbation_bound`)
  - [x] Combined exists_unique
  - [x] Existence via bisection induction (`PicardLindelof.exists_solution`)
- [x] **Theorem 212A**: Global truncation error bound for Euler method (`OpenMath/Basic.lean`)
- [x] **Theorem 213A**: Convergence of the Euler method (`OpenMath/EulerConvergence.lean`)
  - Statement: If f is Lipschitz and sufficiently smooth, the Euler method converges with order 1

### 1.2 Multistep Methods
- [x] **Definition**: General linear multistep method infrastructure (`OpenMath/MultistepMethods.lean`); Adams–Bashforth and Adams–Moulton families (`OpenMath/AdamsMethods.lean`)
- [x] **Example**: Adams–Moulton 2-step method — consistency, order 3, implicit, zero-stable (`OpenMath/AdamsMethods.lean`)
- [x] **Adams–Bashforth 3-step**: consistency, order 3, zero-stability, convergence (`OpenMath/AdamsMethods.lean`, `OpenMath/DahlquistEquivalence.lean`)
- [x] **Adams–Moulton 3-step**: consistency, order 4, implicit, zero-stability, convergence (`OpenMath/AdamsMethods.lean`, `OpenMath/DahlquistEquivalence.lean`)
- [x] **Adams–Bashforth 4-step**: consistency, order 4, explicit, zero-stability, convergence (`OpenMath/AdamsMethods.lean`, `OpenMath/DahlquistEquivalence.lean`)
- [x] **Adams–Moulton 4-step**: consistency, order 5, implicit, zero-stability, convergence (`OpenMath/AdamsMethods.lean`, `OpenMath/DahlquistEquivalence.lean`)
- [x] **Adams–Bashforth 5-step**: consistency, order 5, explicit, zero-stability, convergence (`OpenMath/AdamsMethods.lean`, `OpenMath/DahlquistEquivalence.lean`)
- [x] **Adams–Moulton 5-step**: consistency, order 6, implicit, zero-stability, convergence (`OpenMath/AdamsMethods.lean`, `OpenMath/DahlquistEquivalence.lean`)
- [x] **Adams–Bashforth 6-step**: consistency, order 6, explicit, zero-stability, convergence (`OpenMath/AdamsMethods.lean`, `OpenMath/DahlquistEquivalence.lean`)
- [x] **Adams–Moulton 6-step**: consistency, order 7, implicit, zero-stability, convergence (`OpenMath/AdamsMethods.lean`, `OpenMath/DahlquistEquivalence.lean`)
- [x] **Infrastructure**: Adams zero-stability proofs share the reusable characteristic-polynomial helper
  `adams_zeroStable_of_rhoC_pow_mul` (`OpenMath/AdamsMethods.lean`, cycle 389)
- [x] **Error constants**: `LMM.errorConstant`; forward Euler = 1/2, backward Euler = −1/2, trapezoidal = −1/12; AB2 = 5/12, AM2 = −1/24, AB3 = 3/8, AM3 = −19/720, AB4 = 251/720, AM4 = −3/160, AB5 = 95/288, AM5 = −863/60480, AB6 = 19087/60480, AM6 = −275/24192; BDF2 = −2/9, BDF3 = −3/22, BDF4 = −12/125, BDF5 = −10/137, BDF6 = −20/343, BDF7 = −35/726 (computed despite zero-instability) (`OpenMath/MultistepMethods.lean`, `OpenMath/AdamsMethods.lean`, cycles 390–393)
- [x] **Adams error-constant signs**: AB2–AB6 are strictly positive and AM2–AM6 are strictly negative (`OpenMath/AdamsMethods.lean`, cycle 393)
- [x] **Truncation operator**: definition `LMM.truncationOp`, monomial identity `truncationOp_monomial_zero`, linearity, vanishing on order-`p` monomials, converse/iff order-condition packaging, direct truncation-operator sufficient condition on monomials, leading coefficient at `t^(p+1)` equals `(p+1)! · errorConstant p · h^(p+1)` (`OpenMath/LMMTruncationOp.lean`, cycles 394–395; split from `OpenMath/MultistepMethods.lean` in cycle 397)
  - [x] **Polynomial-form truncation operator**: finset-sum linearity `truncationOp_finset_sum`, polynomial-combination identity `truncationOp_polyCombination_zero`, degree-`≤ p` vanishing for order-`p` methods `truncationOp_polyCombination_eq_zero_of_HasOrder`, degree-`p+1` leading-coefficient formula `truncationOp_polyDegSucc_eq_leading_of_HasOrder` (`OpenMath/LMMTruncationOp.lean`, cycle 396; split in cycle 397)
  - [x] **Translation-invariant truncation operator**: `truncationOp_translation` and shifted-polynomial vanishing `truncationOp_polyShift_eq_zero_of_HasOrder` move the order-`p` polynomial vanishing theorem from the origin to evaluation point `t` for polynomials in `(u - t)` (`OpenMath/LMMTruncationOp.lean`, cycle 397)
  - [x] **Translated leading-coefficient identity**: `truncationOp_polyShiftDegSucc_eq_leading_of_HasOrder` — for an order-`p` LMM, the truncation operator at evaluation point `t` on a degree-`p+1` polynomial in `(u - t)` reduces to its leading coefficient times `(p+1)! · errorConstant p · h^(p+1)` (`OpenMath/LMMTruncationOp.lean`, cycle 398)
  - [x] **Polynomial-eval truncation wrappers**: `truncationOp_polynomial_eval_eq_zero_of_HasOrder` and `truncationOp_polynomial_eval_eq_leading_of_HasOrder` bridge the finite-tuple polynomial identities to `Polynomial.eval`/`Polynomial.derivative.eval` at the origin (`OpenMath/LMMTruncationOp.lean`, cycle 399)
  - [x] **Shifted polynomial-eval truncation wrappers**: `truncationOp_polynomial_evalShift_eq_zero_of_HasOrder` and `truncationOp_polynomial_evalShift_eq_leading_of_HasOrder` lift the `Polynomial.eval` wrappers from the origin to evaluation point `t` (`OpenMath/LMMTruncationOp.lean`, cycle 399)
  - [x] **Taylor-polynomial truncation wrappers**: local definition `taylorPoly y t n := ∑ k ∈ range (n+1), C (y k t / k!) * X^k`; degree bound `taylorPoly_natDegree_le`; coefficient formula `taylorPoly_coeff`; `truncationOp_taylorPoly_eq_zero_of_HasOrder` (degree-`p` Taylor polynomial vanishes); headline `truncationOp_taylorPoly_eq_leading_of_HasOrder` — for an order-`p` LMM, the truncation operator at `t` on the degree-`p+1` Taylor polynomial of `y` about `t` equals `y^(p+1)(t) · errorConstant p · h^(p+1)` (the polynomial-side ingredient of Iserles' local truncation error formula) (`OpenMath/LMMTruncationOp.lean`, cycle 400)
  - [x] **Smooth Taylor-remainder bridge**: `taylorPolyOf`, residual decomposition `truncationOp_smooth_eq_taylor_residual`, pointwise value/derivative residual bounds, and `truncationOp_smooth_eq_leading_add_remainder` bound the smooth truncation operator by the Taylor leading term plus a theorem-local `h^(p+2)` remainder constant. The current existential-constant surface is weak because `C` may depend on the fixed `h`; strengthening to a uniform small-`h` estimate remains the next local-error task. (`OpenMath/LMMTruncationOp.lean`, cycle 401)
  - [x] **Uniform local truncation error bridge**: `truncationOp_smooth_local_truncation_error` — for an order-`p` LMM acting on `ContDiff ℝ (p+2) y`, exhibits a uniform `(C, δ)` pair with `δ ≤ δ₀` such that `‖τ(t,h) − y^(p+1)(t) · errorConstant p · h^(p+1)‖ ≤ C · h^(p+2)` for **all** `h ∈ (0, δ]`, with `C` independent of `h`. Auxiliary infrastructure: `taylorWithinEval_eq_taylorPolyOf_eval`, `taylor_remainder_value_bound_uniform`, `taylor_remainder_deriv_bound_uniform`, and the polynomial identity `taylorPolyOf_derivative_eval`. The bridge is packaged via `localTruncationError` (= `truncationOp` applied to `(y, y')`) and `localTruncationError_leading_bound` (Iserles' textbook-form local truncation error statement). (`OpenMath/LMMTruncationOp.lean`, cycle 402)
  - [x] **Exponential horizon Grönwall bridge**: `discrete_gronwall_exp_horizon` specializes the closed-form discrete Grönwall inequality to the textbook finite-horizon shape `e n ≤ exp(L*T) * e 0 + T * exp(L*T) * C * h^p` under `e (n+1) ≤ (1 + h*L) * e n + C*h^(p+1)` and `(n : ℝ) * h ≤ T`; `lmm_error_bound_from_local_truncation` packages the same bound under the LMM/global-error-facing name. (`OpenMath/LMMTruncationOp.lean`, cycle 405)
  - [x] **Forward-Euler scalar convergence chain**: `LMM.forwardEulerIter` (explicit Euler iteration), `LMM.forwardEuler_localTruncationError_eq` (textbook one-step residual = LMM truncation operator), `LMM.forwardEuler_one_step_error_bound` (Lipschitz one-step error recurrence `e(n+1) ≤ (1+hL)·e(n) + |τ_n|`), `LMM.forwardEuler_local_residual_bound` (uniform `|τ_n| ≤ M/2 · h^2` from a `C^3` solution and a uniform `|y''|` bound on the sample interval), and the headline `LMM.forwardEuler_global_error_bound` (`|y_N - y(t₀ + N h)| ≤ T · exp(L T) · M/2 · h` for `0 < h ≤ δ`, `N h ≤ T`) — the textbook scalar-Euler `O(h)` convergence theorem assembled via `lmm_error_bound_from_local_truncation` at `p = 1`. (`OpenMath/LMMTruncationOp.lean`, cycle 406)
  - [x] **Forward-Euler vector convergence chain**: `LMM.forwardEulerIterVec`, `LMM.forwardEulerVec_one_step_error_bound`, private helpers `iteratedDeriv_two_bounded_on_Icc_vec` and `forwardEulerVec_pointwise_residual_bound`, `LMM.forwardEulerVec_local_residual_bound`, and the headline `LMM.forwardEulerVec_global_error_bound` lift the cycle-406 scalar consumer chain to finite-dimensional normed vector spaces, using an interval-integral Taylor residual inequality and the same `lmm_error_bound_from_local_truncation` Grönwall bridge at `p = 1`. (`OpenMath/LMMTruncationOp.lean`, cycle 407)
  - [x] **Adams–Bashforth 2-step scalar convergence chain**: `LMM.ab2Iter` (two starting samples, recurrence `y_{n+2} = y_{n+1} + h(3/2 f_{n+1} − 1/2 f_n)`), `LMM.ab2_localTruncationError_eq` (textbook AB2 one-step residual `y(t+2h) − y(t+h) − h(3/2 y'(t+h) − 1/2 y'(t))` equals the LMM truncation operator), `LMM.ab2_one_step_lipschitz` and `LMM.ab2_one_step_error_bound` (Lipschitz max-norm one-step recurrence `max(eₙ₊₁,eₙ₊₂) ≤ (1+h·2L)·max(eₙ,eₙ₊₁) + |τ_n|`), private helpers `iteratedDeriv_three_bounded_on_Icc`, `y_third_order_taylor_remainder`, `derivY_second_order_taylor_remainder`, `ab2_pointwise_residual_bound` (combined Taylor remainders giving `9/4·M·h³`), `LMM.ab2_local_residual_bound` (uniform `|τ_n| ≤ C·h³`), and the headline `LMM.ab2_global_error_bound` (`|y_N − y(t₀+Nh)| ≤ exp(2L·T)·ε₀ + K·h²` for `(N+1)·h ≤ T`) — the textbook AB2 `O(h²)` convergence theorem assembled via `lmm_error_bound_from_local_truncation` at `p = 2` with effective Lipschitz constant `2L`. (`OpenMath/LMMAB2Convergence.lean`, cycle 408; extracted from `OpenMath/LMMTruncationOp.lean` in cycle 414)
  - [x] **Adams–Bashforth 2-step vector convergence chain**: `LMM.ab2IterVec`, `LMM.ab2VecResidual` + `LMM.ab2Vec_localTruncationError_eq` (textbook vector residual unfolding), `LMM.ab2Vec_one_step_lipschitz` and `LMM.ab2Vec_one_step_error_bound` (max-norm Lipschitz recurrence `max(‖eₙ₊₁‖,‖eₙ₊₂‖) ≤ (1+h·2L)·max(‖eₙ‖,‖eₙ₊₁‖) + ‖τ_n‖`), private helpers `iteratedDeriv_three_bounded_on_Icc_vec`, `derivY_second_order_taylor_remainder_vec`, `y_third_order_taylor_remainder_vec`, `ab2Vec_pointwise_residual_bound` (combined `intervalIntegral` Taylor remainders giving `9/4·M·h³`), `LMM.ab2Vec_local_residual_bound`, and the headline `LMM.ab2Vec_global_error_bound` (`‖y_N − y(t₀+Nh)‖ ≤ exp(2L·T)·ε₀ + K·h²` for `(N+1)·h ≤ T`) — vector mirror of cycle 408 in finite-dimensional normed spaces, assembled via `lmm_error_bound_from_local_truncation` at `p = 2` with effective Lipschitz constant `2L`. (`OpenMath/LMMAB2Convergence.lean`, cycle 410; extracted from `OpenMath/LMMTruncationOp.lean` in cycle 414)
  - [x] **Adams–Moulton 2-step scalar convergence chain**: `LMM.IsAM2Trajectory` (supplied implicit trajectory satisfying `yₙ₊₂ = yₙ₊₁ + h(5/12 fₙ₊₂ + 8/12 fₙ₊₁ − 1/12 fₙ)`), `LMM.am2_localTruncationError_eq`, `LMM.am2_one_step_lipschitz` and `LMM.am2_one_step_error_pair_bound` (implicit max-norm recurrence under `(5/12)hL ≤ 1/2`, slackened to growth `3L` and residual coefficient `2` after division), `LMM.am2_pointwise_residual_bound` and `LMM.am2_local_residual_bound` (`|τ_n| ≤ C·h⁴` from the public AB3 fourth-order Taylor helpers), and the headline `LMM.am2_global_error_bound` (`|y_N − y(t₀+Nh)| ≤ exp(3L·T)·ε₀ + K·h³` for `(N+1)·h ≤ T`) — the textbook AM2 `O(h³)` scalar convergence theorem for supplied implicit trajectories. (`OpenMath/LMMAM2Convergence.lean`, cycle 434)
  - [x] **Adams–Moulton 2-step vector convergence chain**: `LMM.IsAM2TrajectoryVec` (supplied implicit vector trajectory `yₙ₊₂ = yₙ₊₁ + h • ((5/12) • fₙ₊₂ + (8/12) • fₙ₊₁ − (1/12) • fₙ)`), `LMM.am2Vec_localTruncationError_eq`, `LMM.am2Vec_one_step_lipschitz` and `LMM.am2Vec_one_step_error_pair_bound` (implicit max-norm recurrence under `(5/12)hL ≤ 1/2`, slackened to growth `3L` and residual coefficient `2` after division), `LMM.am2Vec_pointwise_residual_bound` and `LMM.am2Vec_local_residual_bound` (`‖τ_n‖ ≤ C·h⁴` from the now-public AB3 vector fourth-order Taylor helpers `y_fourth_order_taylor_remainder_vec` / `derivY_third_order_taylor_remainder_vec`), and the headline `LMM.am2Vec_global_error_bound` (`‖y_N − y(t₀+Nh)‖ ≤ exp(3L·T)·ε₀ + K·h³` for `(N+1)·h ≤ T`) — the vector AM2 `O(h³)` convergence theorem in a finite-dimensional normed space. (`OpenMath/LMMAM2VectorConvergence.lean`, cycle 438)
  - [x] **Adams–Bashforth 3-step scalar convergence chain**: `LMM.ab3Iter` (three starting samples, recurrence `y_{n+3} = y_{n+2} + h·(23/12·f_{n+2} − 16/12·f_{n+1} + 5/12·f_n)`), `LMM.ab3_localTruncationError_eq` (textbook AB3 one-step residual = LMM truncation operator), `LMM.ab3_one_step_lipschitz` and `LMM.ab3_one_step_error_bound` (Lipschitz 3-window max-norm one-step recurrence `max(eₙ₊₁,eₙ₊₂,eₙ₊₃) ≤ (1+h·(11/3)L)·max(eₙ,eₙ₊₁,eₙ₊₂) + |τ_n|` with effective Lipschitz constant `(23+16+5)/12 · L = 11L/3`), private helpers `iteratedDeriv_four_bounded_on_Icc`, `y_fourth_order_taylor_remainder`, `derivY_third_order_taylor_remainder`, `ab3_pointwise_residual_bound` (algebraic identity `R_y(3) − R_y(2) − (23h/12)·R_y'(2) + (16h/12)·R_y'(1)` giving `7·M·h⁴` over-estimate), `LMM.ab3_local_residual_bound` (uniform `|τ_n| ≤ C·h⁴`), and the headline `LMM.ab3_global_error_bound` (`|y_N − y(t₀+Nh)| ≤ exp((11/3)·L·T)·ε₀ + K·h³` for `(N+2)·h ≤ T`) — the textbook AB3 `O(h³)` convergence theorem assembled via `lmm_error_bound_from_local_truncation` at `p = 3`. (`OpenMath/LMMAB3Convergence.lean`, cycles 416 + 418)
  - [x] **Adams–Bashforth 3-step vector convergence chain**: `LMM.ab3IterVec`, `LMM.ab3VecResidual` + `LMM.ab3Vec_localTruncationError_eq` (textbook vector residual unfolding), `LMM.ab3Vec_one_step_lipschitz` and `LMM.ab3Vec_one_step_error_bound` (3-window max-norm Lipschitz recurrence with effective constant `(11/3)·L`), private interval-integral Taylor helpers `iteratedDeriv_four_bounded_on_Icc_vec`, `y_fourth_order_taylor_remainder_vec`, `derivY_third_order_taylor_remainder_vec`, and `ab3Vec_pointwise_residual_bound` (same `7·M·h⁴` over-estimate as the scalar chain), `LMM.ab3Vec_local_residual_bound`, and the headline `LMM.ab3Vec_global_error_bound` (`‖y_N − y(t₀+Nh)‖ ≤ exp((11/3)·L·T)·ε₀ + K·h³` for `(N+2)·h ≤ T`) — vector mirror of the scalar AB3 convergence chain in finite-dimensional normed spaces. (`OpenMath/LMMAB3Convergence.lean`, cycle 419)
  - [x] **Adams–Moulton 3-step scalar convergence chain**: `LMM.IsAM3Trajectory` (supplied implicit trajectory satisfying `yₙ₊₃ = yₙ₊₂ + h(9/24 fₙ₊₃ + 19/24 fₙ₊₂ − 5/24 fₙ₊₁ + 1/24 fₙ)`), `LMM.am3_localTruncationError_eq`, `LMM.am3_one_step_lipschitz` and `LMM.am3_one_step_error_pair_bound` (3-window implicit recurrence under `(9/24)hL ≤ 1/2`; explicit AM3 weights contribute `25L/24`, and the divided proof uses conservative growth `3L`), `LMM.am3_pointwise_residual_bound` (fifth-order Taylor identity with coefficient `131/32`, slackened to `5`), `LMM.am3_local_residual_bound` (`|τ_n| ≤ C·h⁵`), and the headline `LMM.am3_global_error_bound` (`|y_N − y(t₀+Nh)| ≤ exp(3L·T)·ε₀ + K·h⁴` for `(N+2)·h ≤ T`) — the textbook AM3 `O(h⁴)` scalar convergence theorem for supplied implicit trajectories. (`OpenMath/LMMAM3Convergence.lean`, cycle 435)
  - [x] **Adams–Moulton 3-step vector convergence chain**: `LMM.IsAM3TrajectoryVec` (supplied implicit vector trajectory `yₙ₊₃ = yₙ₊₂ + h • ((9/24) • fₙ₊₃ + (19/24) • fₙ₊₂ − (5/24) • fₙ₊₁ + (1/24) • fₙ)`), `LMM.am3Vec_localTruncationError_eq`, `LMM.am3Vec_one_step_lipschitz` and `LMM.am3Vec_one_step_error_pair_bound` (3-window implicit recurrence under `(9/24)hL ≤ 1/2`, slackened to growth `3L` and residual coefficient `2` after division), `LMM.am3Vec_pointwise_residual_bound` and `LMM.am3Vec_local_residual_bound` (`‖τ_n‖ ≤ C·h⁵` from the now-public AB4 vector fifth-order Taylor helpers `y_fifth_order_taylor_remainder_vec` / `derivY_fourth_order_taylor_remainder_vec`), and the headline `LMM.am3Vec_global_error_bound` (`‖y_N − y(t₀+Nh)‖ ≤ exp(3L·T)·ε₀ + K·h⁴` for `(N+2)·h ≤ T`) — the vector AM3 `O(h⁴)` convergence theorem in a finite-dimensional normed space. (`OpenMath/LMMAM3VectorConvergence.lean`, cycle 439)
  - [x] **Adams–Moulton 4-step scalar convergence chain**: `LMM.IsAM4Trajectory` (supplied implicit trajectory satisfying `yₙ₊₄ = yₙ₊₃ + h(251/720 fₙ₊₄ + 646/720 fₙ₊₃ − 264/720 fₙ₊₂ + 106/720 fₙ₊₁ − 19/720 fₙ)`), `LMM.am4_localTruncationError_eq`, `LMM.am4_one_step_lipschitz` and `LMM.am4_one_step_error_pair_bound` (4-window implicit recurrence under `(251/720)hL ≤ 1/2`; explicit AM4 weights contribute `1035/720 = 23L/16`, and the divided proof slackens growth to `4L` since `3L` does not close `nlinarith`), `LMM.am4_pointwise_residual_bound` (sixth-order Taylor identity with coefficient `250389/21600 ≈ 11.59`, slackened to `12`, using the now-public `iteratedDeriv_six_bounded_on_Icc` / `y_sixth_order_taylor_remainder` / `derivY_fifth_order_taylor_remainder` from `LMMAB5Convergence`), `LMM.am4_local_residual_bound` (`|τ_n| ≤ C·h⁶`), and the headline `LMM.am4_global_error_bound` (`|y_N − y(t₀+Nh)| ≤ exp(4L·T)·ε₀ + K·h⁵` for `(N+3)·h ≤ T`) — the textbook AM4 `O(h⁵)` scalar convergence theorem for supplied implicit trajectories. (`OpenMath/LMMAM4Convergence.lean`, cycle 436)
  - [x] **Adams–Moulton 4-step vector convergence chain**: `LMM.IsAM4TrajectoryVec` (supplied implicit vector trajectory `yₙ₊₄ = yₙ₊₃ + h • ((251/720) • fₙ₊₄ + (646/720) • fₙ₊₃ − (264/720) • fₙ₊₂ + (106/720) • fₙ₊₁ − (19/720) • fₙ)`), `LMM.am4Vec_localTruncationError_eq`, `LMM.am4Vec_one_step_lipschitz` and `LMM.am4Vec_one_step_error_pair_bound` (4-window implicit recurrence under `(251/720)hL ≤ 1/2`, slackened to growth `4L` and residual coefficient `2` after division), `LMM.am4Vec_pointwise_residual_bound` and `LMM.am4Vec_local_residual_bound` (`‖τ_n‖ ≤ C·h⁶` from the now-public AB5 vector sixth-order Taylor helpers `iteratedDeriv_six_bounded_on_Icc_vec` / `y_sixth_order_taylor_remainder_vec` / `derivY_fifth_order_taylor_remainder_vec`), and the headline `LMM.am4Vec_global_error_bound` (`‖y_N − y(t₀+Nh)‖ ≤ exp(4L·T)·ε₀ + K·h⁵` for `(N+3)·h ≤ T`) — the vector AM4 `O(h⁵)` convergence theorem in a finite-dimensional normed space. (`OpenMath/LMMAM4VectorConvergence.lean`, cycle 440)
  - [x] **Adams–Moulton 5-step scalar convergence chain**: `LMM.IsAM5Trajectory` (supplied implicit trajectory satisfying `yₙ₊₅ = yₙ₊₄ + h(475/1440 fₙ₊₅ + 1427/1440 fₙ₊₄ − 798/1440 fₙ₊₃ + 482/1440 fₙ₊₂ − 173/1440 fₙ₊₁ + 27/1440 fₙ)`), `LMM.am5_localTruncationError_eq`, `LMM.am5_one_step_lipschitz` and `LMM.am5_one_step_error_pair_bound` (5-window implicit recurrence under `(475/1440)hL ≤ 1/2`; explicit AM5 weights contribute `2907/1440`, and the divided proof slackens growth to `5L`), `LMM.am5_pointwise_residual_bound` (seventh-order Taylor identity with coefficient `23325037/725760 ≈ 32.14`, slackened to `33`, using the now-public `iteratedDeriv_seven_bounded_on_Icc` / `y_seventh_order_taylor_remainder` / `derivY_sixth_order_taylor_remainder` from `LMMAB6ScalarConvergence`), `LMM.am5_local_residual_bound` (`|τ_n| ≤ C·h⁷`), and the headline `LMM.am5_global_error_bound` (`|y_N − y(t₀+Nh)| ≤ exp(5L·T)·ε₀ + K·h⁶` for `(N+4)·h ≤ T`) — the textbook AM5 `O(h⁶)` scalar convergence theorem for supplied implicit trajectories. (`OpenMath/LMMAM5Convergence.lean`, cycle 437)
  - [x] **Adams–Moulton 5-step vector convergence chain**: `LMM.IsAM5TrajectoryVec` (supplied implicit vector trajectory `yₙ₊₅ = yₙ₊₄ + h • ((475/1440) • fₙ₊₅ + (1427/1440) • fₙ₊₄ − (798/1440) • fₙ₊₃ + (482/1440) • fₙ₊₂ − (173/1440) • fₙ₊₁ + (27/1440) • fₙ)`), `LMM.am5Vec_localTruncationError_eq`, `LMM.am5Vec_one_step_lipschitz` and `LMM.am5Vec_one_step_error_pair_bound` (5-window implicit recurrence under `(475/1440)hL ≤ 1/2`, slackened to growth `5L` and residual coefficient `2` after division), `LMM.am5Vec_pointwise_residual_bound` and `LMM.am5Vec_local_residual_bound` (`‖τ_n‖ ≤ C·h⁷` from the now-public AB6 vector seventh-order Taylor helpers `iteratedDeriv_seven_bounded_on_Icc_vec` / `y_seventh_order_taylor_remainder_vec` / `derivY_sixth_order_taylor_remainder_vec`), and the headline `LMM.am5Vec_global_error_bound` (`‖y_N − y(t₀+Nh)‖ ≤ exp(5L·T)·ε₀ + K·h⁶` for `(N+4)·h ≤ T`) — the vector AM5 `O(h⁶)` convergence theorem in a finite-dimensional normed space. (`OpenMath/LMMAM5VectorConvergence.lean`, cycle 441)
  - [x] **Adams–Moulton 6-step scalar convergence chain**: `LMM.IsAM6Trajectory`, `LMM.am6_localTruncationError_eq`, `LMM.am6_one_step_lipschitz` and `LMM.am6_one_step_error_pair_bound` (6-window implicit recurrence under `(19087/60480)hL ≤ 1/2`, slackened to growth `7L` and residual coefficient `2` after division), private eighth-order Taylor helpers, `LMM.am6_pointwise_residual_bound`, `LMM.am6_local_residual_bound` (`|τ_n| ≤ C·h⁸`, exact coefficient `1121952791/12700800` slackened to `89`), and the headline `LMM.am6_global_error_bound` (`|y_N − y(t₀+Nh)| ≤ exp(7L·T)·ε₀ + K·h⁷` for `(N+5)·h ≤ T`). (`OpenMath/LMMAM6Convergence.lean`, cycle 442)
  - [x] **Adams–Moulton 6-step vector convergence chain**: `LMM.IsAM6TrajectoryVec` (supplied implicit vector trajectory with AM6 weights), `LMM.am6Vec_localTruncationError_eq`, `LMM.am6Vec_one_step_lipschitz` and `LMM.am6Vec_one_step_error_pair_bound` (6-window implicit recurrence under `(19087/60480)hL ≤ 1/2`, slackened to growth `7L` and residual coefficient `2` after division), private eighth-order vector Taylor helpers, `LMM.am6Vec_pointwise_residual_bound`, `LMM.am6Vec_local_residual_bound` (`‖τ_n‖ ≤ C·h⁸`, exact coefficient `1121952791/12700800` slackened to `89`), and the headline `LMM.am6Vec_global_error_bound` (`‖y_N − y(t₀+Nh)‖ ≤ exp(7L·T)·ε₀ + K·h⁷` for `(N+5)·h ≤ T`) — the vector AM6 `O(h⁷)` convergence theorem in a finite-dimensional normed space. (`OpenMath/LMMAM6VectorConvergence.lean`, cycle 443)
  - [x] **Adams–Moulton 7-step scalar convergence chain**: `LMM.adamsMoulton7` (added to `OpenMath/AdamsMethods.lean`), `LMM.IsAM7Trajectory` (supplied implicit trajectory satisfying `yₙ₊₇ = yₙ₊₆ + h·(36799/120960 fₙ₊₇ + 139849/120960 fₙ₊₆ − 121797/120960 fₙ₊₅ + 123133/120960 fₙ₊₄ − 88547/120960 fₙ₊₃ + 41499/120960 fₙ₊₂ − 11351/120960 fₙ₊₁ + 1375/120960 fₙ)`), `LMM.am7_localTruncationError_eq`, `LMM.am7_one_step_lipschitz` and `LMM.am7_one_step_error_pair_bound` (7-window implicit recurrence under `(36799/120960)hL ≤ 1/2`, slackened to growth `10L` and residual coefficient `2` after division — minimum integer `G ≥ 2(β + S) ≈ 9.33` is 10), private ninth-order Taylor helpers `iteratedDeriv_nine_bounded_on_Icc`, `y_ninth_order_taylor_remainder`, `derivY_eighth_order_taylor_remainder`, the extracted `am7_residual_alg_identity` / `am7_residual_bound_alg_identity` / `am7_residual_nine_term_triangle` / `am7_residual_combine` helpers (kernel-friendly extraction, mirroring cycle 442's AM6 split), `LMM.am7_pointwise_residual_bound`, `LMM.am7_local_residual_bound` (`|τ_n| ≤ C·h⁹`, exact coefficient `84361887977/348364800 ≈ 242.17` slackened to `243`), and the headline `LMM.am7_global_error_bound` (`|y_N − y(t₀+Nh)| ≤ exp(10L·T)·ε₀ + K·h⁸` for `(N+6)·h ≤ T`). (`OpenMath/LMMAM7Convergence.lean`, cycle 444)
  - [x] **Adams–Moulton 7-step vector convergence chain**: `LMM.IsAM7TrajectoryVec`, `LMM.am7Vec_localTruncationError_eq`, `LMM.am7Vec_one_step_lipschitz` and `LMM.am7Vec_one_step_error_pair_bound` (7-window supplied implicit vector recurrence under `(36799/120960)hL ≤ 1/2`, slackened to growth `10L` and residual coefficient `2` after division), private ninth-order vector Taylor helpers `iteratedDeriv_nine_bounded_on_Icc_vec`, `y_ninth_order_taylor_remainder_vec`, `derivY_eighth_order_taylor_remainder_vec`, the extracted `am7Vec_residual_alg_identity` / `am7Vec_residual_bound_alg_identity` / `am7Vec_residual_nine_term_triangle` / `am7Vec_residual_combine` helpers, `LMM.am7Vec_pointwise_residual_bound`, `LMM.am7Vec_local_residual_bound` (`‖τ_n‖ ≤ C·h⁹`, exact scalar coefficient slackened to `243`), and the headline `LMM.am7Vec_global_error_bound` (`‖y_N − y(t₀+Nh)‖ ≤ exp(10L·T)·ε₀ + K·h⁸` for `(N+6)·h ≤ T`) — closing the AB2–AB6 + AM2–AM7 §1.2 quantitative convergence stack. (`OpenMath/LMMAM7VectorConvergence.lean`, cycle 445)
  - [x] **Adams–Bashforth 4-step scalar convergence chain**: `LMM.ab4Iter` (four starting samples, recurrence `y_{n+4} = y_{n+3} + h·((55/24)·f_{n+3} − (59/24)·f_{n+2} + (37/24)·f_{n+1} − (9/24)·f_n)`), `LMM.ab4_localTruncationError_eq` (textbook AB4 one-step residual = LMM truncation operator), `LMM.ab4_one_step_lipschitz` and `LMM.ab4_one_step_error_bound` (Lipschitz 4-window max-norm one-step recurrence `max(eₙ₊₁,…,eₙ₊₄) ≤ (1+h·(20/3)L)·max(eₙ,…,eₙ₊₃) + |τ_n|` with effective Lipschitz constant `(55+59+37+9)/24 · L = 20L/3`), private helpers `iteratedDeriv_five_bounded_on_Icc`, `y_fifth_order_taylor_remainder`, `derivY_fourth_order_taylor_remainder`, `ab4_pointwise_residual_bound` (algebraic identity `R_y(4) − R_y(3) − (55h/24)·R_y'(3) + (59h/24)·R_y'(2) − (37h/24)·R_y'(1)` giving `20·M·h⁵` over-estimate from `57588/2880`), `LMM.ab4_local_residual_bound` (uniform `|τ_n| ≤ C·h⁵`), and the headline `LMM.ab4_global_error_bound` (`|y_N − y(t₀+Nh)| ≤ exp((20/3)·L·T)·ε₀ + K·h⁴` for `(N+3)·h ≤ T`) — the textbook AB4 `O(h⁴)` convergence theorem assembled via `lmm_error_bound_from_local_truncation` at `p = 4`. (`OpenMath/LMMAB4Convergence.lean`, cycle 420)
  - [x] **Adams–Bashforth 4-step vector convergence chain**: `LMM.ab4IterVec`, `LMM.ab4VecResidual` + `LMM.ab4Vec_localTruncationError_eq` (textbook vector residual unfolding), `LMM.ab4Vec_one_step_lipschitz` and `LMM.ab4Vec_one_step_error_bound` (4-window max-norm Lipschitz recurrence with effective constant `(20/3)·L`), private interval-integral Taylor helpers `iteratedDeriv_five_bounded_on_Icc_vec`, `y_fifth_order_taylor_remainder_vec`, `derivY_fourth_order_taylor_remainder_vec`, and `ab4Vec_pointwise_residual_bound` (same `20·M·h⁵` over-estimate as the scalar chain), `LMM.ab4Vec_local_residual_bound`, and the headline `LMM.ab4Vec_global_error_bound` (`‖y_N − y(t₀+Nh)‖ ≤ exp((20/3)·L·T)·ε₀ + K·h⁴` for `(N+3)·h ≤ T`) — vector mirror of the scalar AB4 convergence chain in finite-dimensional normed spaces. (`OpenMath/LMMAB4Convergence.lean`, cycle 421)
  - [x] **Adams–Bashforth 5-step scalar convergence chain**: `LMM.ab5Iter` (five starting samples, recurrence `y_{n+5} = y_{n+4} + h·((1901/720)·f_{n+4} − (2774/720)·f_{n+3} + (2616/720)·f_{n+2} − (1274/720)·f_{n+1} + (251/720)·f_n)`), `LMM.ab5_localTruncationError_eq` (textbook AB5 one-step residual = LMM truncation operator), `LMM.ab5_one_step_lipschitz` and `LMM.ab5_one_step_error_bound` (Lipschitz 5-window max-norm one-step recurrence `max(eₙ₊₁,…,eₙ₊₅) ≤ (1+h·(551/45)L)·max(eₙ,…,eₙ₊₄) + |τ_n|` with effective Lipschitz constant `(1901+2774+2616+1274+251)/720 · L = 551L/45`), private helpers `iteratedDeriv_six_bounded_on_Icc`, `y_sixth_order_taylor_remainder`, `derivY_fifth_order_taylor_remainder`, `ab5_pointwise_residual_bound` (algebraic identity `R_y(5) − R_y(4) − (1901h/720)·R_y'(4) + (2774h/720)·R_y'(3) − (2616h/720)·R_y'(2) + (1274h/720)·R_y'(1)` giving `59·M·h⁶` over-estimate from `5072212/86400`), `LMM.ab5_local_residual_bound` (uniform `|τ_n| ≤ C·h⁶`), and the headline `LMM.ab5_global_error_bound` (`|y_N − y(t₀+Nh)| ≤ exp((551/45)·L·T)·ε₀ + K·h⁵` for `(N+4)·h ≤ T`) — the textbook AB5 `O(h⁵)` convergence theorem assembled via `lmm_error_bound_from_local_truncation` at `p = 5`. (`OpenMath/LMMAB5Convergence.lean`, cycle 422)
  - [x] **Adams–Bashforth 5-step vector convergence chain**: `LMM.ab5IterVec`, `LMM.ab5VecResidual` + `LMM.ab5Vec_localTruncationError_eq` (textbook vector residual unfolding), `LMM.ab5Vec_one_step_lipschitz` and `LMM.ab5Vec_one_step_error_bound` (5-window max-norm Lipschitz recurrence with effective constant `(551/45)·L`), private interval-integral Taylor helpers `iteratedDeriv_six_bounded_on_Icc_vec`, `y_sixth_order_taylor_remainder_vec`, `derivY_fifth_order_taylor_remainder_vec`, and `ab5Vec_pointwise_residual_bound` (same `59·M·h⁶` over-estimate as the scalar chain from `5072212/86400`), `LMM.ab5Vec_local_residual_bound`, and the headline `LMM.ab5Vec_global_error_bound` (`‖y_N − y(t₀+Nh)‖ ≤ exp((551/45)·L·T)·ε₀ + K·h⁵` for `(N+4)·h ≤ T`) — vector mirror of the scalar AB5 convergence chain in finite-dimensional normed spaces; cycle 431 adds `LMM.ab5GenericCoeff`, the iteration/residual bridges to `LMM.abIterVec`/`LMM.abResidualVec`, and rewires the headline theorem through `LMM.ab_global_error_bound_generic_vec`. (`OpenMath/LMMAB5Convergence.lean`, cycles 423 + 431)
  - [x] **Adams–Bashforth 6-step scalar convergence chain**: `LMM.ab6Iter` (six starting samples, recurrence `y_{n+6} = y_{n+5} + h·((4277/1440)·f_{n+5} − (7923/1440)·f_{n+4} + (9982/1440)·f_{n+3} − (7298/1440)·f_{n+2} + (2877/1440)·f_{n+1} − (475/1440)·f_n)`), `LMM.ab6_localTruncationError_eq` (textbook AB6 one-step residual = LMM truncation operator), `LMM.ab6_one_step_lipschitz` and `LMM.ab6_one_step_error_bound` (Lipschitz 6-window max-norm one-step recurrence `max(eₙ₊₁,…,eₙ₊₆) ≤ (1+h·(114/5)L)·max(eₙ,…,eₙ₊₅) + |τ_n|` with effective Lipschitz constant `(4277+7923+9982+7298+2877+475)/1440 · L = 114L/5`), private helpers `iteratedDeriv_seven_bounded_on_Icc`, `y_seventh_order_taylor_remainder`, `derivY_sixth_order_taylor_remainder`, `ab6_pointwise_residual_bound` (algebraic identity `R_y(6) − R_y(5) − (4277h/1440)·R_y'(5) + (7923h/1440)·R_y'(4) − (9982h/1440)·R_y'(3) + (7298h/1440)·R_y'(2) − (2877h/1440)·R_y'(1)` giving `175·M·h⁷` over-estimate from `1264800760/7257600`), `LMM.ab6_local_residual_bound` (uniform `|τ_n| ≤ C·h⁷`), and the headline `LMM.ab6_global_error_bound` (`|y_N − y(t₀+Nh)| ≤ exp((114/5)·L·T)·ε₀ + K·h⁶` for `(N+5)·h ≤ T`) — the textbook AB6 `O(h⁶)` convergence theorem assembled via `lmm_error_bound_from_local_truncation` at `p = 6`. (`OpenMath/LMMAB6ScalarConvergence.lean`, cycle 424; split in cycle 425)
  - [x] **Adams–Bashforth 6-step vector convergence chain**: `LMM.ab6IterVec`, `LMM.ab6VecResidual` + `LMM.ab6Vec_localTruncationError_eq` (textbook vector residual unfolding), `LMM.ab6Vec_one_step_lipschitz` and `LMM.ab6Vec_one_step_error_bound` (6-window max-norm Lipschitz recurrence with effective constant `(114/5)·L`), private interval-integral Taylor helpers `iteratedDeriv_seven_bounded_on_Icc_vec`, `y_seventh_order_taylor_remainder_vec`, `derivY_sixth_order_taylor_remainder_vec`, and `ab6Vec_pointwise_residual_bound` (same `175·M·h⁷` over-estimate as the scalar chain from `1264800760/7257600`), `LMM.ab6Vec_local_residual_bound`, and the headline `LMM.ab6Vec_global_error_bound` (`‖y_N − y(t₀+Nh)‖ ≤ exp((114/5)·L·T)·ε₀ + K·h⁶` for `(N+5)·h ≤ T`) — vector mirror of the scalar AB6 convergence chain in finite-dimensional normed spaces. (`OpenMath/LMMAB6VectorConvergence.lean`, cycle 425)
  - [x] **BDF1 (backward Euler) scalar quantitative convergence chain**: `LMM.IsBDF1Trajectory` (supplied implicit one-step trajectory satisfying `y_{n+1} = y_n + h · f(t_{n+1}, y_{n+1})`), `LMM.bdf1_localTruncationError_eq` (textbook one-step residual `y(t+h) − y(t) − h · y'(t+h)` equals the LMM truncation operator for `backwardEuler`), `LMM.bdf1_one_step_lipschitz` and `LMM.bdf1_one_step_error_bound` (1-window implicit recurrence under `h·L ≤ 1/2`, slackened to growth `2L` and residual coefficient `2` after dividing out `(1 − h·L)`), `LMM.bdf1_pointwise_residual_bound` (forward-Euler Taylor remainder plus a segment derivative bound on `|y'(t+h) − y'(t)| ≤ M·h` giving `(3/2)·M·h²` slackened to `2·M·h²`), `LMM.bdf1_local_residual_bound` (`|τ_n| ≤ C·h²`), and the headline `LMM.bdf1_global_error_bound` (`|y_N − y(t₀+Nh)| ≤ exp(2L·T)·ε₀ + K·h` for `N·h ≤ T`) — the textbook BDF1 `O(h)` scalar convergence theorem for supplied implicit trajectories. (`OpenMath/LMMBDF1Convergence.lean`, cycle 446)
  - [x] **BDF1 (backward Euler) vector quantitative convergence chain**: `LMM.IsBDF1TrajectoryVec` (supplied implicit one-step vector trajectory satisfying `y_{n+1} = y_n + h • f(t_{n+1}, y_{n+1})`), `LMM.bdf1VecResidual` + `LMM.bdf1Vec_localTruncationError_eq` (textbook vector residual unfolding), `LMM.bdf1Vec_one_step_lipschitz` and `LMM.bdf1Vec_one_step_error_bound` (1-window implicit norm recurrence under `h·L ≤ 1/2`, slackened to growth `2L` and residual coefficient `2` after dividing out `(1 − h·L)`), private vector Taylor helpers for `‖y'(t+h)-y'(t)‖ ≤ M·h` and `‖y(t+h)-y(t)-h•y'(t)‖ ≤ M/2·h²`, `LMM.bdf1Vec_local_residual_bound` (`‖τ_n‖ ≤ C·h²`), and the headline `LMM.bdf1Vec_global_error_bound` (`‖y_N − y(t₀+Nh)‖ ≤ exp(2L·T)·ε₀ + K·h` for `N·h ≤ T`) — the finite-dimensional vector mirror of the scalar BDF1 quantitative convergence theorem. (`OpenMath/LMMBDF1VectorConvergence.lean`, cycle 447)
- [x] **Theorem**: Consistency conditions for multistep methods (`OpenMath/MultistepMethods.lean`)
- [x] **Definition**: Order of a linear multistep method (`OpenMath/MultistepMethods.lean`)
- [x] **Theorem**: Zero-stability of multistep methods (`OpenMath/MultistepMethods.lean`)
- [x] **Definition**: A-stability of multistep methods (`OpenMath/MultistepMethods.lean`)
- [x] **Theorem**: A-stability implies roots of ρ in unit disk (`OpenMath/MultistepMethods.lean`)
- [x] **Theorem**: Dahlquist's second barrier — A-stable + zero-stable ⟹ order ≤ 2 (`OpenMath/MultistepMethods.lean`)
  - [x] `E_nonneg_re`: Re(σ/ρ) ≥ 0 on unit circle for A-stable methods
  - [x] `re_inv_exp_sub_one`: Re(1/(e^{iθ}-1)) = -1/2 on the unit circle
  - [x] `sigmaC_one_eq_rhoCDeriv_one`: σ_ℂ(1) = ρ'_ℂ(1) for consistent methods
  - [x] `sigmaC_one_ne_zero`: σ(1) ≠ 0 for zero-stable consistent methods
  - [x] `dahlquistCounterexample`: counterexample (order 3, A-stable, not zero-stable)
  - [x] Reversed polynomial identity: ρ̃(w) = w^s · ρ(1/w) via `Fin.revPerm`
  - [x] Boundary non-negativity: Re(Gt(z)) ≥ 0 for |z| = 1
  - [x] `DiffContOnCl ℂ Gt (Metric.ball 0 1)`: removable singularity + boundary regularity
  - [x] `HasDerivAt Gt (1/12) 1`: polynomial algebra for derivative at removable singularity
  - [x] `continuousOn_Gtilde_closedBall`: continuity on closed unit disk
- [x] **Theorem**: Dahlquist equivalence theorem (consistency + stability ⟺ convergence) (`OpenMath/DahlquistEquivalence.lean`)
  - [x] `SatisfiesRecurrence`, `HasStableRecurrence`, `IsConvergent` definitions
  - [x] `geometric_satisfies_iff`, `linear_geometric_satisfies`
  - [x] `not_stableRecurrence_of_root_outside_disk`, `not_stableRecurrence_of_double_root_on_circle`
  - [x] `zeroStable_of_stableRecurrence`: stable recurrence → zero-stable
  - [x] `stableRecurrence_of_zeroStable`: zero-stable → stable recurrence
    - [x] `aeval_tupleSucc_charPoly_eq_zero`: Cayley-Hamilton for companion
    - [x] `charPoly_eval_eq_rhoC`: charPoly evaluation = ρ_ℂ
    - [x] `tupleSucc_eigenvalue_is_rhoC_root`: eigenvalue → ρ-root
    - [x] `uniformly_bounded_tupleSucc_iterates`: spectral bound via generalized eigenspace decomposition (`OpenMath/SpectralBound.lean`)
  - [x] `dahlquist_equivalence`: full equivalence theorem
  - [x] Convergence for Euler, trapezoidal, AB2, AM2, BDF2, BDF3
  - [x] `dahlquistCounterexample_not_convergent`

### 1.3 Order and Convergence
- [x] **Theorem**: Convergence theorem for one-step methods (`OpenMath/OneStepConvergence.lean`)

## Chapter 2: Runge–Kutta Methods

### 2.1 Explicit Runge–Kutta Methods
- [x] **Definition**: Butcher tableau (`OpenMath/RungeKutta.lean`)
- [x] **Definition**: Consistency, explicit RK, order conditions up to order 4 (`OpenMath/RungeKutta.lean`)
- [x] **Example**: Forward Euler, explicit midpoint, Heun's method as RK (`OpenMath/RungeKutta.lean`)
- [x] **Example**: Classical RK4 method — consistency, explicit, order 4 (`OpenMath/RungeKutta.lean`)
- [x] **Theorem**: Explicit RK order barriers (s-stage explicit ⟹ order ≤ s for s ≤ 4) (`OpenMath/OrderBarriers.lean`)
- [x] **Theorem**: Explicit methods cannot satisfy C(2) with distinct nodes (`OpenMath/OrderBarriers.lean`)

### 2.2 Implicit Runge–Kutta Methods
- [x] **Definition**: Implicit RK methods (implicit Euler, implicit midpoint) (`OpenMath/RungeKutta.lean`)
- [x] **Definition**: Stability function R(z) for 1-stage RK methods (`OpenMath/RungeKutta.lean`)
- [x] **Theorem**: A-stability of implicit Euler and implicit midpoint (`OpenMath/RungeKutta.lean`)
- [x] **Theorem**: Forward Euler (RK) is NOT A-stable (`OpenMath/RungeKutta.lean`)
- [x] **Example**: Gauss–Legendre 2-stage — Butcher tableau, consistency, A-stability, order 4 (`OpenMath/RungeKutta.lean`)
- [x] **Example**: Gauss–Legendre 3-stage — order ≥ 5, B(6), D(3) (`OpenMath/GaussLegendre3.lean`)
- [x] **Example**: Radau IA 2-stage — order 3, A/L-stability, algebraic stability (`OpenMath/RadauIA2.lean`)
- [x] **Example**: Radau IA 3-stage (`OpenMath/RadauIA3.lean`)
- [x] **Example**: Radau IIA 3-stage — order ≥ 5, algebraic stability (`OpenMath/RadauIIA3.lean`)
- [x] **Definition**: B(p), C(q), D(r) simplifying assumptions (`OpenMath/Collocation.lean`)
- [x] **Theorem**: B(p)∧C(q) ⟹ order ≥ p, various combinations (`OpenMath/Collocation.lean`)
- [x] **Theorem**: Nørsett's even-order theorem: symmetric + order ≥ 3 ⟹ order ≥ 4 (`OpenMath/Symmetry.lean`)
- [x] **Definition**: Self-adjoint / adjoint pair (`OpenMath/Adjoint.lean`)

### 2.3 Lobatto Methods
- [x] **Example**: Lobatto IIIA 2-stage and 3-stage (`OpenMath/LobattoIIIA.lean`, `OpenMath/LobattoIIIA3.lean`)
- [x] **Example**: Lobatto IIIB 2-stage and 3-stage (`OpenMath/LobattoIIIB.lean`, `OpenMath/LobattoIIIB3.lean`)
- [x] **Example**: Lobatto IIIC 2-stage and 3-stage (`OpenMath/LobattoIIIC.lean`, `OpenMath/LobattoIIIC3.lean`)

## Chapter 3: Stiff Equations

- [x] **Definition**: Stiffness (`OpenMath/Stiffness.lean`)
- [x] **Theorem**: A-stability of backward Euler and trapezoidal rule (`OpenMath/MultistepMethods.lean`)
- [x] **Theorem**: Forward Euler is not A-stable (`OpenMath/MultistepMethods.lean`)
- [x] **Theorem**: Dahlquist's second barrier (A-stable + zero-stable ⟹ order ≤ 2) (`OpenMath/MultistepMethods.lean`)
- [x] **Counterexample**: A-stable order-3 method without zero-stability (`dahlquistCounterexample`)
- [x] **Definition**: L-stability (`OpenMath/StiffEquations.lean`)
- [x] **Theorem**: L-stability of backward Euler, Radau IIA, SDIRK2, SDIRK3 (`OpenMath/StiffEquations.lean`, `OpenMath/SDIRK.lean`, `OpenMath/SDIRK3.lean`)
- [x] **Definition**: Algebraic stability (`OpenMath/RungeKutta.lean`)
- [x] **Theorem**: Algebraic stability of GL2, GL3, Radau IIA3, Lobatto IIIC3 (various files)
- [x] **Theorem 358A**: algebraic-stability characterization of collocation methods (`OpenMath/CollocationAlgStability.lean`)
  - [x] Forward direction: collocation + algebraically stable ⇒ nodes are zeros of `P_s^* − θ P_{s-1}^*` for some θ ≥ 0
  - [x] Reverse direction: collocation + boundary nodes ⇒ algebraically stable (cycle 371, via `antiderivPoly` helper and Lagrange/quadrature route)
- [x] **Theorem 359C**: classical collocation families are algebraically stable (`OpenMath/CollocationFamilies.lean`)
  - [x] `gaussLegendreNodes_hasAlgStabilityBoundaryNodes`: GL nodes ⇒ θ=0 boundary nodes
  - [x] `thm_359C_gaussLegendre`: any collocation method with GL nodes is algebraically stable (via 358A)
  - [x] `thm_359C_radauI`: any collocation method on `P_s^* − P_{s-1}^*` zeros is algebraically stable (θ=1)
  - [x] Concrete corollaries `rkGaussLegendre2_algStable_via_358A` and `rkGaussLegendre3_algStable_via_358A`
- [x] **Theorem 359B**: Radau IIA family is algebraically stable (`OpenMath/CollocationFamilies.lean`, cycle 374)
  - [x] `HasRadauIIANodes`: tableau abscissae are zeros of `P_s^* − P_{s-1}^*` (right-endpoint Radau, θ=1 under live sign convention)
  - [x] `radauIIANodes_hasAlgStabilityBoundaryNodes`: Radau IIA nodes ⇒ algebraic-stability boundary nodes with θ = 1 ≥ 0
  - [x] `thm_359B_radauIIA`: any collocation method with Radau IIA nodes is algebraically stable (via 358A)
  - [x] Concrete corollary `rkRadauIIA3_algStable_via_358A`
- [ ] **Theorem 359B (Radau IA side)**: left-endpoint Radau algebraic-stability family (`OpenMath/CollocationFamilies.lean`, cycle 375 partial)
  - [x] `HasRadauIANodes`: tableau abscissae are zeros of `P_s^* + P_{s-1}^*` (`algStabilityBoundaryPoly s (-1)`)
  - [x] Concrete node certificates `rkRadauIA2_hasRadauIANodes` and `rkRadauIA3_hasRadauIANodes`
  - [ ] Family-level bridge blocked: the requested `IsCollocation` + θ = -1 statement is false for the genuine 2-stage left-Radau collocation tableau; see `.prover-state/issues/cycle_375_radauIA_collocation_counterexample.md`
- [x] **§3.5.10 packaging corollaries**: family-level BN-stability for collocation methods (`OpenMath/CollocationFamilies.lean`, cycle 376)
  - [x] `thm_359C_gaussLegendre_bnStable`: `IsCollocation ∧ HasGaussLegendreNodes → IsBNStable`
  - [x] `thm_359B_radauIIA_bnStable`: `IsCollocation ∧ HasRadauIIANodes → IsBNStable`
  - [x] `thm_359C_radauI_bnStable`: `IsCollocation ∧ (zeros of P_s^* − P_{s-1}^*) → IsBNStable`
  - [x] Concrete corollaries `rkGaussLegendre2_bnStable_via_358A`, `rkGaussLegendre3_bnStable_via_358A`, `rkRadauIIA3_bnStable_via_358A`
  - [ ] Real Theorem 359D textbook statement still pending: requires Iserles §3.5.10 lookup to identify the named theorem after 359C
- [x] **Theorem 351B**: A-stability criterion via E-function (`OpenMath/AStabilityCriterion.lean`)
- [x] **Theorems 355C/355D/355E**: global order-arrow trajectory bookkeeping (`OpenMath/OrderStars.lean`, `OpenMath/PadeOrderStars.lean`)
  - [x] Formalized local order-star geometry, arrow directions, and the 355F imaginary-axis obstruction
  - [x] Introduced explicit endpoint bookkeeping via `OrderArrowTerminationData`
  - [x] Closed the concrete no-escape seam via `noArrowsEscapeToInfinity_of_concreteRationalApprox`
  - [x] Landed the concrete wrappers `thm_355D_of_concreteRationalApprox` and `thm_355E'_of_concreteRationalApprox`
- [x] **Theorem 355G**: repaired Ehle barrier / Padé wedge boundary (`OpenMath/OrderStars.lean`, `OpenMath/PadeOrderStars.lean`)
  - [x] Kept the honest downstream boundary separate as `EhleBarrierInput`
  - [x] Built the concrete Padé constructor `ehleBarrierInput_of_padeR_aStable`
  - [x] Closed `padeREhleBarrierNatInput_of_padeR_aStable` and `ehle_barrier_nat_of_padeR`
- [x] **Theorem 356C**: AN-stability implies algebraic stability (`OpenMath/ANStability.lean`)
  - [x] Defined AN-stability (`IsANStable`) and diagonal stability function (`stabilityFnDiag`)
  - [x] Proved `bⱼ ≥ 0` direction: det formula, stability function formula, norm bound
  - [x] Proved M positive semidefinite direction via the imaginary-basis perturbation argument
- [x] **Theorem 357C**: algebraic stability implies BN-stability (`OpenMath/BNStability.lean`)
- [x] **Theorem 357D**: BN-stability implies AN-stability for irreducible non-confluent methods (`OpenMath/BNImpliesAN.lean`)
- [x] **Definition**: Padé approximants and stability functions (`OpenMath/Pade.lean`)
- [x] **Theorem 353A**: Padé approximation order (`OpenMath/PadeOrder.lean`)
- [x] **Theorem 352C/352D**: Padé recurrence infrastructure (`OpenMath/Pade.lean`)
  - [x] Added general `padeP`, `padeQ`, `padeR` families
  - [x] Proved diagonal symmetry and specialization lemmas `padeQ_diagonal_eq_padeP_neg`, `padeP_one_one`, `padeQ_two_two`
  - [x] Proved pair packaging theorem `padePQ_pair_recurrence`
  - [x] Proved coefficient recurrences `padeQ_succ_left`, `padeP_succ_right`
- [x] **Definition**: Embedded RK pairs (`OpenMath/EmbeddedRK.lean`)
- [x] **Definition**: Stiff accuracy (`OpenMath/StiffAccuracy.lean`)
- [x] **Theorem 342C**: Gaussian quadrature order-condition equivalence (`OpenMath/Collocation.lean`)
  - [x] Defined `SatisfiesE (η, ζ)` from equation (321c)
  - [x] Proved `B(2s) ∧ C(s) ⇒ E(s,s)` (342m) and `B(2s) ∧ D(s) ⇒ E(s,s)` (342o)
  - [x] Proved `B(2s) ∧ E(s,s) ⇒ C(s)` (342n, requires distinct nodes + nonzero weights) via Vandermonde uniqueness
  - [x] Proved `B(2s) ∧ E(s,s) ⇒ D(s)` (342p, requires distinct nodes) via Vandermonde uniqueness
  - [x] Proved `G(p) ⇒ B(p)` (342j) via `bushyTree`
  - [x] Proved `G(2n) ⇒ E(n,n)` (342k) via `branchedTree`
  - [x] `B(2n) ∧ C(n) ∧ D(n) ⇒ G(2n)` (342l) fully proved via gen_tree_cond_big_child_aux
- [x] **Theorem 301A**: rooted-tree infrastructure (`OpenMath/RootedTree.lean`)
  - [x] Defined `BTree`
  - [x] Defined `order`, `symmetry`, `density`
  - [x] Added basic examples of orders `1` through `3`
  - [x] Proved tree-based order infrastructure through order `5` (`thm_301A_order1` ... `thm_301A_order5`)
  - [x] Theorem-facing bag-first recovery interface is in place; remaining `.hnode` equalities are private `RootedTree.lean` internals with no `OrderConditions.lean` consumers

### BDF Methods (Section 4.5)
- [x] **BDF1-2**: backward Euler and BDF2 (`OpenMath/MultistepMethods.lean`)
- [x] **BDF3**: consistency, order 3, zero-stability, convergence (`OpenMath/MultistepMethods.lean`)
- [x] **BDF4**: consistency, order 4, zero-stability (`OpenMath/MultistepMethods.lean`)
- [x] **BDF5**: consistency, order 5, not A-stable (`OpenMath/MultistepMethods.lean`, `OpenMath/BDF.lean`)
- [x] **BDF6**: consistency, order 6, not A-stable (`OpenMath/MultistepMethods.lean`, `OpenMath/BDF.lean`)
- [x] **A(α)-stability**: sector definition, monotonicity, A-stable ↔ A(π/2)-stable (`OpenMath/BDF.lean`)
- [x] **Theorem**: BDF3-6 are NOT A-stable (via Dahlquist barrier) (`OpenMath/BDF.lean`)
- [x] **BDF5 zero-stability**: roots in disk via w=1/ξ substitution + nlinarith (`OpenMath/MultistepMethods.lean`)
- [x] **BDF6 zero-stability**: roots in disk via w=1/ξ substitution + nlinarith, unit roots via real/imaginary decomposition (`OpenMath/MultistepMethods.lean`)
- [x] **BDF4 convergence**: consistent + zero-stable → convergent (`OpenMath/DahlquistEquivalence.lean`)
- [x] **BDF5 convergence**: consistent + zero-stable → convergent (`OpenMath/DahlquistEquivalence.lean`)
- [x] **BDF6 convergence**: consistent + zero-stable → convergent; BDF6 is the highest-order convergent BDF method (`OpenMath/DahlquistEquivalence.lean`)
- [x] **BDF7 infrastructure**: definition, consistency, order 7, implicitness, characteristic factorization, and bad-root reduction (`OpenMath/MultistepMethods.lean`, cycle 377)
- [x] **BDF7 zero-instability**: exact algebraic root certificate for the Cayley-transformed sextic (`OpenMath/MultistepMethods.lean`, cycle 379)
- [x] **BDF7 non-convergence**: not zero-stable → not convergent via Dahlquist equivalence (`OpenMath/DahlquistEquivalence.lean`, cycle 379)
- [x] **BDF error constants**: BDF2 = −2/9, BDF3 = −3/22, BDF4 = −12/125, BDF5 = −10/137, BDF6 = −20/343, BDF7 = −35/726 (computed despite zero-instability) (`OpenMath/MultistepMethods.lean`, cycles 392–393)

## Current Target

**Current target files**: `OpenMath/LMMTruncationOp.lean` hosts the local
truncation-operator infrastructure and forward-Euler convergence chains,
`OpenMath/LMMAB2Convergence.lean` hosts the Adams–Bashforth 2-step scalar
and vector convergence chains, `OpenMath/LMMAB3Convergence.lean` hosts the
Adams–Bashforth 3-step scalar and vector convergence chains,
`OpenMath/LMMAB4Convergence.lean` hosts the Adams–Bashforth 4-step scalar
and vector convergence chains, `OpenMath/LMMAB5Convergence.lean` hosts the
Adams–Bashforth 5-step scalar and vector convergence chains,
`OpenMath/LMMAB6ScalarConvergence.lean` hosts the Adams–Bashforth 6-step
scalar convergence chain, `OpenMath/LMMAB6VectorConvergence.lean` hosts
the Adams–Bashforth 6-step vector convergence chain,
`OpenMath/LMMAM5VectorConvergence.lean` hosts the Adams–Moulton 5-step
vector quantitative convergence chain, `OpenMath/LMMAM6Convergence.lean`
hosts the Adams–Moulton 6-step scalar quantitative convergence chain,
`OpenMath/LMMAM6VectorConvergence.lean` hosts the Adams–Moulton 6-step
vector quantitative convergence chain,
`OpenMath/LMMAM7Convergence.lean` hosts the Adams–Moulton 7-step scalar
quantitative convergence chain, `OpenMath/LMMAM7VectorConvergence.lean`
hosts the Adams–Moulton 7-step vector quantitative convergence chain,
`OpenMath/LMMBDF1Convergence.lean` hosts the BDF1 (backward Euler) scalar
quantitative convergence chain, `OpenMath/LMMBDF1VectorConvergence.lean`
hosts the BDF1 (backward Euler) vector quantitative convergence chain, and
`OpenMath/MultistepMethods.lean` still hosts the rest of the §1.2 LMM stack.

**Active frontier**: AB2–AB6 now each have closed scalar and vector
quantitative convergence chains. AM2–AM7 now each have closed scalar and
vector quantitative convergence chains. Cycle 446 added
`OpenMath/LMMBDF1Convergence.lean` (BDF1 / backward Euler scalar quantitative
convergence) using the AM2 implicit template at the simpler 1-step case,
with effective growth `2L`, residual coefficient `2`, and pointwise residual
bound `2·M·h²` derived from forward-Euler Taylor plus a segment derivative
bound on `|y'(t+h) − y'(t)|`. Cycle 447 adds
`OpenMath/LMMBDF1VectorConvergence.lean`, the finite-dimensional vector mirror
with the same effective growth `2L`, residual coefficient `2`, and
`‖τ_n‖ ≤ C·h²` residual shape. The next §1.2 convergence frontier is
**BDF2 scalar quantitative convergence**, with AB7/AM8 as the next
Adams-family extension.

**Blocked/deferred theorem**: Theorem 359D still needs the concrete Iserles
§3.5.10 source statement. The cycle 376 §3.5.10 packaging corollaries provide a
clean BN-stability scaffold once that source is available. BDF7
zero-instability and the Dahlquist-equivalence `bdf7_not_convergent` wrapper
are closed.

Cycle 389 source lookup note:
- The accessible Iserles second-edition source places "Order and convergence of
  multistep methods" in §2.2, not §1.3. The named theorem found there is Theorem
  2.2, the Dahlquist equivalence theorem: starting errors tend to zero, and
  convergence is equivalent to order `p ≥ 1` plus the root condition. No separate
  quantitative `O(h^p)` starting-error theorem was located in the available source.
- Cycle 389 therefore used the strategy fallback and consolidated the Adams
  zero-stability proofs by extracting `adams_zeroStable_of_rhoC_pow_mul`.

Blocked side note:
- The Radau IA left-endpoint family cannot be added with the cycle-375 statement
  `IsCollocation ∧ HasRadauIANodes → IsAlgStable`: the project's `IsCollocation`
  interface means `C(s)`, and the explicit 2-stage left-Radau collocation tableau
  on nodes `{0, 2/3}` has `M₀₀ = -1/16`. Any future Radau IA family theorem should
  use the Radau IA simplifying-assumption shape (`B(2s-1)`, `C(s-1)`, `D(s)`) or a
  different adjoint/transpose interface, not the collocation theorem 358A bridge.

Note: in cycle 374, what the strategy called the Radau IIA "right-endpoint" case turned out to coincide with the existing `thm_359C_radauI` (θ=1) under the live sign convention `shiftedLegendreP n 1 = 1`. The new `thm_359B_radauIIA` is the semantically named wrapper plus the concrete corollary for `rkRadauIIA3`. Cycle 375 added the Radau IA node predicate and concrete node certificates, but found that the proposed collocation-family bridge is false under the live `IsCollocation` interface.

## Sorry locations

- No active `sorry`s. Frontier closed through BDF7 zero-instability and the
  BDF7 non-convergence wrapper.
