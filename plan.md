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

**Current target files**: `OpenMath/LMMTruncationOp.lean` is the active
frontier for local truncation-operator infrastructure, and
`OpenMath/MultistepMethods.lean` still hosts the rest of the §1.2 LMM stack.

**Active frontier**: the cycle 394–402 `truncationOp` thread now reaches a
uniform local truncation error bridge in `OpenMath/LMMTruncationOp.lean`:
cycle 402 closed the uniform-`(C, δ)` step, packaged the local truncation
error notation `τ(t, h)` as `localTruncationError`, and stated Iserles'
textbook-form leading-order bound `localTruncationError_leading_bound`.
The next natural step is to bootstrap from `‖τ‖ ≤ C h^(p+2)` to global
convergence/error estimates over a finite time horizon (linking the local
bound to the discrete-Grönwall / stability machinery used in Dahlquist
equivalence).

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
