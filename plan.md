# Formalization Plan

## Textbook
*A First Course in the Numerical Analysis of Differential Equations* — Arieh Iserles (Cambridge, 2nd edition)

## Status Key
- [x] Formalized (0 sorry)
- [ ] Not started
- [~] In progress

## Chapter 1: Multistep Methods

### 1.1 The Euler Method
- [x] **Theorem 212A**: Global truncation error bound for Euler method (`OpenMath/Basic.lean`)
- [x] **Theorem 213A**: Convergence of the Euler method (`OpenMath/EulerConvergence.lean`)
  - Statement: If f is Lipschitz and sufficiently smooth, the Euler method converges with order 1

### 1.2 Multistep Methods
- [x] **Definition**: General linear multistep method (Adams–Bashforth, Adams–Moulton) (`OpenMath/MultistepMethods.lean`)
- [x] **Example**: Adams–Moulton 2-step method — consistency, order 3, implicit, zero-stable (`OpenMath/MultistepMethods.lean`)
- [x] **Theorem**: Consistency conditions for multistep methods (`OpenMath/MultistepMethods.lean`)
- [x] **Definition**: Order of a linear multistep method (`OpenMath/MultistepMethods.lean`)
- [x] **Theorem**: Zero-stability of multistep methods (`OpenMath/MultistepMethods.lean`)
- [x] **Definition**: A-stability of multistep methods (`OpenMath/MultistepMethods.lean`)
- [x] **Theorem**: A-stability implies roots of ρ in unit disk (`OpenMath/MultistepMethods.lean`)
- [~] **Theorem**: Dahlquist's second barrier — A-stable + zero-stable ⟹ order ≤ 2 (2 sorrys remain in `order_ge_three_not_aStable_core`)
  - [x] `E_nonneg_re`: Re(σ/ρ) ≥ 0 on unit circle for A-stable methods
  - [x] `re_inv_exp_sub_one`: Re(1/(e^{iθ}-1)) = -1/2 on the unit circle
  - [x] `sigmaC_one_eq_rhoCDeriv_one`: σ_ℂ(1) = ρ'_ℂ(1) for consistent methods
  - [x] `sigmaC_one_ne_zero`: σ(1) ≠ 0 for zero-stable consistent methods
  - [x] `dahlquistCounterexample`: counterexample showing barrier is FALSE without zero-stability (order 3, A-stable, not zero-stable)
  - [x] Reversed polynomial identity: ρ̃(w) = w^s · ρ(1/w) via `Fin.revPerm`
  - [x] Boundary non-negativity: Re(Gt(z)) ≥ 0 for |z| = 1
  - [ ] `DiffContOnCl ℂ Gt (Metric.ball 0 1)`: removable singularity + boundary regularity
  - [ ] `HasDerivAt Gt (1/12) 1`: polynomial algebra for derivative at removable singularity
- [~] **Theorem**: Dahlquist equivalence theorem (consistency + stability ⟺ convergence) (`OpenMath/DahlquistEquivalence.lean`)
  - [x] Definition: `SatisfiesRecurrence` — characteristic recurrence of LMM
  - [x] Definition: `HasStableRecurrence` — all solutions bounded
  - [x] Definition: `IsConvergent` — consistency + stable recurrence
  - [x] `geometric_satisfies_iff`: ξ^n satisfies recurrence iff ρ(ξ) = 0
  - [x] `linear_geometric_satisfies`: n·ξ^n satisfies recurrence when ξ is double root
  - [x] `not_stableRecurrence_of_root_outside_disk`: root with |ξ| > 1 → unstable
  - [x] `not_stableRecurrence_of_double_root_on_circle`: double root on |ξ| = 1 → unstable
  - [x] `zeroStable_of_stableRecurrence`: stable recurrence → zero-stable (proved)
  - [~] `stableRecurrence_of_zeroStable`: zero-stable → stable recurrence (proved modulo spectral bound)
    - [x] `toLinearRecurrence`: connect LMM to Mathlib's `LinearRecurrence`
    - [x] `satisfiesRecurrence_iff_isSolution`: equivalence of solution predicates
    - [x] `tupleSucc_iterate_eq_mkSol`: state vector = tupleSucc^n(init)
    - [ ] `uniformly_bounded_tupleSucc_iterates`: spectral bound (1 sorry — needs Jordan NF or generalized eigenspace)
  - [x] `dahlquist_equivalence`: full equivalence theorem (modulo above sorry)
  - [x] Convergence verified for all standard methods (Euler, trapezoidal, AB2, AM2, BDF2)
  - [x] `dahlquistCounterexample_not_convergent`: counterexample is not convergent

### 1.3 Order and Convergence
- [ ] **Theorem**: Convergence theorem for one-step methods

## Chapter 2: Runge–Kutta Methods

### 2.1 Explicit Runge–Kutta Methods
- [x] **Definition**: Butcher tableau (`OpenMath/RungeKutta.lean`)
- [x] **Definition**: Consistency, explicit RK, order conditions up to order 4 (`OpenMath/RungeKutta.lean`)
- [x] **Example**: Forward Euler, explicit midpoint, Heun's method as RK (`OpenMath/RungeKutta.lean`)
- [x] **Example**: Classical RK4 method — consistency, explicit, order 4 (`OpenMath/RungeKutta.lean`)

### 2.2 Implicit Runge–Kutta Methods
- [x] **Definition**: Implicit RK methods (implicit Euler, implicit midpoint) (`OpenMath/RungeKutta.lean`)
- [x] **Definition**: Stability function R(z) for 1-stage RK methods (`OpenMath/RungeKutta.lean`)
- [x] **Theorem**: A-stability of implicit Euler and implicit midpoint (`OpenMath/RungeKutta.lean`)
- [x] **Theorem**: Forward Euler (RK) is NOT A-stable (`OpenMath/RungeKutta.lean`)
- [x] **Example**: Gauss–Legendre 2-stage method — Butcher tableau, consistency, not explicit (`OpenMath/RungeKutta.lean`)
- [x] **Definition**: GL2 stability function R(z) = (1+z/2+z²/12)/(1-z/2+z²/12) (`OpenMath/RungeKutta.lean`)
- [x] **Theorem**: A-stability of GL2 method (`gl2_aStable`) (`OpenMath/RungeKutta.lean`)
- [x] **Theorem**: GL2 has order 4 (`rkGaussLegendre2_order4`) (`OpenMath/RungeKutta.lean`)

## Chapter 3: Stiff Equations

- [ ] **Definition**: Stiffness
- [x] **Theorem**: A-stability of backward Euler and trapezoidal rule (`OpenMath/MultistepMethods.lean`)
- [x] **Theorem**: Forward Euler is not A-stable (`OpenMath/MultistepMethods.lean`)
- [~] **Theorem**: Dahlquist's second barrier (A-stable + zero-stable ⟹ order ≤ 2) — 1 sorry remains (`order_ge_three_not_aStable_core`)
- [x] **Counterexample**: A-stable order-3 method without zero-stability (`dahlquistCounterexample`)

## Current Target

**Next: Close remaining sorrys or advance to new material**

Options:
- Close `stableRecurrence_of_zeroStable` (1 sorry in DahlquistEquivalence.lean): needs general solution theory for linear recurrences (companion matrix, eigenvalue analysis). Key step: show solutions of ∑ α_j y_{n+j} = 0 are linear combinations of generalized eigensolutions ξ^n, n·ξ^n, etc.
- Close remaining Dahlquist barrier sorrys in MultistepMethods.lean (2 sorrys: `hasDerivAt_Gtilde_one`, `continuousOn_Gtilde_closedBall`): requires removable singularity theory, blocked by Mathlib gaps.
- Add higher-order Gauss–Legendre methods (3-stage, order 6) or collocation RK framework.
- Formalize Chapter 4: stiff equations — L-stability, algebraic stability, stiff decay.
