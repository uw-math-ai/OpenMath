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
- [x] **Definition**: General linear multistep method (Adams–Bashforth, Adams–Moulton) (`OpenMath/MultistepMethods.lean`)
- [x] **Example**: Adams–Moulton 2-step method — consistency, order 3, implicit, zero-stable (`OpenMath/MultistepMethods.lean`)
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
- [x] **Definition**: Padé approximants and stability functions (`OpenMath/Pade.lean`)
- [~] **Theorem 352C/352D**: Padé recurrence infrastructure (`OpenMath/Pade.lean`)
  - [x] Added general `padeP`, `padeQ`, `padeR` families
  - [x] Proved diagonal symmetry and specialization lemmas `padeQ_diagonal_eq_padeP_neg`, `padeP_one_one`, `padeQ_two_two`
  - [x] Proved pair packaging theorem `padePQ_pair_recurrence`
  - [ ] Remaining coefficient recurrences `padeQ_succ_left`, `padeP_succ_right` need a clean factorial-sum proof
- [x] **Definition**: Embedded RK pairs (`OpenMath/EmbeddedRK.lean`)
- [x] **Definition**: Stiff accuracy (`OpenMath/StiffAccuracy.lean`)
- [x] **Theorem 342C**: Gaussian quadrature order-condition equivalence (`OpenMath/Collocation.lean`)
  - [x] Defined `SatisfiesE (η, ζ)` from equation (321c)
  - [x] Proved `B(2s) ∧ C(s) ⇒ E(s,s)` (342m) and `B(2s) ∧ D(s) ⇒ E(s,s)` (342o)
  - [x] Proved `B(2s) ∧ E(s,s) ⇒ C(s)` (342n, requires distinct nodes + nonzero weights) via Vandermonde uniqueness
  - [x] Proved `B(2s) ∧ E(s,s) ⇒ D(s)` (342p, requires distinct nodes) via Vandermonde uniqueness
  - [ ] Remaining implications (342j, 342k, 342l) require rooted tree infrastructure from thm:301A
- [~] **Theorem 301A**: rooted-tree infrastructure (`OpenMath/RootedTree.lean`)
  - [x] Defined `BTree`
  - [x] Defined `order`, `symmetry`, `density`
  - [x] Added basic examples of orders `1` through `3`
  - [ ] Upgrade child representation from `List` fallback to the intended unordered multiplicity model

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

## Current Target

**BDF family complete (BDF1–6: definitions, consistency, order, zero-stability, convergence).**

Next targets:
1. **Theorem 352D** — finish the factorial-sum proofs of `padeQ_succ_left` and `padeP_succ_right` in `OpenMath/Pade.lean`
2. **Theorem 301A** — finish rooted-tree infrastructure by replacing the `List` fallback with an unordered multiplicity model and proving the final recursion formulas
3. **Theorem 342C** remaining implications (342j, 342k, 342l) — require tree infrastructure from 301A

## Sorry locations
None — the project is sorry-free as of cycle 96.

## Recent git history
b696343 Finish BDF5 zero-stability proof
e9b65f8 cycle 90: close all sorrys in MultistepMethods.lean
2b88e99 cycle 89: close hQ1pp
0ac9f11 cycle 87: decompose dahlquist barrier derivative proof
64c2d11 cycle 85: restructure Gtilde derivative proof
