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
- [x] **Theorem**: Consistency conditions for multistep methods (`OpenMath/MultistepMethods.lean`)
- [ ] **Theorem**: Zero-stability of multistep methods
- [ ] **Theorem**: Dahlquist equivalence theorem (consistency + stability ⟺ convergence)

### 1.3 Order and Convergence
- [ ] **Definition**: Order of a numerical method
- [ ] **Theorem**: Convergence theorem for one-step methods

## Chapter 2: Runge–Kutta Methods

### 2.1 Explicit Runge–Kutta Methods
- [ ] **Definition**: Butcher tableau
- [ ] **Theorem**: Order conditions for RK methods
- [ ] **Example**: Classical RK4 method

### 2.2 Implicit Runge–Kutta Methods
- [ ] **Definition**: Implicit RK methods
- [ ] **Theorem**: A-stability of implicit methods

## Chapter 3: Stiff Equations

- [ ] **Definition**: Stiffness
- [ ] **Theorem**: A-stability of the trapezoidal rule
- [ ] **Theorem**: Dahlquist's second barrier (A-stable methods have order ≤ 2)

## Current Target

**Next: Zero-stability of multistep methods**

Define zero-stability (root condition on ρ) and prove that the standard methods (forward Euler, backward Euler, trapezoidal, AB2) are zero-stable. Then state the Dahlquist equivalence theorem.
