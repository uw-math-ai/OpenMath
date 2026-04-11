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
- [x] **Definition**: Order of a linear multistep method (`OpenMath/MultistepMethods.lean`)
- [x] **Theorem**: Zero-stability of multistep methods (`OpenMath/MultistepMethods.lean`)
- [x] **Definition**: A-stability of multistep methods (`OpenMath/MultistepMethods.lean`)
- [~] **Theorem**: Dahlquist's second barrier — A-stable ⟹ order ≤ 2 (stated, proof sorry)
- [ ] **Theorem**: Dahlquist equivalence theorem (consistency + stability ⟺ convergence)

### 1.3 Order and Convergence
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
- [x] **Theorem**: A-stability of backward Euler and trapezoidal rule (`OpenMath/MultistepMethods.lean`)
- [x] **Theorem**: Forward Euler is not A-stable (`OpenMath/MultistepMethods.lean`)
- [~] **Theorem**: Dahlquist's second barrier (A-stable methods have order ≤ 2) — stated in `MultistepMethods.lean`

## Current Target

**Next: Runge–Kutta methods (Chapter 2)**

Define Butcher tableaux, explicit RK methods, and prove order conditions for classical RK4.
Alternative: formalize convergence definition and Dahlquist equivalence theorem.
