# Formalization Plan

## Textbook
*A First Course in the Numerical Analysis of Differential Equations* — Arieh Iserles (Cambridge, 2nd edition).

This plan follows Iserles' chapter numbering exactly. Theorem labels of the form
`NMS_n` (e.g. `212A`, `351B`, `358A`) are Iserles' own §N.M.S enumeration and are
preserved verbatim.

## Status Key
- `[x]` Formalized (no live `sorry`)
- `[ ]` Not started
- `[~]` In progress
- `[-]` Blocked or deferred — see **Blockers** at the end

## Status Summary

- **Part I, Chapters 1–4 (ODE theory and stability):** essentially closed.
  Open items are blockers, not scheduled work.
- **Part I, Chapter 5 (Geometric integration):** symmetry/adjoint/reflected
  foundations exist; symplectic / Hamiltonian / Verlet content is **the
  active frontier**.
- **Part I, Chapter 6 (Error control):** embedded-RK infrastructure and two
  embedded pairs exist; Milne device, Fehlberg, DOPRI, and step control are open.
- **Part I, Chapter 7 (Nonlinear algebraic systems):** unstarted.
- **Part II (Chs 8–11) and Part III (Chs 12–17):** unstarted, scoped here as
  stubs so the planner has visible forward direction.

---

## Chapter 1: Euler's Method and Beyond

### 1.1 ODEs and the Lipschitz condition
- [x] **Definition 110A**: Lipschitz condition in second variable (`OpenMath/PicardLindelof.lean`)
- [x] **Theorem 110C**: Picard–Lindelöf existence and uniqueness (`OpenMath/PicardLindelof.lean`)
  - [x] Uniqueness via Gronwall (`PicardLindelof.unique`)
  - [x] Continuous dependence on initial data (`PicardLindelof.continuous_dependence`)
  - [x] Perturbation bound (`PicardLindelof.perturbation_bound`)
  - [x] Combined `exists_unique`
  - [x] Existence via bisection induction (`PicardLindelof.exists_solution`)

### 1.2 Euler's method
- [x] **Theorem 212A**: Global truncation error bound for Euler (`OpenMath/Basic.lean`)
- [x] **Theorem 213A**: Convergence of Euler with order 1 (`OpenMath/EulerConvergence.lean`)

### 1.3 The trapezoidal rule
- [x] Trapezoidal rule formalized as the 1-step Adams–Moulton method; A-stable;
  error constant `−1/12` (cross-ref Ch 2 and Ch 4)

### 1.4 The theta method
- [ ] **Definition**: θ-method `y_{n+1} = y_n + h(θ f_n + (1−θ) f_{n+1})` as a
  one-parameter family unifying forward Euler (θ=1), backward Euler (θ=0), and
  trapezoidal (θ=1/2) (new file `OpenMath/ThetaMethod.lean`)
- [ ] **Theorem**: θ-method is consistent (`OpenMath/ThetaMethod.lean`)
- [ ] **Theorem**: θ-method has order 1 in general, order 2 iff θ = 1/2
  (`OpenMath/ThetaMethod.lean`)
- [ ] **Theorem**: θ-method A-stability domain — A-stable iff θ ≤ 1/2
  (`OpenMath/ThetaMethod.lean`)
- [ ] **Theorem**: θ-method recovers forward Euler / backward Euler / trapezoidal
  at θ ∈ {1, 0, 1/2} (`OpenMath/ThetaMethod.lean`)

---

## Chapter 2: Multistep Methods

### 2.1 The Adams method
- [x] **General LMM infrastructure** (`OpenMath/MultistepMethods.lean`)
- [x] **Adams–Bashforth and Adams–Moulton families** (`OpenMath/AdamsMethods.lean`)
- [x] **Adams convergence corollaries** for AB2–AB6 and AM2–AM6: consistency,
  order, zero-stability, and convergence via Dahlquist
  (`OpenMath/AdamsMethods.lean`, `OpenMath/DahlquistEquivalence.lean`)
- [x] **Reusable Adams zero-stability helper** `adams_zeroStable_of_rhoC_pow_mul`
  (`OpenMath/AdamsMethods.lean`, cycle 389)

### 2.2 Order and convergence of multistep methods
- [x] **Consistency, order, zero-stability** definitions (`OpenMath/MultistepMethods.lean`)
- [x] **Error constants** `LMM.errorConstant`: forward Euler `1/2`, backward Euler `−1/2`,
  trapezoidal `−1/12`, AB2 `5/12`, AM2 `−1/24`, …; AB2–AB6 strictly positive,
  AM2–AM6 strictly negative (`OpenMath/AdamsMethods.lean`, cycle 388)
- [x] **BDF error constants** computed: BDF2 `−2/9`, BDF3 `−3/22`, BDF4 `−12/125`,
  BDF5 `−10/137`, BDF6 `−20/343`, BDF7 `−35/726` (cycles 392–393)
- [x] **Truncation operator infrastructure** (`OpenMath/LMMTruncationOp.lean`,
  cycles 394–399): definition `LMM.truncationOp`, monomial / polynomial / shifted /
  Taylor-remainder identities, and the uniform local-truncation-error bridge
  `truncationOp_smooth_local_truncation_error`
- [x] **Discrete Gronwall for finite horizons** `discrete_gronwall_exp_horizon`
  (`OpenMath/LMMTruncationOp.lean`)
- [x] **Theorem (Dahlquist equivalence)**: consistency + zero-stability ⟺
  convergence (`OpenMath/DahlquistEquivalence.lean`); includes spectral bound
  via generalized eigenspace decomposition (`OpenMath/SpectralBound.lean`)
- [x] **One-step convergence theorem** (`OpenMath/OneStepConvergence.lean`)

#### Per-step quantitative convergence chains (covered)
The following per-step `OpenMath/LMM*Convergence.lean` files each carry the
trajectory predicate, residual unfolding, one-step Lipschitz/error bound,
pointwise local-truncation-error bound, and finite-horizon global error
bound for one specific scheme:

- Forward Euler (`OpenMath/LMMTruncationOp.lean`)
- AB2 through AB13 (scalar and vector) — `OpenMath/LMMAB{2,…,13}{,Vector}Convergence.lean`
- AM2 through AM12 (scalar and vector) — `OpenMath/LMMAM{2,…,12}{,Vector}Convergence.lean`
- BDF1 through BDF3 (scalar and vector, full global theorem) —
  `OpenMath/LMMBDF{1,2,3}{,Vector}Convergence.lean`
- BDF4 through BDF7 (scalar and vector truncation chains; global theorem deferred for
  BDF4–BDF6, impossible for zero-unstable BDF7) —
  `OpenMath/LMMBDF{4,5,6,7}{,Vector}Convergence.lean`

> **Cap:** The per-step enumeration is closed. Do **not** add AB14, AM13,
> or BDF8 quantitative convergence chains. Once the Dahlquist equivalence
> (`OpenMath/DahlquistEquivalence.lean`) is in place, qualitative convergence
> for any consistent zero-stable method follows; further quantitative
> per-step files repeat the same template and are not in Iserles.

### 2.3 Backward differentiation formulae
- [x] **BDF1–BDF2** (`OpenMath/MultistepMethods.lean`)
- [x] **BDF3–BDF6**: consistency, order = step count, zero-stability
  (`OpenMath/MultistepMethods.lean`, `OpenMath/BDF.lean`)
- [x] **BDF5 / BDF6 zero-stability** via `w = 1/ξ` substitution + `nlinarith`,
  unit-root reductions for BDF6
- [x] **BDF7 infrastructure**: definition, consistency, order 7, characteristic
  factorization (`OpenMath/MultistepMethods.lean`, cycle 377)
- [x] **BDF7 zero-instability** via exact algebraic root certificate for the
  Cayley-transformed sextic (cycle 379)
- [x] **BDF7 non-convergence** via Dahlquist equivalence (`OpenMath/DahlquistEquivalence.lean`)
- [x] **BDF4–BDF6 convergence** via Dahlquist equivalence

---

## Chapter 3: Runge–Kutta Methods

### 3.0 Foundations: rooted trees and order conditions
- [x] **Theorem 301A**: rooted-tree infrastructure (`OpenMath/RootedTree.lean`):
  `BTree`, `order`, `symmetry`, `density`, examples through order 5,
  `thm_301A_order1` … `thm_301A_order5`
- [x] **Order conditions** through order 5 (`OpenMath/OrderConditions.lean`,
  `OpenMath/RootedTree.lean`)

### 3.1 Gaussian quadrature
- [x] **Legendre / shifted Legendre infrastructure** (`OpenMath/Legendre.lean`,
  `OpenMath/LegendreHelpers.lean`, `OpenMath/ShiftedLegendreDivision.lean`)
- [x] **Theorem 342C**: Gaussian quadrature order-condition equivalence
  (`OpenMath/Collocation.lean`)
  - 342j (`G(p) ⇒ B(p)`), 342k (`G(2n) ⇒ E(n,n)`), 342l (`B(2n) ∧ C(n) ∧ D(n) ⇒ G(2n)`)
  - 342m / 342n / 342o / 342p (`B(2s) ∧ C(s)/D(s) ⇔ E(s,s)` bidirections)

### 3.2 Explicit Runge–Kutta schemes
- [x] **Butcher tableau** (`OpenMath/RungeKutta.lean`, `OpenMath/ExplicitRK.lean`)
- [x] **Examples**: forward Euler / explicit midpoint / Heun / classical RK4 as RK,
  consistency, order conditions through order 4
- [x] **Theorem (order barrier)**: s-stage explicit ⟹ order ≤ s for s ≤ 4
  (`OpenMath/OrderBarriers.lean`)
- [x] **Theorem**: explicit methods cannot satisfy `C(2)` with distinct nodes
  (`OpenMath/OrderBarriers.lean`)

### 3.3 Implicit Runge–Kutta schemes
- [x] **Implicit Euler / implicit midpoint** (`OpenMath/RungeKutta.lean`)
- [x] **Stability function `R(z)`** for 1-stage RK (`OpenMath/RungeKutta.lean`)
- [x] **A-stability**: implicit Euler / implicit midpoint A-stable; forward Euler not
- [x] **Gauss–Legendre 2-stage** — order 4, A-stable (`OpenMath/RungeKutta.lean`)
- [x] **Gauss–Legendre 3-stage** — order ≥ 5, `B(6)`, `D(3)` (`OpenMath/GaussLegendre3.lean`)
- [x] **Radau IA 2-stage / 3-stage** (`OpenMath/RadauIA2.lean`, `OpenMath/RadauIA3.lean`)
- [x] **Radau IIA 3-stage** — order ≥ 5, algebraic stability (`OpenMath/RadauIIA3.lean`)
- [x] **SDIRK2 / SDIRK3** (`OpenMath/SDIRK.lean`, `OpenMath/SDIRK3.lean`)
- [x] **Lobatto IIIA / IIIB / IIIC, 2-stage and 3-stage**
  (`OpenMath/LobattoIIIA{,3}.lean`, `OpenMath/LobattoIIIB{,3}.lean`,
  `OpenMath/LobattoIIIC{,3}.lean`)

### 3.4 Collocation and IRK
- [x] **`B(p)`, `C(q)`, `D(r)` simplifying assumptions** (`OpenMath/Collocation.lean`)
- [x] **Theorem**: `B(p) ∧ C(q) ⟹ order ≥ p`, plus assorted combinations
- [x] **Symmetric methods, Nørsett's even-order theorem**
  (symmetric + order ≥ 3 ⟹ order ≥ 4) (`OpenMath/Symmetry.lean`)
- [x] **Self-adjoint / adjoint pair** (`OpenMath/Adjoint.lean`)
- [x] **Reflected RK tableau** `(1−c, b−A, b)` and transfer of `B`, `C`, `D`, `E`
  (`OpenMath/ReflectedMethods.lean`)
- [x] **`CollocationBN` infrastructure** (`OpenMath/CollocationBN.lean`)

### 3.5 Stability theory of RK methods (Padé, order stars, AN/BN/algebraic)
- [x] **Theorem 351B**: A-stability criterion via E-function (`OpenMath/AStabilityCriterion.lean`)
- [x] **Padé approximants and stability functions** (`OpenMath/Pade.lean`)
- [x] **Theorems 352C / 352D**: Padé recurrence — `padeP`, `padeQ`, `padeR` families,
  diagonal symmetry, specialization, pair packaging, coefficient recurrences
- [x] **Theorem 353A**: Padé approximation order (`OpenMath/PadeOrder.lean` /
  `OpenMath/PadeAsymptotics.lean`, `OpenMath/PadeUniqueness.lean`)
- [x] **Theorems 355C / 355D / 355E**: order-arrow trajectory bookkeeping,
  endpoint data, no-escape, concrete wrappers
  (`OpenMath/OrderStars.lean`, `OpenMath/PadeOrderStars.lean`)
- [x] **Theorem 355G**: Ehle barrier / Padé wedge boundary, with separate honest
  downstream `EhleBarrierInput` and concrete Padé constructor
- [x] **Theorem 356C**: AN-stability ⇒ algebraic stability (`OpenMath/ANStability.lean`)
- [x] **Theorem 357C**: algebraic stability ⇒ BN-stability (`OpenMath/BNStability.lean`)
- [x] **Theorem 357D**: BN-stability ⇒ AN-stability for irreducible non-confluent
  methods (`OpenMath/BNImpliesAN.lean`)
- [x] **Theorem 358A**: algebraic-stability characterization of collocation
  methods (`OpenMath/CollocationAlgStability.lean`); both directions
- [x] **Theorem 359B (Radau IIA family)**: collocation + Radau IIA nodes ⇒
  algebraically stable (`OpenMath/CollocationFamilies.lean`, cycle 374)
- [x] **Theorem 359C**: classical collocation families (Gauss–Legendre, Radau I/θ=1)
  algebraically stable; concrete corollaries
  `rkGaussLegendre{2,3}_algStable_via_358A` (`OpenMath/CollocationFamilies.lean`)
- [-] **Theorem 359B (Radau IA side)**: blocked — see Blockers
- [x] **§3.5.10 packaging corollaries**: family-level BN-stability for GL, Radau IIA
  collocation (`OpenMath/CollocationFamilies.lean`, cycle 376)
- [-] **Theorem 359D**: pending — needs Iserles §3.5.10 source statement (see Blockers)

---

## Chapter 4: Stiff Equations

### 4.1 What are stiff ODEs?
- [x] **Definition**: stiffness (`OpenMath/Stiffness.lean`)

### 4.2 Linear stability domain and A-stability
- [x] **Definition**: A-stability of multistep methods (`OpenMath/MultistepMethods.lean`)
- [x] **A-stability ⇒ roots of `ρ` in unit disk** (`OpenMath/MultistepMethods.lean`)

### 4.3 A-stability of Runge–Kutta methods
- [x] Cross-ref Ch 3.5 (Padé, order stars, AN/BN/algebraic stability)
- [x] **Definition**: stiff accuracy (`OpenMath/StiffAccuracy.lean`); concrete certs
  for implicit Euler, SDIRK2/3, Radau IIA2/3, Lobatto IIIA2/3, Lobatto IIIC2/3
- [x] **Definition**: L-stability (`OpenMath/StiffEquations.lean`); concrete certs
  for backward Euler, Radau IIA, SDIRK2, SDIRK3
  (`OpenMath/StiffEquations.lean`, `OpenMath/SDIRK.lean`, `OpenMath/SDIRK3.lean`)

### 4.4 A-stability of multistep methods (Dahlquist barriers)
- [x] **A-stability of backward Euler and trapezoidal rule** (`OpenMath/MultistepMethods.lean`)
- [x] **Forward Euler is not A-stable** (`OpenMath/MultistepMethods.lean`)
- [x] **Theorem (Dahlquist's second barrier)**: A-stable + zero-stable ⟹ order ≤ 2
  (`OpenMath/MultistepMethods.lean`); 9 supporting lemmas including
  `E_nonneg_re`, `re_inv_exp_sub_one`, removable-singularity Gtilde proof,
  and `dahlquistCounterexample` (order-3 A-stable but not zero-stable)

### 4.5 BDF methods (stability-side; defined in §2.3)
- [x] **A(α)-stability sector**: definition, monotonicity, A-stable ↔ A(π/2)-stable
  (`OpenMath/BDF.lean`)
- [x] **BDF3–6 are NOT A-stable** via Dahlquist barrier (`OpenMath/BDF.lean`)
- [x] **BDF4 stable-block quadratic Lyapunov certificate and forced one-step
  recurrence** (`OpenMath/BDFQuadraticLyapunov.lean`): `bdf4RecDefect`,
  `bdf4LyapU`, stable coordinates, `bdf4CubicQuad`, exact homogeneous decrease,
  coercive bounds, `bdf4StableEnergy`, `bdf4LyapW`, forced energy/defect
  recurrences, `bdf4_eIdx4_le_W_add_defect`,
  `bdf4LyapW_one_step_error_bound` (cycles 458 / 488 / 489)
- [-] **BDF4 / BDF5 / BDF6 global Lyapunov / quantitative convergence**: deferred
  by spectral obstruction (see Blockers)

---

## Chapter 5: Geometric Numerical Integration

> **This is the active frontier.** Symmetry / adjoint / reflected foundations
> already exist in Ch 3.4; the symplectic / Hamiltonian / Verlet content below
> is open and is what cycle 491+ should pursue.

### 5.1 Between quality and quantity
- Motivational. No formal items.

### 5.2 Monotone equations and algebraic stability
- [x] Cross-reference Ch 3.5: 356C / 357C / 357D / 358A / 359B / 359C and the
  GL / Radau IIA / Lobatto IIIC concrete algebraic-stability certificates.

### 5.3 From here to eternity (long-time behavior; Hamiltonian systems)
- [ ] **Definition**: Hamiltonian function `H : Fin (2*d) → ℝ` (or `H : EuclideanSpace ℝ (Fin (2*d)) → ℝ`),
  separable form `H(q,p) = T(p) + V(q)` (new file `OpenMath/Hamiltonian.lean`)
- [ ] **Definition**: Hamiltonian flow ODE `q' = ∂H/∂p`, `p' = −∂H/∂q`
  (`OpenMath/Hamiltonian.lean`)
- [ ] **Theorem**: the Hamiltonian is a first integral — `H` is constant along
  Hamiltonian-flow trajectories (`OpenMath/Hamiltonian.lean`)

### 5.4 Symplectic methods
- [ ] **Definition**: canonical symplectic 2-form / matrix
  `J = [[0, I_d], [−I_d, 0]]` on `ℝ^{2d}` (new file `OpenMath/Symplectic.lean`)
- [ ] **Definition**: `IsSymplectic φ` for a smooth `φ : ℝ^{2d} → ℝ^{2d}` via
  `(Dφ(x))ᵀ · J · (Dφ(x)) = J` for all `x` (`OpenMath/Symplectic.lean`)
- [ ] **Lemma**: composition of symplectic maps is symplectic
  (`OpenMath/Symplectic.lean`)
- [ ] **Theorem**: the Hamiltonian flow is symplectic (`OpenMath/Symplectic.lean`)
- [ ] **Definition**: symplectic Euler scheme for separable Hamiltonians:
  `q_{n+1} = q_n + h ∂H/∂p(q_n, p_{n+1})`, `p_{n+1} = p_n − h ∂H/∂q(q_n, p_{n+1})`
  (new file `OpenMath/SymplecticEuler.lean`)
- [ ] **Theorem**: symplectic Euler is symplectic (`OpenMath/SymplecticEuler.lean`)
- [x] Cross-reference: symmetric / self-adjoint RK methods (`OpenMath/Symmetry.lean`,
  `OpenMath/Adjoint.lean`); reflected tableau (`OpenMath/ReflectedMethods.lean`).

### 5.5 The symplectic Verlet (Störmer–Verlet) method
- [ ] **Definition**: Störmer–Verlet method for separable Hamiltonians (new file
  `OpenMath/Verlet.lean`)
- [ ] **Theorem**: Störmer–Verlet is symplectic and time-reversible
  (`OpenMath/Verlet.lean`)
- [ ] **Theorem**: Störmer–Verlet has order 2 (`OpenMath/Verlet.lean`)

---

## Chapter 6: Error Control

### 6.1 Numerical software vs numerical mathematics
- Motivational. No formal items.

### 6.2 The Milne device
- [ ] **Definition**: Milne device for matched predictor–corrector multistep pairs
  (e.g. AB(p)/AM(p)) — local error estimate from `(y* − y) / (1 − error-constant ratio)`
  (new file `OpenMath/MilneDevice.lean`)
- [ ] **Theorem**: Milne estimate is asymptotically correct as `h → 0` for
  matched-order pairs (`OpenMath/MilneDevice.lean`)

### 6.3 Embedded Runge–Kutta methods
- [x] **`EmbeddedRKPair` structure**, `IsConsistent`, `IsExplicit`, `errorWeights`,
  `HasFSAL`, weight-sum identities (`OpenMath/EmbeddedRK.lean`)
- [x] **Heun–Euler 2(1)**: explicit, consistent, main order 2, embed order 1,
  error-weight closure (`OpenMath/EmbeddedRK.lean`)
- [x] **Bogacki–Shampine 3(2)**: explicit, consistent, main order 3, embed order 2,
  stiffly accurate, FSAL, non-negative weights, `B(3)`, `C(1)` (`OpenMath/EmbeddedRK.lean`)
- [ ] **Fehlberg 4(5) (RKF45)** embedded pair: tableau, consistency, orders 4 and 5,
  error-weight closure (extends `OpenMath/EmbeddedRK.lean` or `OpenMath/RKF45.lean`)
- [ ] **Dormand–Prince 5(4) (DOPRI5)** embedded pair: tableau, consistency,
  orders 5 and 4, FSAL, error-weight closure (extends `OpenMath/EmbeddedRK.lean`
  or `OpenMath/DOPRI5.lean`)
- [ ] **Theorem**: error-weight estimate `h · Σᵢ (bᵢ − b̂ᵢ) kᵢ` agrees with the
  true LTE difference of the two embedded methods up to higher-order terms
- [ ] **Algorithm**: step-size adaptation via local error estimate (PI controller
  or proportional rule)

---

## Chapter 7: Nonlinear Algebraic Systems

### 7.1 Functional iteration
- [ ] **Definition**: functional iteration in `ℝᵈ`; contraction-mapping predicate
  (likely thin wrapper over Mathlib's `ContractingWith`) — new file
  `OpenMath/FunctionalIteration.lean`
- [ ] **Theorem**: Banach fixed-point theorem for contractions on a complete
  metric space (probably re-export of `ContractingWith.fixedPoint_unique` etc.)
- [ ] **Theorem**: functional iteration on the implicit RK / implicit LMM
  fixed-point equation converges for `h · L · |a-coefficient bound| < 1`
  (`OpenMath/FunctionalIteration.lean`)

### 7.2 The Newton–Raphson method
- [ ] **Definition**: Newton–Raphson iteration in `ℝᵈ` (`OpenMath/Newton.lean`)
- [ ] **Theorem**: quadratic convergence near a simple root with Lipschitz
  Jacobian (`OpenMath/Newton.lean`)
- [ ] **Definition**: modified Newton (frozen Jacobian) (`OpenMath/Newton.lean`)
- [ ] **Theorem**: linear convergence of modified Newton when the Jacobian is
  refreshed sufficiently often (`OpenMath/Newton.lean`)

### 7.3 Starting and stopping the iteration
- [ ] **Definitions**: residual-based and increment-based stopping criteria
  (`OpenMath/Newton.lean`)

---

## Part II: Numerical Algebra (Chapters 8–11)

> All chapters in Part II are unstarted. Items below are concrete `[ ]`
> targets; the planner should reach for them only after Chs 5–7 close (or
> if all of Chs 5–7 have hard blockers).

### Chapter 8: Direct methods for linear algebraic systems
- [ ] **Definition**: LU factorization of a square matrix `A = L · U`
  (new file `OpenMath/LU.lean`)
- [ ] **Theorem**: existence and uniqueness of LU when every leading principal
  minor of `A` is non-singular (`OpenMath/LU.lean`)
- [ ] **Definition**: forward and backward substitution (`OpenMath/LU.lean`)
- [ ] **Theorem**: forward / backward substitution solves `L · x = b` /
  `U · x = b` in `O(d²)` operations (`OpenMath/LU.lean`)
- [ ] **Definition**: partial pivoting; permutation matrix `P` so that
  `P · A = L · U` (`OpenMath/LU.lean`)
- [ ] **Theorem**: every non-singular `A` admits an LU factorization with
  partial pivoting (`OpenMath/LU.lean`)
- [ ] **Definition**: Cholesky factorization `A = L · Lᵀ` for symmetric
  positive-definite `A` (new file `OpenMath/Cholesky.lean`)
- [ ] **Theorem**: existence and uniqueness of Cholesky for SPD `A`
  (`OpenMath/Cholesky.lean`)
- [ ] **Definition**: banded matrix; bandwidth (`OpenMath/LU.lean` or new
  `OpenMath/Banded.lean`)
- [ ] **Theorem**: LU of a banded matrix preserves bandwidth

### Chapter 9: Iterative methods for sparse linear algebraic systems
- [ ] **Definition**: linear one-step stationary iteration
  `x_{n+1} = H · x_n + v` (new file `OpenMath/StationaryIteration.lean`)
- [ ] **Theorem**: convergence iff spectral radius `ρ(H) < 1`
  (`OpenMath/StationaryIteration.lean`)
- [ ] **Theorem**: convergence rate is geometric with ratio `ρ(H)`
- [ ] **Definitions**: Jacobi, Gauss–Seidel, SOR iterations from a matrix
  splitting `A = L + D + U` (new file `OpenMath/JacobiSOR.lean`)
- [ ] **Theorem**: Jacobi converges for strictly diagonally dominant `A`
  (`OpenMath/JacobiSOR.lean`)
- [ ] **Theorem**: Gauss–Seidel converges for SPD `A` (`OpenMath/JacobiSOR.lean`)
- [ ] **Theorem (Ostrowski–Reich)**: SOR converges for SPD `A` iff
  `0 < ω < 2` (`OpenMath/JacobiSOR.lean`)
- [ ] **Theorem**: optimal SOR parameter `ω*` for the discrete Poisson
  matrix (cross-ref Ch 15) (`OpenMath/JacobiSOR.lean`)

### Chapter 10: The conjugate gradient method
- [ ] **Definition**: Krylov subspace `K_n(A, r₀)` (new file
  `OpenMath/Krylov.lean`)
- [ ] **Definition**: conjugate gradient iteration on SPD systems
  (new file `OpenMath/ConjugateGradient.lean`)
- [ ] **Theorem**: CG residuals are mutually `A`-orthogonal
  (`OpenMath/ConjugateGradient.lean`)
- [ ] **Theorem**: CG terminates in at most `d` iterations in exact
  arithmetic (`OpenMath/ConjugateGradient.lean`)
- [ ] **Theorem**: CG error bound via condition number
  `‖x_n − x*‖_A ≤ 2 · ((√κ − 1)/(√κ + 1))ⁿ · ‖x₀ − x*‖_A`
  (`OpenMath/ConjugateGradient.lean`)
- [ ] **Definition**: preconditioned CG (`OpenMath/ConjugateGradient.lean`)
- [ ] **Definition**: Jacobi preconditioner; incomplete-Cholesky
  preconditioner (`OpenMath/Preconditioners.lean`)

### Chapter 11: Classical iterative methods for nonsymmetric systems
- [ ] **Definition**: GMRES iteration (Arnoldi-based) on general non-singular
  `A` (new file `OpenMath/GMRES.lean`)
- [ ] **Theorem**: GMRES residual minimization in the Krylov subspace
  (`OpenMath/GMRES.lean`)
- [ ] **Theorem**: GMRES terminates in at most `d` iterations (exact
  arithmetic) (`OpenMath/GMRES.lean`)
- [ ] **Definition**: BiCGStab iteration (`OpenMath/BiCGStab.lean`)
- [ ] **Theorem**: BiCGStab convergence on a model problem
  (`OpenMath/BiCGStab.lean`)

---

## Part III: Partial Differential Equations (Chapters 12–17)

> Items below are concrete `[ ]` targets. Some Mathlib infrastructure (Sobolev
> spaces, weak derivatives) may need to be vendored or imported on demand.

### Chapter 12: Finite difference schemes for PDEs
- [ ] **Definition**: discrete grid; finite-difference operators (forward,
  backward, central) (new file `OpenMath/FiniteDifference.lean`)
- [ ] **Theorem**: order of the central second-difference operator approximating
  `∂²/∂x²` is 2 (`OpenMath/FiniteDifference.lean`)
- [ ] **Definition**: explicit / implicit / Crank–Nicolson schemes for the
  1D heat equation (new file `OpenMath/HeatEquationFD.lean`)
- [ ] **Theorem**: von Neumann stability analysis for the explicit heat scheme;
  CFL condition `μ = h_t / h_x² ≤ 1/2` (`OpenMath/HeatEquationFD.lean`)
- [ ] **Theorem**: Crank–Nicolson is unconditionally stable
  (`OpenMath/HeatEquationFD.lean`)
- [ ] **Theorem (Lax equivalence)**: for a consistent linear scheme,
  stability ⟺ convergence (new file `OpenMath/LaxEquivalence.lean`)
- [ ] **Definition**: explicit / implicit / leapfrog schemes for the 1D wave
  equation (new file `OpenMath/WaveEquationFD.lean`)
- [ ] **Theorem**: CFL condition for the explicit wave scheme — `c · h_t ≤ h_x`
  (`OpenMath/WaveEquationFD.lean`)

### Chapter 13: The finite element method
- [ ] **Definition**: weak formulation of the 1D Poisson problem
  `−u'' = f` on `(0,1)` with Dirichlet BCs (new file `OpenMath/FEM.lean`)
- [ ] **Definition**: hat-function basis on a uniform mesh (`OpenMath/FEM.lean`)
- [ ] **Definition**: Galerkin discretization (`OpenMath/FEM.lean`)
- [ ] **Theorem (Lax–Milgram)**: existence and uniqueness of weak solution
  for a coercive bounded bilinear form on a Hilbert space
  (likely a wrapper over Mathlib) (`OpenMath/LaxMilgram.lean`)
- [ ] **Theorem (Céa's lemma)**: Galerkin error bounded by best approximation
  error (`OpenMath/FEM.lean`)
- [ ] **Theorem**: piecewise-linear FEM has `O(h²)` energy-norm error
  for `H²` solutions of the 1D Poisson problem (`OpenMath/FEM.lean`)
- [ ] **Definition**: stiffness and mass matrices; their assembly
  (`OpenMath/FEM.lean`)

### Chapter 14: Spectral methods
- [ ] **Definition**: Fourier collocation on a periodic grid (new file
  `OpenMath/FourierSpectral.lean`)
- [ ] **Theorem**: spectral convergence — Fourier truncation error decays faster
  than any algebraic rate for `C^∞` periodic functions
  (`OpenMath/FourierSpectral.lean`)
- [ ] **Definition**: Chebyshev collocation on `[−1, 1]` (new file
  `OpenMath/ChebyshevSpectral.lean`)
- [ ] **Theorem**: Chebyshev spectral derivative matrix construction
  (`OpenMath/ChebyshevSpectral.lean`)

### Chapter 15: Gauss–Seidel and SOR for elliptic PDEs
- [ ] **Definition**: discrete 2D Poisson matrix on a uniform `N × N` grid
  (new file `OpenMath/PoissonDiscrete.lean`)
- [ ] **Theorem**: discrete Poisson matrix is symmetric positive-definite
  (`OpenMath/PoissonDiscrete.lean`)
- [ ] **Theorem**: Jacobi spectral radius for discrete Poisson is
  `cos(π/(N+1))` (`OpenMath/PoissonDiscrete.lean`)
- [ ] **Theorem**: optimal SOR parameter for discrete Poisson is
  `ω* = 2 / (1 + sin(π/(N+1)))` (`OpenMath/PoissonDiscrete.lean`)

### Chapter 16: The multigrid technique
- [ ] **Definition**: restriction and prolongation operators between fine and
  coarse grids (new file `OpenMath/Multigrid.lean`)
- [ ] **Definition**: V-cycle on a hierarchy of grids (`OpenMath/Multigrid.lean`)
- [ ] **Theorem**: smoothing property — Jacobi / Gauss–Seidel reduces
  high-frequency error components (`OpenMath/Multigrid.lean`)
- [ ] **Theorem**: V-cycle convergence rate is bounded independently of
  mesh size for the discrete Poisson problem (`OpenMath/Multigrid.lean`)

### Chapter 17: Fast Poisson solvers
- [ ] **Definition**: discrete Fourier transform (likely re-export from Mathlib)
  (`OpenMath/FastPoisson.lean`)
- [ ] **Theorem**: discrete Poisson on a periodic / Dirichlet rectangle is
  diagonalized by the discrete sine / Fourier transform
  (`OpenMath/FastPoisson.lean`)
- [ ] **Algorithm**: FFT-based Poisson solver in `O(d² log d)`
  (`OpenMath/FastPoisson.lean`)
- [ ] **Definition**: cyclic-reduction Poisson solver for tri-diagonal block
  systems (`OpenMath/CyclicReduction.lean`)

---

## Active Frontier

- **Chapters 1–4 are essentially closed.** The only remaining items are the
  three blockers below and (low priority) the θ-method definition in §1.4.
- **Active work:** Chapter 5 (Geometric Numerical Integration). First three
  files are listed in **Current Target** below.
- **Next after Ch 5:** Chapter 6 missing items (Milne device, Fehlberg 4(5),
  DOPRI 5(4), step-size adaptation), then Chapter 7 (functional iteration,
  Newton–Raphson).

---

## Current Target

**Highest priority for the next planner cycle: start Chapter 5 (Geometric
Numerical Integration).** Concrete first goals, in order:

1. **`OpenMath/Hamiltonian.lean`** — define a Hamiltonian
   `H : EuclideanSpace ℝ (Fin (2*d)) → ℝ` together with the separable form
   `H(q,p) = T(p) + V(q)`, the Hamiltonian flow ODE
   `q' = ∂H/∂p, p' = −∂H/∂q`, and the energy-conservation theorem
   "`H` is constant along trajectories of the Hamiltonian flow".

2. **`OpenMath/Symplectic.lean`** — define the canonical symplectic matrix
   `J = [[0, I_d], [−I_d, 0]]`, the predicate `IsSymplectic φ` via
   `(Dφ)ᵀ · J · (Dφ) = J`, and prove that composition of symplectic maps
   is symplectic and that the Hamiltonian flow is symplectic.

3. **`OpenMath/SymplecticEuler.lean`** — define the symplectic Euler scheme
   for separable Hamiltonians and prove it is symplectic.

Each file should be sorry-first, batch ~5 Aristotle jobs, sleep 30 minutes,
incorporate proofs that compile against live infrastructure, and close
remaining goals manually. Keep `maxHeartbeats ≤ 200000`.

**If Chapter 5 is unexpectedly blocked,** pivot to **Chapter 6 (Error
Control)**: Fehlberg 4(5) and DOPRI 5(4) extend the existing
`EmbeddedRKPair` infrastructure in `OpenMath/EmbeddedRK.lean` and should
not need new framework. Implement Fehlberg first (extend
`OpenMath/EmbeddedRK.lean`), then DOPRI, then the Milne device for
multistep predictor–corrector pairs.

**If Ch 5 and Ch 6 are both blocked,** pivot to **Chapter 7 (Nonlinear
Algebraic Systems)**: define functional iteration on `ℝᵈ` (thin wrapper
over Mathlib `ContractingWith`) and Newton–Raphson with quadratic
convergence near a simple root.

### Do NOT

- Do **not** add `OpenMath/LMMAB14*Convergence.lean`,
  `OpenMath/LMMAM13*Convergence.lean`, `OpenMath/LMMBDF8*Convergence.lean`,
  or any further per-step LMM convergence chains. The Dahlquist
  equivalence (`OpenMath/DahlquistEquivalence.lean`) already gives
  qualitative convergence of every consistent zero-stable method;
  these per-step quantitative chains repeat the same template, are not
  in Iserles, and were the reason cycles 466–489 stopped advancing the
  textbook.
- Do **not** reopen the BDF4 / BDF5 / BDF6 global-Lyapunov work without
  first updating `.prover-state/issues/bdf4_lyapunov_gap.md`. Cycle 489
  closed the forced-defect one-step recurrence (`bdf4LyapW_one_step_error_bound`);
  the remaining global-Gronwall assembly is the only piece left and is
  bounded — finish it in at most one cycle if you choose to attempt it,
  otherwise leave it deferred.
- Do **not** attempt the Radau IA family-level collocation bridge
  (`IsCollocation ∧ HasRadauIANodes → IsAlgStable`). The
  counterexample in
  `.prover-state/issues/cycle_375_radauIA_collocation_counterexample.md`
  is decisive under the live `IsCollocation` interface.
- Do **not** create new tracked `OpenMath/*.lean` files containing live
  `sorry` outside the active Chapter 5 target. Scratch belongs in
  `.prover-state/`.

---

## Sorry Locations

- No active `sorry`s.

---

## Blockers / Deferred

- **BDF4 / BDF5 / BDF6 global Lyapunov / quantitative convergence** —
  `.prover-state/issues/bdf4_lyapunov_gap.md`. Spectral obstruction:
  the absolute companion matrix of BDF4 has Perron eigenvalue ≈ 2.58, so
  weighted-ℓ¹ Lyapunov sums in error coordinates cannot give the required
  `1 + O(h)` contraction. Cycle 489 landed
  `bdf4LyapW_one_step_error_bound` via a stable-block quadratic Lyapunov
  certificate; the remaining global-Gronwall assembly is open. Same
  obstruction blocks BDF5 and BDF6. BDF7 has no global theorem because it
  is zero-unstable (proved).
- **Theorem 359D (Iserles §3.5.10)** — pending the textbook source
  statement. The cycle 376 §3.5.10 packaging corollaries
  (`OpenMath/CollocationFamilies.lean`) provide a clean BN-stability
  scaffold once the named theorem after 359C is identified.
- **Theorem 359B (Radau IA family bridge)** —
  `.prover-state/issues/cycle_375_radauIA_collocation_counterexample.md`.
  `IsCollocation ∧ HasRadauIANodes → IsAlgStable` is false under the
  live `IsCollocation` interface (`C(s)`): the explicit 2-stage left-Radau
  collocation tableau on nodes `{0, 2/3}` has `M₀₀ = −1/16`. Concrete node
  certificates `rkRadauIA{2,3}_hasRadauIANodes` are landed; a future Radau IA
  family theorem must use the simplifying-assumption shape
  `B(2s−1) ∧ C(s−1) ∧ D(s)` or a different adjoint/transpose interface,
  not the 358A bridge.
