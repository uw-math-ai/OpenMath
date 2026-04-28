# Formalization Plan

## Textbook
*Numerical Methods for Ordinary Differential Equations* — J. C. Butcher
(Wiley, 2nd edition, 2008). PDF copy: `.prover-state/textbook/butcher.pdf`;
plain-text extraction: `.prover-state/textbook/butcher.txt`.

This plan follows Butcher's chapter and section numbering exactly. Theorem
labels of the form `§NMS_letter` (e.g. `212A`, `351B`, `358A`) are
Butcher's own §N.M.S enumeration and are preserved verbatim throughout the
codebase.

> **Scope.** Butcher's book covers only ODEs (5 chapters). The earlier
> Iserles-flavoured stubs for linear algebra (LU/Cholesky/CG/GMRES) and PDEs
> (FEM/spectral/multigrid) are out of scope here and have been removed.
> A separate Iserles PDF is kept at `.prover-state/textbook/iserles.pdf`
> for cross-reference only.

## Status Key
- `[x]` Formalized (no live `sorry`)
- `[ ]` Not started
- `[~]` In progress
- `[-]` Blocked or deferred — see **Blockers** at the end

## Status Summary

- **Chapter 1 (Differential and Difference Equations):** §110 (existence /
  uniqueness) closed; §111–§142 mostly background — items below are the
  small remaining hooks.
- **Chapter 2 (Numerical Differential Equation Methods):** §21 (Euler
  analysis) and a large fragment of §24 (LMM survey) closed via the
  Adams / BDF / Dahlquist work. Survey-level items in §25–§27 remain open.
- **Chapter 3 (Runge–Kutta Methods):** §30–§35 essentially closed (rooted
  trees, order conditions, low-order explicit, IRK, A-stability via Padé /
  order stars / AN / BN / algebraic stability). §36 (implementable IRK,
  DIRK, singly implicit) is partially closed (SDIRK2/3). **§37 (Symplectic
  RK), §38 (Algebraic Properties / Butcher group), §39 (Implementation
  Issues) are open** and §38 is **the single biggest remaining gap inside
  Ch 3** — it is Butcher's namesake topic.
- **Chapter 4 (Linear Multistep Methods):** §40–§44 essentially closed
  (Dahlquist equivalence, both Dahlquist barriers, BDF1–BDF7
  consistency / order / zero-stability, BDF7 zero-instability via algebraic
  root certificate, BDF4 stable-block quadratic Lyapunov). §45 (One-Leg
  Methods and G-stability) and §46 (implementation: Nordsieck etc.) are
  open.
- **Chapter 5 (General Linear Methods):** **completely open. This is the
  active frontier and the largest real gap in the codebase.** Butcher's
  Ch 5 unifies RK and LMM under a single multivalue-multistage framework
  and is the part of Butcher's book that does not appear in any other
  ODE textbook.

---

## Chapter 1: Differential and Difference Equations

### §10 Differential Equation Problems
- §100–§107 are example problems (Kepler, MoL, pendulum, chemical
  kinetics, Van der Pol, Lotka–Volterra, rigid body). No formal items;
  these motivate later chapters.

### §11 Differential Equation Theory
- [x] **§110 Existence and uniqueness of solutions** —
  Picard–Lindelöf with Lipschitz right-hand side
  (`OpenMath/PicardLindelof.lean`):
  - [x] Definition: Lipschitz condition in second variable
  - [x] Uniqueness via Gronwall (`PicardLindelof.unique`)
  - [x] Continuous dependence on initial data (`PicardLindelof.continuous_dependence`)
  - [x] Perturbation bound (`PicardLindelof.perturbation_bound`)
  - [x] Combined `exists_unique`
  - [x] Existence via bisection induction (`PicardLindelof.exists_solution`)
- [ ] **§111 Linear systems of differential equations** — matrix
  exponential form `y(x) = exp((x − x₀)A) y₀`. Likely a thin re-export of
  Mathlib `Matrix.exp` (new file `OpenMath/LinearODE.lean`).
- [x] **§112 Stiff differential equations** — informal definition
  (`OpenMath/Stiffness.lean`, `OpenMath/StiffEquations.lean`).

### §12 Further Evolutionary Problems
- §120–§124 are again example problems (many-body gravitation,
  delay equations, problems on the sphere, further Hamiltonians, DAEs).
  No formal items at this level. The Hamiltonian-flow scaffold in
  `OpenMath/Hamiltonian.lean` (cycle 491; `Hamiltonian.energy_conserved`
  for the exact flow) covers §123 background and §370 motivation. It is
  *not* a prerequisite for §370A (which is about the *RK update*
  preserving quadratic invariants of the ODE, not about the exact
  Hamiltonian flow), and it is not on the active formalization path.

### §13 Difference Equation Problems
- §130–§135 are example difference-equation problems (Fibonacci,
  arithmetic-geometric mean, etc.). No formal items.

### §14 Difference Equation Theory
- [ ] **§140–§142 Linear difference equations / constant coefficients /
  powers of matrices** — closed-form solution and Jordan-block bound for
  `‖Aⁿ‖`. Already implicitly used by `OpenMath/SpectralBound.lean` and the
  Dahlquist equivalence proof. **Status: covered by existing infrastructure
  in spirit; no dedicated standalone module.** Optional polish: extract a
  named §142 theorem if it would be useful elsewhere.

---

## Chapter 2: Numerical Differential Equation Methods

### §20 The Euler Method (introduction by example)
- §200–§204 are introductory experiments. No formal items.

### §21 Analysis of the Euler Method
- [x] **§210 Formulation of the Euler method** (`OpenMath/Basic.lean`)
- [x] **§211 Local truncation error** (`OpenMath/Basic.lean`)
- [x] **§212 Global truncation error** (`OpenMath/Basic.lean`,
  `thm_212A_global_truncation_error`)
- [x] **§213 Convergence of the Euler method**
  (`OpenMath/EulerConvergence.lean`)
- [x] **§214 Order of convergence** — Euler has order 1
  (`OpenMath/EulerConvergence.lean`)
- [ ] **§215 Asymptotic error formula** — leading-order term `e_n ≈ h ψ(xₙ)`
  with `ψ` solving the variational ODE. Open.
- [x] **§216 Stability characteristics** — A-stability characterization
  (`OpenMath/MultistepMethods.lean`); forward Euler not A-stable, backward
  Euler A-stable.
- [ ] **§217 Local truncation error estimation** (Richardson; covered in
  §331 below).
- [ ] **§218 Rounding error** — Wilkinson-style backward analysis. Out of
  scope for now.

### §22 Generalizations of the Euler Method
- §220–§226 are a survey introducing RK / LMM / Taylor-series / hybrid
  / implicit methods. The detailed treatments live in §23 / §24 / §25 /
  §26 / §22.5 below.

### §23 Runge–Kutta Methods (introductory survey)
- See full treatment in Chapter 3.

### §24 Linear Multistep Methods (introductory survey)
- See full treatment in Chapter 4. Closed at the survey level via the
  Adams / BDF infrastructure.

### §25 Taylor Series Methods
- [ ] **§250 Introduction to Taylor series methods** — fixed-order
  truncation of the Taylor expansion of `y(x+h)` (new file
  `OpenMath/TaylorSeriesMethod.lean`).
- [ ] **§251 Manipulation of power series** — Cauchy product / power-series
  ring lemmas (likely Mathlib re-export).
- [ ] **§253 Other methods using higher derivatives** — Obreshkov-style
  schemes; brief.
- [ ] **§254 The use of f-derivatives** — the recursion
  `y^(k) = (d/dx)^(k−1) f(x, y)`.

### §26 Hybrid Methods
- §260–§264 are the bridge into Chapter 5 (general linear methods). Open;
  see Chapter 5 below.

### §27 Introduction to Implementation
- §270–§274 cover variable stepsize / interpolation / Kepler / discontinuous
  problems at the survey level. Open and low priority.

---

## Chapter 3: Runge–Kutta Methods

### §30 Preliminaries (rooted trees and Taylor expansion)
- [x] **§300 Rooted trees** — `BTree`, `order`, `symmetry`, `density`,
  examples through order 5 (`OpenMath/RootedTree.lean`); statements
  `thm_301A_order1` … `thm_301A_order5`.
- [x] **§301 Functions on trees** — elementary differentials and weights
  (`OpenMath/RootedTree.lean`, `OpenMath/OrderConditions.lean`).
- [x] **§302–§306 Combinatorial / labelled-tree / differentiation /
  Taylor-theorem infrastructure** — used implicitly by the order-condition
  derivation.

### §31 Order Conditions
- [x] **§310 Elementary differentials** (`OpenMath/OrderConditions.lean`)
- [x] **§311 Taylor expansion of the exact solution**
  (`OpenMath/OrderConditions.lean`)
- [x] **§312 Elementary weights** (`OpenMath/OrderConditions.lean`)
- [x] **§313 Taylor expansion of the approximate solution**
  (`OpenMath/OrderConditions.lean`)
- [x] **§315 Conditions for order** through order 5
  (`OpenMath/OrderConditions.lean`, `OpenMath/RootedTree.lean`)
- [x] **§318 Local truncation error / §319 Global truncation error**
  (`OpenMath/OneStepConvergence.lean`)

### §32 Low Order Explicit Methods
- [x] **Butcher tableau** structure
  (`OpenMath/RungeKutta.lean`, `OpenMath/ExplicitRK.lean`)
- [x] **§320 Examples**: forward Euler / explicit midpoint / Heun /
  classical RK4 with consistency and order conditions through order 4
- [x] **§321 Simplifying assumptions `B(p)`, `C(q)`, `D(r)`**
  (`OpenMath/Collocation.lean`)
- [x] **§322 Methods of order 4** (RK4 family)
- [x] **§324 Order barriers** — s-stage explicit ⟹ order ≤ s for s ≤ 4
  (`OpenMath/OrderBarriers.lean`); explicit methods cannot satisfy `C(2)`
  with distinct nodes
- [ ] **§325–§327 Methods of order 5, 6, and >6** — concrete tableaux
  open. Low priority.

### §33 Runge–Kutta Methods with Error Estimates
- [x] **`EmbeddedRKPair` structure**, `IsConsistent`, `IsExplicit`,
  `errorWeights`, `HasFSAL` (`OpenMath/EmbeddedRK.lean`)
- [x] **Heun–Euler 2(1)**: explicit, consistent, main order 2, embed
  order 1, error-weight closure (`OpenMath/EmbeddedRK.lean`)
- [x] **Bogacki–Shampine 3(2)**: explicit, consistent, main order 3,
  embed order 2, stiffly accurate, FSAL, non-negative weights, `B(3)`,
  `C(1)` (`OpenMath/EmbeddedRK.lean`)
- [x] **§334 Fehlberg 4(5) (RKF45)** embedded pair: tableau, consistency,
  orders 4 and 5, embedding-not-order-5, error-weight closure
  (`OpenMath/EmbeddedRK.lean`: `rkRKF45`, `rkRKF45_main_order5`,
  `rkRKF45_embed_order4`, `rkRKF45_embed_not_order5`,
  `rkRKF45_errorWeights_sum`).
- [ ] **§335 Verner 6(5) / 7(8)** embedded pairs (low priority).
- [ ] **§336 Dormand–Prince 5(4) (DOPRI5)** embedded pair: tableau,
  consistency, orders 5 and 4, FSAL, error-weight closure.

### §34 Implicit Runge–Kutta Methods
- [x] **§340 Introduction**: implicit Euler / implicit midpoint
  (`OpenMath/RungeKutta.lean`)
- [ ] **§341 Solvability of implicit equations** — contraction-mapping
  argument for `h · L · |a-coefficient bound| < 1`. Open (planned thin
  wrapper over Mathlib `ContractingWith`).
- [x] **§342 Methods based on Gaussian quadrature** —
  Legendre / shifted-Legendre infrastructure (`OpenMath/Legendre.lean`,
  `OpenMath/LegendreHelpers.lean`,
  `OpenMath/ShiftedLegendreDivision.lean`,
  `OpenMath/Collocation.lean`); 342C order-condition equivalence (342j /
  342k / 342l / 342m / 342n / 342o / 342p).
- [x] **§342 Concrete: Gauss–Legendre 2-stage / 3-stage**
  (`OpenMath/RungeKutta.lean`, `OpenMath/GaussLegendre3.lean`).
- [x] **§343 Reflected methods** — reflected RK tableau `(1−c, b−A, b)`
  and transfer of `B`, `C`, `D`, `E` (`OpenMath/ReflectedMethods.lean`,
  `OpenMath/Adjoint.lean`); symmetric methods and Nørsett's even-order
  theorem (`OpenMath/Symmetry.lean`).
- [x] **§344 Methods based on Radau and Lobatto quadrature** —
  Radau IA 2/3-stage (`OpenMath/RadauIA{2,3}.lean`), Radau IIA 3-stage
  (`OpenMath/RadauIIA3.lean`), Lobatto IIIA / IIIB / IIIC, 2-stage and
  3-stage (`OpenMath/LobattoIIIA{,3}.lean`,
  `OpenMath/LobattoIIIB{,3}.lean`,
  `OpenMath/LobattoIIIC{,3}.lean`).

### §35 Stability of Implicit Runge–Kutta Methods
- [x] **§350 A-stability, A(α)-stability and L-stability** —
  A-stability of implicit Euler / implicit midpoint
  (`OpenMath/RungeKutta.lean`); L-stability of backward Euler /
  Radau IIA / SDIRK2 / SDIRK3 (`OpenMath/StiffEquations.lean`,
  `OpenMath/SDIRK.lean`, `OpenMath/SDIRK3.lean`); stiff accuracy for
  implicit Euler / SDIRK2/3 / Radau IIA2/3 / Lobatto IIIA2/3 / IIIC2/3
  (`OpenMath/StiffAccuracy.lean`).
- [x] **§351B A-stability criterion** via E-function
  (`OpenMath/AStabilityCriterion.lean`).
- [x] **§352 Padé approximations to the exponential function** —
  Padé recurrence, `padeP` / `padeQ` / `padeR` families, diagonal
  symmetry, specialization, pair packaging, coefficient recurrences
  (`OpenMath/Pade.lean`, `OpenMath/PadeAsymptotics.lean`,
  `OpenMath/PadeUniqueness.lean`); Theorems 352C / 352D.
- [x] **§353 A-stability of Gauss and related methods** — Theorem 353A
  approximation order; concrete corollaries.
- [x] **§354 Order stars** (`OpenMath/OrderStars.lean`,
  `OpenMath/PadeOrderStars.lean`) — Theorems 355C / 355D / 355E
  (trajectory bookkeeping, endpoint data, no-escape, concrete wrappers).
- [x] **§355 Order arrows and the Ehle barrier** — Theorem 355G with
  separate honest downstream `EhleBarrierInput` and concrete Padé
  constructor.
- [x] **§356 AN-stability** — Theorem 356C: AN ⇒ algebraic stability
  (`OpenMath/ANStability.lean`).
- [x] **§357 Non-linear stability** — Theorem 357C: algebraic ⇒ BN
  (`OpenMath/BNStability.lean`); Theorem 357D: BN ⇒ AN for irreducible
  non-confluent methods (`OpenMath/BNImpliesAN.lean`).
- [x] **§358 BN-stability of collocation methods** — Theorem 358A:
  algebraic-stability characterization of collocation methods, both
  directions (`OpenMath/CollocationAlgStability.lean`).
- [x] **§358/§359 Family-level stability** — Theorem 359B (Radau IIA):
  collocation + Radau IIA nodes ⇒ algebraically stable
  (`OpenMath/CollocationFamilies.lean`); Theorem 359C: classical
  collocation families (Gauss–Legendre, Radau I/θ=1) algebraically
  stable; concrete corollaries
  `rkGaussLegendre{2,3}_algStable_via_358A`; §3.5.10 packaging
  corollaries (family-level BN-stability for GL and Radau IIA
  collocation).
- [-] **§359B (Radau IA family bridge)**: blocked — see Blockers.
- [-] **§359D**: pending — needs identification of the named theorem
  after 359C in Butcher's text. See Blockers.

### §36 Implementable Implicit Runge–Kutta Methods
- [x] **§361 Diagonally implicit Runge–Kutta methods (SDIRK)** — SDIRK2
  and SDIRK3 with A-stability and L-stability
  (`OpenMath/SDIRK.lean`, `OpenMath/SDIRK3.lean`).
- [x] **§362 The importance of high stage order** — partially via
  `OpenMath/StiffAccuracy.lean` certificates.
- [ ] **§363 Singly implicit methods** — open.
- [ ] **§364 Generalizations of singly implicit methods** — open.
- [ ] **§365 Effective order and DESIRE methods** — open. (Effective
  order is also studied algebraically in §389.)

### §37 Symplectic Runge–Kutta Methods *(closed, cycle 492)*
- [x] **§370A Maintaining quadratic invariants** — `symplecticDefect i j` and
  `IsSymplectic` predicates introduced; `IsSymplectic.preserves_quadInv`
  proved in `OpenMath/SymplecticRK.lean` (Cooper 1987 / Sanz-Serna).
- [x] **§371 Examples of symplectic methods** — Gauss–Legendre 1-stage
  (implicit midpoint), 2-stage and 3-stage all proved symplectic
  (`rkGaussLegendre1_isSymplectic`, `rkGaussLegendre2_isSymplectic`,
  `rkGaussLegendre3_isSymplectic`).
- [ ] **§372 Order conditions** — symplectic order conditions
  (consequence of `M = 0` plus the standard order conditions; minor).
- [ ] **§373 Experiments with symplectic methods** — informal.

### §38 Algebraic Properties of Runge–Kutta Methods *(largest gap inside Ch 3 — Butcher's namesake)*
- [ ] **§380 Motivation** — RK composition.
- [~] **§381 Equivalence classes of Runge–Kutta methods** — quotient by
  re-labelling of stages. Relabeling-equivalence relation `IsRKEquivalent`
  with `refl`/`symm`/`trans`, `Setoid` instance, and the sanity lemma
  `weights_sum_eq` are landed in `OpenMath/ButcherGroup.lean` (cycle 496);
  `c_sum_eq` landed in cycle 497.
  Cross-stage-count equivalence (embedding into `Fin (s ⊔ t)`) remains open.
- [~] **§382 The group of Runge–Kutta methods** — composition law on
  equivalence classes.
  - raw `ButcherProduct` and block-structure computation lemmas landed
    in `OpenMath/ButcherGroup.lean` (cycle 500); cycle 501 proved
    `ButcherProduct.equiv_congr` and lifted composition to
    `QuotEquiv.product`, with `QuotEquiv.product_weightsSum`.
  - Cycle 502 landed **partial associativity** modulo relabel:
    `ButcherProduct.assoc_A` and `ButcherProduct.assoc_b` (the `A`
    matrix and `b` weights agree under the canonical reassociation
    `finReassoc s t u : Fin ((s+t)+u) ≃ Fin (s+(t+u))`), the cross-size
    helper `ButcherTableau.elementaryWeight_eq_of_A`, the raw
    `ButcherProduct.bSeries_assoc`, and the QuotEquiv-level lifts
    `QuotEquiv.product_bSeries_assoc`,
    `QuotEquiv.product_weightsSum_assoc`, and
    `QuotEquiv.product_satisfiesTreeCondition_assoc`. The `c` field
    disagrees on the third block (`1+t₃.c` vs `2+t₃.c`); see
    `.prover-state/issues/butcher_section382_composition.md`. Full
    on-the-nose `IsRKEquivalent` associativity remains open and
    requires reworking `ButcherProduct.c`.
- [~] **§383 The Runge–Kutta group `G₁`** — elementary-weight
  homomorphism into the group of mappings on rooted trees. Prep layer
  landed in `OpenMath/ButcherGroup.lean` (cycle 497):
  `IsRKEquivalent.elementaryWeight_eq`,
  `IsRKEquivalent.satisfiesTreeCondition_iff`, and
  `IsRKEquivalent.hasTreeOrder_iff`. Quotient-facing packaging landed
  in cycle 498: `QuotEquiv` alias, `QuotEquiv.satisfiesTreeCondition`,
  `QuotEquiv.hasTreeOrder`, sanity lifts `QuotEquiv.weightsSum` /
  `QuotEquiv.cSum`, plus the `_mk` computation lemmas. Cycle 499 added the
  quotient-facing Butcher-series coefficient map `QuotEquiv.bSeries` and
  `satisfiesTreeCondition_iff_bSeries`. Cycle 503 added the §384-facing
  wrapper `QuotEquiv.bSeriesHom`, the zero-stage vanishing coefficient
  lemma `QuotEquiv.bSeriesHom_one`, and the associativity alias
  `QuotEquiv.bSeriesHom_assoc`. The full `G₁` quotient/group construction
  remains open.
- [~] **§384 A homomorphism between two groups** — bridge from RK
  composition to the formal-power-series group on rooted trees.
  Cycle 503 landed identity prep for `bSeries` under `QuotEquiv.product`:
  `ButcherProduct.bSeries_one_left`, `ButcherProduct.bSeries_one_right`,
  `QuotEquiv.product_bSeries_one_left`, and
  `QuotEquiv.product_bSeries_one_right`. The non-tautological tree
  convolution for `QuotEquiv.bSeriesHom_product` remains open; see
  `.prover-state/issues/butcher_section384_convolution.md`.
- [ ] **§385 A generalization of `G₁`** — including non-RK methods.
- [ ] **§386 Recursive formula for the product** — explicit Butcher
  product on tree-indexed coefficients.
- [~] **§387 Some special elements of `G`** — identity, inverse, power.
  Cycle 498 landed the identity element: `trivialTableau : ButcherTableau 0`
  and `trivialTableau_unique` in `OpenMath/ButcherGroup.lean`. Inverse and
  integer-power constructions remain open.
- [ ] **§388 Some subgroups and quotient groups**.
- [ ] **§389 An algebraic interpretation of effective order** — connects
  to §365 above.

  *Suggested file split:* `OpenMath/ButcherGroup.lean` (group structure,
  §380–§387) and `OpenMath/EffectiveOrder.lean` (§365 / §389).

### §39 Implementation Issues *(open; survey-level — low priority)*
- [ ] §390–§395 (introduction, optimal sequences, accept / reject,
  error per step vs error per unit step, control-theoretic considerations,
  solving the implicit equations).

---

## Chapter 4: Linear Multistep Methods

### §40 Preliminaries
- [x] **§400 Fundamentals** — general LMM
  `Σⱼ αⱼ y_{n+j} = h Σⱼ βⱼ f(x_{n+j}, y_{n+j})`
  (`OpenMath/MultistepMethods.lean`).
- [x] **§401 Starting methods** — implicit assumption that the first `k`
  values are exact (used in every per-step convergence chain).
- [x] **§402 Convergence / §403 Stability / §404 Consistency**
  (`OpenMath/MultistepMethods.lean`,
  `OpenMath/DahlquistEquivalence.lean`).
- [x] **§405 Necessity of conditions for convergence /
  §406 Sufficiency of conditions** — the **Dahlquist equivalence theorem**
  (consistency + zero-stability ⟺ convergence)
  (`OpenMath/DahlquistEquivalence.lean`); spectral bound via generalized
  eigenspace decomposition (`OpenMath/SpectralBound.lean`); one-step
  convergence (`OpenMath/OneStepConvergence.lean`).

### §41 The Order of Linear Multistep Methods
- [x] **§410 Criteria for order** — `LMM.errorConstant` and the
  truncation operator (`OpenMath/MultistepMethods.lean`,
  `OpenMath/LMMTruncationOp.lean`).
- [x] **§411 Derivation of methods** — Adams family
  (`OpenMath/AdamsMethods.lean`).
- [x] **§412 Backward difference methods (BDF)** — BDF1–BDF7
  consistency, order = step count, zero-stability via `w = 1/ξ`
  substitution + `nlinarith` and unit-root reductions; BDF7
  zero-instability via Cayley-transformed sextic algebraic root
  certificate (`OpenMath/BDF.lean`,
  `OpenMath/MultistepMethods.lean`).

### §42 Errors and Error Growth
- [x] **§420 Introduction** — error constants computed for forward
  Euler `1/2`, backward Euler `−1/2`, trapezoidal `−1/12`, AB2 `5/12`,
  AM2 `−1/24`, … BDF2 `−2/9`, BDF3 `−3/22`, BDF4 `−12/125`,
  BDF5 `−10/137`, BDF6 `−20/343`, BDF7 `−35/726`
  (`OpenMath/AdamsMethods.lean`,
  `OpenMath/MultistepMethods.lean`).
- [x] **§421 Further remarks on error growth** — discrete Gronwall
  (`OpenMath/LMMTruncationOp.lean`,
  `discrete_gronwall_exp_horizon`).
- [x] **§423 Weakly stable methods** — covered implicitly by per-step
  chains.

#### Per-step quantitative convergence chains (covered)
The following per-step `OpenMath/LMM*Convergence.lean` files each carry
the trajectory predicate, residual unfolding, one-step Lipschitz / error
bound, pointwise local-truncation-error bound, and finite-horizon global
error bound for one specific scheme:

- Forward Euler (`OpenMath/LMMTruncationOp.lean`)
- AB2 through AB13 (scalar and vector) — `OpenMath/LMMAB{2,…,13}{,Vector}Convergence.lean`
- AM2 through AM12 (scalar and vector) — `OpenMath/LMMAM{2,…,12}{,Vector}Convergence.lean`
- BDF1 through BDF3 (scalar and vector, full global theorem) —
  `OpenMath/LMMBDF{1,2,3}{,Vector}Convergence.lean`
- BDF4 (scalar and vector, full global theorem closed cycle 490 via the
  stable-block quadratic Lyapunov certificate) —
  `OpenMath/LMMBDF4{,Vector}Convergence.lean`,
  `OpenMath/BDFQuadraticLyapunov.lean`
- BDF5 / BDF6 (scalar and vector truncation chains; global theorem
  deferred — see Blockers) — `OpenMath/LMMBDF{5,6}{,Vector}Convergence.lean`
- BDF7 (truncation chain only; impossible to globally converge because
  zero-unstable, proved) — `OpenMath/LMMBDF7{,Vector}Convergence.lean`

> **Cap:** The per-step enumeration is closed. Do **not** add AB14, AM13,
> or BDF8 quantitative convergence chains. Once the Dahlquist equivalence
> (`OpenMath/DahlquistEquivalence.lean`) is in place, qualitative
> convergence for any consistent zero-stable method follows; further
> quantitative per-step files repeat the same template and are not in
> Butcher.

### §43 Stability Characteristics
- [x] **§430–§434 Stability regions, boundary locus, Schur, P-C
  stability** — A-stability characterization, A-stable iff roots of `ρ`
  in unit disk; A-stability of backward Euler / trapezoidal; forward
  Euler not A-stable (`OpenMath/MultistepMethods.lean`); A(α)-stability
  sector definition, monotonicity, A-stable ↔ A(π/2)-stable
  (`OpenMath/BDF.lean`); BDF3–6 are NOT A-stable via Dahlquist barrier.

### §44 Order and Stability Barriers
- [x] **§441 Maximum order for a convergent k-step method** — first
  Dahlquist barrier consequence, plus the headline **Dahlquist's second
  barrier** (A-stable + zero-stable ⟹ order ≤ 2)
  (`OpenMath/MultistepMethods.lean`); 9 supporting lemmas including
  `E_nonneg_re`, `re_inv_exp_sub_one`, removable-singularity Gtilde
  proof, and `dahlquistCounterexample` (order-3 A-stable but not
  zero-stable).
- [x] **§442 Order stars for linear multistep methods** — covered via
  the RK side (`OpenMath/OrderStars.lean`,
  `OpenMath/PadeOrderStars.lean`); the LMM specialization is by reduction.
- [ ] **§443 Order arrows for linear multistep methods** — explicit
  LMM-side restatement open.

### §45 One-Leg Methods and G-stability *(partly closed; follow-ups open)*
- [x] **§450 One-leg counterpart** to a linear multistep method —
  coefficient-level `OneLegMethod`, `OneLegMethod.toLMM`,
  `LMM.toOneLeg`, round trips, and the trapezoidal one-leg method
  `OneLegMethod.trapezoid` with
  `OneLegMethod.trapezoid_toLMM_eq_lmm_trapezoid`
  (`OpenMath/OneLegMethods.lean`).
- [x] **§451 G-stability** — `gNormSq`, scalar `OneLegMethod.IsGStable`,
  and `OneLegMethod.trapezoid_isGStable_with_G_one` for the `1×1`
  identity matrix (`OpenMath/GStability.lean`).
- [ ] **§452 Transformations** between one-leg and LMM.
- [ ] **§453 Effective order interpretation** of the transformation.
- [ ] **§454 Concluding remarks**.

### §46 Implementation Issues *(open; lower priority)*
- [ ] **§460–§463** — survey, data representation, variable stepsize for
  Nordsieck methods, local error estimation. Largely implementation;
  the local-error-estimation §463 piece is the Milne device and is
  worth a dedicated file
  (`OpenMath/MilneDevice.lean`).

---

## Chapter 5: General Linear Methods

> **The whole chapter is open.** This is the biggest real gap in the
> codebase and is what cycle 491+ should pursue once Ch 3 §37 is done.
> Butcher's Ch 5 unifies RK and LMM under a single multivalue-multistage
> framework and is the part of the book that does not appear in any other
> textbook.

### §50 Representing Methods in General Linear Form
- [ ] **§500 Multivalue-multistage methods** — define a general linear
  method by the four block matrices
  `(A, U, B, V)` of sizes `s×s`, `s×r`, `r×s`, `r×r`, and the step
  ```
  Y = h (A ⊗ I) F(Y) + (U ⊗ I) y^{[n−1]}
  y^{[n]} = h (B ⊗ I) F(Y) + (V ⊗ I) y^{[n−1]}
  ```
  on an `r`-vector of input quantities and `s`-vector of stages
  (new file `OpenMath/GeneralLinearMethod.lean`).
- [ ] **§501 Transformations of methods** — equivalence under
  `T : (A, U, B, V) ↦ (A, U T⁻¹, T B, T V T⁻¹)`.
- [ ] **§502 Runge–Kutta methods as general linear methods** — embedding
  `r = 1`, `U = 𝟙`, `V = 1`.
- [ ] **§503 Linear multistep methods as general linear methods** —
  `s = 1` embedding (Nordsieck-vector form).
- [ ] **§504 Some known unconventional methods** — e.g. cyclic LMM and
  Adams–Bashforth–Moulton predictor-corrector pairs as GLMs (low
  priority).
- [ ] **§505 Some recently discovered general linear methods** — DIMSIM,
  ARK, IRKS examples (low priority; reuses §54 / §55 below).

### §51 Consistency, Stability and Convergence
- [ ] **§510 Definitions of consistency and stability** — analogue of
  §40 for GLMs.
- [ ] **§511 Covariance of methods** under the equivalence transformation
  of §501.
- [ ] **§512 Definition of convergence**.
- [ ] **§513 Necessity of stability** for convergence.
- [ ] **§514 Necessity of consistency** for convergence.
- [ ] **§515 Stability and consistency imply convergence** — the GLM
  analogue of the Dahlquist equivalence theorem
  (`OpenMath/DahlquistEquivalence.lean` is a special case).

### §52 The Stability of General Linear Methods
- [ ] **§520 Introduction** — stability matrix `M(z) := V + z B (I − z A)⁻¹ U`.
- [ ] **§521 Methods with maximal stability order** — Padé-like
  conditions on `M(z)`.
- [ ] **§522 Outline proof of the Butcher–Chipman conjecture** — order
  of `M(z)` as approximation to `exp(z) · I`. (Outline only; full proof
  out of scope for this cycle.)
- [ ] **§523 Non-linear stability** — algebraic stability for GLMs.
- [ ] **§524 Reducible linear multistep methods and G-stability** —
  reuses §451.
- [ ] **§525 G-symplectic methods** — symplectic GLMs (extends §37 to
  the GLM setting).

### §53 The Order of General Linear Methods
- [ ] **§530 Possible definitions of order** — order via local
  truncation error vs effective order.
- [ ] **§531 Local and global truncation errors** for GLMs.
- [ ] **§532 Algebraic analysis of order** — tree-based order conditions
  (extends §31).
- [ ] **§534 The order of a G-symplectic method**.
- [ ] **§535 The underlying one-step method** of a GLM.

### §54 Methods with Runge–Kutta Stability
- [ ] **§540 Design criteria for general linear methods**.
- [ ] **§541 The types of DIMSIM methods** — Type 1/2/3/4 classification.
- [ ] **§542 Runge–Kutta stability** — the condition `M(z)` has a single
  non-zero eigenvalue.
- [ ] **§543 Almost Runge–Kutta methods (ARK)**.
- [ ] **§544–§546 Concrete ARK methods** (3-stage order 3,
  4-stage order 4, 5-stage order 5).
- [ ] **§547 ARK methods for stiff problems**.

### §55 Methods with Inherent Runge–Kutta Stability
- [ ] **§550–§558** — doubly companion matrices, IRKS, derivation,
  property F, non-stiff / stiff examples, scale-and-modify. Lower
  priority within Ch 5.

---

## Active Frontier

- **Chapters 1–4 are essentially closed** modulo the three Blockers
  below and small low-priority survey items.
- **Highest-value gaps inside the existing chapters:**
  - §38 Algebraic Properties / Butcher group (Butcher's namesake topic;
    medium-sized).
  - §45 One-Leg Methods and G-stability (medium-sized).
- **Largest real gap:** **Chapter 5 (General Linear Methods)** —
  completely open and the part of Butcher that is not duplicated
  elsewhere.

---

## Backlog Queue

> **Source of truth for the planner's next-target rotation.** When
> the items in `## Current Target` are closed in tracked Lean code, the
> planner's first instruction in `strategy.md` must be: mark the closed
> items `[x]` in their chapter section, delete the closed body of
> `## Current Target`, and copy the **top item below** into
> `## Current Target` with concrete steps for the worker. Cross items
> off this list as they are promoted into `## Current Target`. New
> items always append at the bottom; **do not reorder closed work to
> the top.**

> **§334 Fehlberg 4(5) was completed for cycle 494; §38 Butcher group
> was promoted to `## Current Target`.** Items below renumber from #1.

1. **Butcher §500 — General linear method definition.** New file
   `OpenMath/GeneralLinearMethod.lean`. The four-block
   `(A, U, B, V)` data of sizes `s×s`, `s×r`, `r×s`, `r×r` and the
   one-step update on `r`-vectors of input quantities.
2. **Butcher §502 — RK as a general linear method.** Extend
   `OpenMath/GeneralLinearMethod.lean` with the embedding
   `r = 1`, `U = 𝟙`, `V = 1`. Use the existing `ButcherTableau`.
3. **Butcher §503 — LMM as a general linear method.** Extend
   `OpenMath/GeneralLinearMethod.lean` with the `s = 1` Nordsieck-vector
   embedding. Use the existing `LMM` interface.
4. **Butcher §510 — GLM consistency and stability definitions.**
   `OpenMath/GeneralLinearMethod.lean`. Direct generalisation of §40.
5. **Butcher §515 — GLM Dahlquist equivalence.** `stability + consistency
   ⟹ convergence` for GLMs. The existing
   `OpenMath/DahlquistEquivalence.lean` is a special case; the GLM
   version reduces to the same companion-matrix spectral bound.
6. **Butcher §111 — Linear systems of differential equations.** New
   file `OpenMath/LinearODE.lean`. `y(x) = exp((x − x₀) A) y₀` as a
   thin re-export of Mathlib `Matrix.exp` plus `Matrix.exp_add` for
   commuting matrices.
7. **Butcher §250 — Taylor series methods.** New file
   `OpenMath/TaylorSeriesMethod.lean`. Fixed-order truncation of the
   Taylor expansion of `y(x+h)`; consistency and order from existing
   `OneStepConvergence.lean` machinery.
8. **Butcher §341 — Solvability of implicit RK equations.** Thin
    wrapper over Mathlib `ContractingWith` proving stage solvability
    when `h · L · max_i Σ_j |A_{ij}| < 1`. Likely lives in
    `OpenMath/RungeKutta.lean`.
9. **Butcher §215 — Asymptotic error formula for the Euler method.**
    Leading-order term `e_n ≈ h ψ(xₙ)` with `ψ` solving the variational
    ODE. Extends `OpenMath/EulerConvergence.lean`.
10. **Butcher §336 — Dormand–Prince 5(4) (DOPRI5) embedded pair.**
    Same template as §334. Extends `OpenMath/EmbeddedRK.lean`.
11. **Butcher §463 — Milne device for local error estimation.** New
    file `OpenMath/MilneDevice.lean`. Predictor / corrector pair, local
    error from the difference, classical estimate.
12. **Butcher §520–§522 — Stability matrix of a GLM and the
    Butcher–Chipman conjecture (outline).** Extends the GLM file family.
    Stability matrix `M(z) := V + z B (I − z A)⁻¹ U`, Padé-like
    conditions on `M(z)`, outline of order of `M(z)` as approximation to
    `exp(z) · I`.
13. **Butcher §54 — DIMSIM types and ARK methods.** New file
    `OpenMath/DIMSIM.lean`. §541 type 1/2/3/4 classification, §543 ARK
    structural conditions.
14. **Butcher §55 — Inherent Runge–Kutta stability (IRKS).** New file
    `OpenMath/IRKS.lean`. Doubly companion matrices, derivation,
    property F.
15. **Butcher §38 follow-up — Effective order.** `OpenMath/EffectiveOrder.lean`.
    §365 (effective order definition / DESIRE) plus §389 algebraic
    interpretation. Builds on Current Target.
16. **Butcher §372 — Symplectic order conditions.** Short corollary in
    `OpenMath/SymplecticRK.lean`: an `IsSymplectic` method satisfying
    order-`p` conditions automatically satisfies the symplectic
    order-`p` conditions. Trivial follow-up to §370A.
17. **Butcher §443 — Order arrows for LMMs.** Explicit LMM-side
    restatement of order arrows in `OpenMath/PadeOrderStars.lean` or a
    new sibling. Reuses the §354 / §355 machinery.

When this list reaches under five items, any planner cycle that lands
without completing real work must append at least one new concrete
target before exiting (drawn from the chapter sections above). Do not
let the queue empty.

---

## Current Target

**Butcher §38 — Butcher group (algebraic RK properties).** New file
`OpenMath/ButcherGroup.lean`. Butcher's namesake topic and the single
biggest remaining gap inside Chapter 3.

Concrete next steps:

- Sketch the §380 motivation: why the equivalence-class group of RK
  methods modulo stage relabelling is well-defined and why the
  composition operation is associative.
- Define `ButcherProduct` (composition of two `ButcherTableau` values
  with possibly different stage counts), and the equivalence
  `IsRKEquivalent` under stage relabelling permutations (§381).
- Establish that `ButcherProduct` descends to the quotient — i.e.
  `IsRKEquivalent`-classes form a monoid under composition (§382).
- Define the elementary-weight homomorphism on rooted trees and use
  it to identify the `G₁` group of order-`p` RK methods modulo
  ≥(p+1)-order trees (§383).
- Cycle 497 landed the §383 class-invariance prep layer:
  `elementaryWeight_eq`, `satisfiesTreeCondition_iff`, and
  `hasTreeOrder_iff` for `IsRKEquivalent`; cycles 498-499 added the
  quotient-facing `QuotEquiv` packaging, including the lifted Butcher-series
  coefficient map `QuotEquiv.bSeries`. Cycle 500 landed the raw
  `ButcherProduct` definition plus block-structure computation lemmas
  (`butcherProduct_b_castAdd` / `_natAdd`, `butcherProduct_c_castAdd` /
  `_natAdd`) and the weights-sum sanity `butcherProduct_b_sum`. Cycle 501
  lifted `ButcherProduct` to
  `QuotEquiv s → QuotEquiv t → QuotEquiv (s + t)` via
  `ButcherProduct.equiv_congr`, and proved the lifted weights-sum law.
  Cycle 502 landed partial §382 associativity (`A` and `b` only) at the
  raw level (`ButcherProduct.assoc_A`, `ButcherProduct.assoc_b`,
  `ButcherProduct.bSeries_assoc`) and the QuotEquiv-level
  `QuotEquiv.product_bSeries_assoc`,
  `QuotEquiv.product_weightsSum_assoc`,
  `QuotEquiv.product_satisfiesTreeCondition_assoc`; the `c`-field
  mismatch on the third block is recorded in
  `.prover-state/issues/butcher_section382_composition.md`. Cycle 503
  landed the §384 identity-prep layer:
  `ButcherProduct.bSeries_one_left`, `ButcherProduct.bSeries_one_right`,
  `QuotEquiv.product_bSeries_one_left`,
  `QuotEquiv.product_bSeries_one_right`, `QuotEquiv.bSeriesHom`,
  `QuotEquiv.bSeriesHom_one`, and `QuotEquiv.bSeriesHom_assoc`.
  Next step: define the non-tautological tree-indexed convolution/product
  (Butcher §386-style recursive formula) and prove
  `QuotEquiv.bSeriesHom_product`; see
  `.prover-state/issues/butcher_section384_convolution.md`.
- Cover §387 special elements: identity (zero-stage), inverse, integer
  power.
- Defer §389 effective order to a separate `OpenMath/EffectiveOrder.lean`
  follow-up (item #15 in the Backlog Queue).

Expected sorry-first surface:
- `def ButcherProduct : ButcherTableau s → ButcherTableau t → ButcherTableau (s + t)`
- `def IsRKEquivalent : ButcherTableau s → ButcherTableau s → Prop`
- `theorem rkEquiv_refl / symm / trans` (basic equivalence)
- `def G₁` group via elementary-weight homomorphism through order p
- `theorem butcherProduct_assoc_modEquiv`

### Do NOT

- Do **not** add `OpenMath/LMMAB14*Convergence.lean`,
  `OpenMath/LMMAM13*Convergence.lean`, `OpenMath/LMMBDF8*Convergence.lean`,
  or any further per-step LMM convergence chains. The Dahlquist
  equivalence (`OpenMath/DahlquistEquivalence.lean`) already gives
  qualitative convergence of every consistent zero-stable method;
  these per-step quantitative chains repeat the same template, are not
  in Butcher, and were the reason cycles 466–489 stopped advancing the
  textbook.
- Do **not** reopen the BDF5 / BDF6 global-Lyapunov work without
  first updating `.prover-state/issues/bdf4_lyapunov_gap.md`. BDF4 closed
  in cycle 490; the BDF5 / BDF6 spectral obstruction is structural and
  needs a separate bespoke certificate per method, not a generic
  template.
- Do **not** attempt the Radau IA family-level collocation bridge
  (`IsCollocation ∧ HasRadauIANodes → IsAlgStable`). The
  counterexample in
  `.prover-state/issues/cycle_375_radauIA_collocation_counterexample.md`
  is decisive under the live `IsCollocation` interface.
- Do **not** create new tracked `OpenMath/*.lean` files containing live
  `sorry` outside the active §334 target or explicitly scheduled
  follow-up targets. Scratch belongs
  in `.prover-state/scratch/`.
- Do **not** extend `OpenMath/Hamiltonian.lean` as the cycle's headline
  target. The cycle 491 file (`Hamiltonian.energy_conserved` for the
  *exact* flow) is informally Butcher §123 / §370 motivation, not an
  active formalization seam. §370 is about the *RK method* preserving
  quadratic invariants of the ODE, not about the exact Hamiltonian flow,
  and is now closed in `OpenMath/SymplecticRK.lean`. Touch
  `OpenMath/Hamiltonian.lean` only for genuine maintenance, not as a way
  to manufacture a cycle.

---

## Sorry Locations

- No active `sorry`s in tracked code.

---

## Blockers / Deferred

- **BDF5 / BDF6 global Lyapunov / quantitative convergence** —
  `.prover-state/issues/bdf4_lyapunov_gap.md`. Spectral obstruction:
  the absolute companion matrix of BDF4/5/6 has Perron eigenvalue ≈ 2.58,
  so weighted-ℓ¹ Lyapunov sums in error coordinates cannot give the
  required `1 + O(h)` contraction. Cycle 490 closed BDF4 via a
  stable-block quadratic Lyapunov certificate
  (`OpenMath/BDFQuadraticLyapunov.lean`). The same obstruction blocks
  BDF5 and BDF6 — each will need its own bespoke quadratic Lyapunov
  certificate on its own stable subspace; the BDF4 prototype is the
  template. BDF7 has no global theorem because it is zero-unstable
  (proved).
- **§359D (Butcher §3.5.10)** — pending the textbook source statement.
  The cycle 376 §3.5.10 packaging corollaries
  (`OpenMath/CollocationFamilies.lean`) provide a clean BN-stability
  scaffold once the named theorem after 359C is identified in
  `.prover-state/textbook/butcher.txt`.
- **§359B (Radau IA family bridge)** —
  `.prover-state/issues/cycle_375_radauIA_collocation_counterexample.md`.
  `IsCollocation ∧ HasRadauIANodes → IsAlgStable` is false under the
  live `IsCollocation` interface (`C(s)`): the explicit 2-stage left-Radau
  collocation tableau on nodes `{0, 2/3}` has `M₀₀ = −1/16`. Concrete
  node certificates `rkRadauIA{2,3}_hasRadauIANodes` are landed; a
  future Radau IA family theorem must use the simplifying-assumption
  shape `B(2s−1) ∧ C(s−1) ∧ D(s)` or a different adjoint / transpose
  interface, not the 358A bridge.
