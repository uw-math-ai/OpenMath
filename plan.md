# Formalization Plan

## Textbook
*Numerical Methods for Ordinary Differential Equations* — J.C. Butcher (3rd edition)

**Source**: `extraction/raw_text/` (`ch01.txt`–`ch05.txt`, `full_text.txt`).  
**Data guide**: `extraction/FORMALIZATION_DATA_GUIDE.md`  
**Entity data**: `extraction/formalization_data/entities/<id>.json` — one file per theorem.

## Status Key
- `[x]` Formalized (0 sorry)
- `[~]` In progress
- `[ ]` Not started
- `[!]` Deferred — depends on a later chapter; pick up after that chapter is done

**Progress: 65 / 175** entities done (5 chapters; `def:356A` partial — DJ-irreducibility component only)

## Order
Process chapters in order Ch.1 → Ch.5. Within each chapter, follow the listed
order — it is a valid topological sort restricted to that chapter (filtered from
`extraction/formalization_data/topo_order.json`), so every dependency of an entity
is either earlier in the same chapter or in an earlier chapter that has already
been completed.

Per `extraction/FORMALIZATION_DATA_GUIDE.md` §5.2, subsection number is **not**
a valid intra-chapter order — there are 91 intra-chapter forward references.
Follow the order as listed.

The single cross-chapter exception is `thm:243A` in Ch.2, which previews three
Ch.4 definitions (`def:402A`, `def:403A`, `def:404B`); it is parked at the end
of Ch.2 and resumed after Ch.4 §404 is done.

---

## Chapter 1 — Differential and Difference Equations  (17 entities)

- [x] `def:110A` **Lipschitz condition in its second variable** (§110)
- [x] `def:142A` **power-boundedness** (§142)
- [x] `thm:101A` **The Kepler problem** (§101)
- [x] `thm:123B` **Area invariance for Hamiltonian parallelograms** (§123)
- [ ] `thm:142D` **Convergence Equivalence for Matrix Powers** (§142)
- [x] `def:112A` **one-sided Lipschitz condition** (§112)
- [x] `def:142B` **convergent (matrix)** (§142)
- [x] `lem:110B` **Contraction Mapping Fixed Point Existence** (§110)
- [x] `thm:123A` **Further Hamiltonian problems** (§123)
- [ ] `thm:142E` **Stable Matrix Perturbation Power Bound** (§142)
- [x] `thm:110C` **Existence and uniqueness of solutions** (§110)
- [x] `thm:112B` **One Sided Lipschitz Solution Difference Bound** (§112)
- [ ] `thm:142C` **Stability and Minimal Polynomial Zeros Condition** (§142)
- [x] `thm:111A` **inhomogeneous term** (§111)
- [ ] `thm:142F` **Stable Matrix Perturbation Bound** (§142)
- [x] `thm:140A` **Linear difference equations** (§140)
- [x] `thm:141A` **Constant coefficients** (§141)

---

## Chapter 2 — Numerical Differential Equation Methods  (4 entities; 1 deferred)

- [x] `thm:212A` **Global truncation error (Euler)** (§212)
- [x] `thm:213A` **Convergence of the Euler method** (§213)
- [x] `thm:213B` **Euler method uniform convergence theorem** (§213)

### Deferred to after Chapter 4
- [x] `thm:243A` **Consistency, stability and convergence** (§243) — iff packager landed cycle 069 in `OpenMath/Chapter4/Section405.lean`. Forward direction (`stable ∧ consistent ⇒ convergent`) closed via cycle 068 `stable_consistent_isConvergent`. Reverse direction (`convergent_isStable` cycle 072, `convergent_isPreconsistent` cycle 069, `convergent_isConsistent` cycle 070) all closed.

---

## Chapter 3 — Runge–Kutta Methods  (92 entities)

- [x] `def:350A` **A-stability, A(α)-stability and L-stability** (§350)
- [x] `def:381B` **Φ-equivalent** (§380)
- [x] `def:381D` **P -reducible** (§380)
- [x] `lem:322A` **Methods of order 4** (§322) — `OpenMath/Chapter3/Section322.lean`
- [x] `lem:383C` **Existence of Left and Right Inverses** (§383)
- [x] `thm:301A` **Functions on trees** (§301)
- [ ] `thm:302C` **Rooted Tree Enumeration Formulas** (§302)
- [ ] `thm:342C` **Gaussian Quadrature Order Conditions Equivalence** (§342)
- [x] `thm:343A` **Reflected methods** (§343) — `OpenMath/Chapter3/Section343.lean`
- [ ] `thm:351B` **A Stability Criterion for Runge Kutta Methods** (§351)
- [ ] `thm:356C` **AN stability necessary conditions** (§356)
- [ ] `cor:342D` **Gaussian Quadrature Runge Kutta Order Condition** (§342)
- [ ] `cor:356D` **Positive weights for DJ irreducible methods** (§356)
- [x] `def:310A` **elementary differential** (§310) — `OpenMath/Chapter3/Section310.lean`
- [x] `def:355A` **down arrows** (§355) — `OpenMath/Chapter3/Section355.lean`
- [x] `def:381E` **reduced method (381E)** (§380) — `IsIrreducible` formalised; `reducedMethod` construction deferred (see `.prover-state/issues/reduced_method_deferred.md`)
- [ ] `lem:342B` **Gaussian quadrature exactness degree** (§342)
- [ ] `lem:351A` **Criteria for A-stability** (§351)
- [ ] `thm:302A` **Some combinatorial questions** (§302)
- [x] `def:356B` **reduced method (356B)** (§356) — `OpenMath/Chapter3/Section356.lean`
- [x] `def:381C` **0-reduced method** (§380)
- [ ] `def:381F` **P -equivalent** (§380)
- [ ] `lem:342A` **Methods based on Gaussian quadrature** (§342)
- [ ] `thm:302B` **Rooted Tree Generating Function Identity** (§302)
- [ ] `thm:311B` **Taylor expansion exact solution formula** (§311)
- [ ] `thm:314A` **Independence of the elementary differentials** (§314)
- [ ] `thm:355F` **A stability condition for Runge Kutta methods** (§355)
- [~] `def:356A` **irreducibility in the sense of Dahlquist and Jeltsch** (§356) — DJ-irreducibility formalized in `OpenMath/Chapter3/Section356.lean`; AN-stability component deferred (see `.prover-state/issues/AN_stability_deferred.md`)
- [ ] `lem:319A` **Global truncation error (RK)** (§319)
- [ ] `lem:359A` **The V and W transformations** (§359)
- [ ] `thm:304A` **Enumerating non-rooted trees** (§304)
- [ ] `thm:306A` **Taylor’s theorem** (§306)
- [ ] `thm:344A` **Methods based on Radau and Lobatto quadrature** (§344)
- [ ] `thm:381G` **Irreducible Runge Kutta Stage Distinguishability** (§380)
- [ ] `thm:381H` **Runge Kutta Equivalence Conditions** (§380)
- [x] `def:357A` **B-stability** (§357) — `OpenMath/Chapter3/Section357.lean`
- [x] `def:381A` **equivalent** (§380) — `OpenMath/Chapter3/Section381.lean`
- [ ] `lem:310B` **Elementary Differential Weight Formula** (§310)
- [ ] `thm:319B` **Global truncation error bound via local error accumulation** (§319)
- [ ] `thm:352E` **V function recurrence relation** (§352)
- [x] `def:357B` **algebraically stable** (§357) — `OpenMath/Chapter3/Section357.lean`
- [ ] `lem:311A` **The Taylor expansion of the exact solution** (§311)
- [ ] `lem:312B` **Elementary Weight Summation Formula** (§312)
- [ ] `lem:313A` **The Taylor expansion of the approximate solution** (§313)
- [x] `lem:383A` **The Runge–Kutta group** (§383)
- [ ] `thm:317A` **Independence of elementary weights** (§317)
- [ ] `thm:352D` **Pade approximation recurrence relation** (§352)
- [ ] `thm:388B` **Equivalence of Additive and Multiplicative Perturbations** (§388)
- [ ] `cor:359B` **W transformation preserves orthogonality conditions** (§359)
- [x] `def:312A` **derivative weights** (§312)
- [x] `lem:383B` **Associativity of multiplicative forest mappings** (§383)
- [ ] `thm:311C` **Taylor expansion via Picard iteration** (§311)
- [ ] `thm:313B` **Runge Kutta method Taylor expansion formulas** (§313)
- [ ] `thm:352C` **Pade approximant recurrence relation** (§352)
- [ ] `thm:357D` **BN Stability Implies AN Stability** (§357)
- [ ] `thm:382A` **The group of Runge–Kutta methods** (§380)
- [ ] `thm:388C` **One plus Hp is normal in G1** (§388)
- [ ] `def:388D` **Consistency Condition for Group Element** (§388)
- [ ] `lem:383D` **Runge Kutta group inverse formula** (§383)
- [ ] `thm:311D` **Taylor expansion of exact solution equals numerical method** (§311)
- [ ] `thm:352A` **Padé approximations to the exponential function** (§352)
- [x] `thm:357C` **Algebraic Stability Implies BN Stability** (§357) — `OpenMath/Chapter3/Section357.lean`
- [ ] `thm:363A` **Singly implicit methods** (§363)
- [ ] `thm:384A` **A homomorphism between two groups** (§384)
- [ ] `def:388F` **Algebraic condition for group commutators** (§388)
- [ ] `thm:315A` **Conditions for order** (§315)
- [ ] `thm:353A` **A-stability of Gauss and related methods** (§353)
- [ ] `thm:355B` **Order arrow tangency directions theorem** (§355)
- [ ] `thm:358A` **BN-stability of collocation methods** (§358)
- [ ] `thm:382B` **Runge Kutta method composition inverse** (§380)
- [ ] `thm:386A` **Recursive formula for the product** (§386)
- [x] `def:323A` **internal order q** (§323)
- [ ] `thm:324C` **Explicit Runge Kutta Order Stage Lower Bound** (§324)
- [ ] `thm:355C` **Arrow Termination at Poles Zeros or Infinity** (§355)
- [ ] `thm:359C` **Algebraic Stability of Implicit Runge Kutta Methods** (§359)
- [ ] `thm:388G` **D is normal subgroup of G1** (§388)
- [ ] `thm:388H` **Exponential Function Class and Derivative Inclusion** (§388)
- [ ] `thm:323B` **Runge Kutta method augmentation theorem** (§323)
- [ ] `thm:324A` **Order barriers** (§324)
- [ ] `thm:343B` **Reflected Order Conditions Preservation** (§343)
- [ ] `thm:355D` **Down arrow zero up arrow pole inequality** (§355)
- [ ] `thm:387A` **Some special elements of G** (§387)
- [ ] `thm:388E` **C is a normal subgroup of G1** (§388)
- [ ] `thm:324B` **Explicit Runge Kutta Order Barrier** (§324)
- [ ] `thm:333A` **A class of error-estimating methods** (§333)
- [ ] `thm:355E` **Pade approximation arrow termination theorem** (§355)
- [ ] `thm:388A` **Some subgroups and quotient groups** (§388)
- [ ] `lem:389A` **An algebraic interpretation of effective order** (§389)
- [ ] `thm:352B` **Uniqueness of Pade exponential approximation** (§352)
- [ ] `thm:355G` **A-stability Pade approximation order restriction** (§355)
- [x] `def:370A` **Maintaining quadratic invariants** (§370) — `OpenMath/Chapter3/Section370.lean`
- [ ] `thm:372A` **Order conditions** (§372)

---

## Chapter 4 — Linear Multistep Methods  (27 entities)

- [x] `def:404A` **preconsistent** (§404) — `OpenMath/Chapter4/Section404.lean`
- [ ] `def:451A` **G-stable** (§451)
- [ ] `thm:431A` **Stability regions** (§431)
- [x] `def:402A` **convergent (LMM)** (§402) — `OpenMath/Chapter4/Section404.lean`
- [ ] `def:422B` **underlying one-step method** (§422)
- [ ] `def:442A` **principal sheet** (§441)
- [ ] `thm:454A` **Concluding remarks on G-stability** (§454)
- [x] `def:404B` **consistent (LMM)** (§404)
- [x] `def:403A` **stability in the sense of Dahlquist** (§403) — OpenMath/Chapter4/Section404.lean
- [x] `def:406A` **local truncation error** (§406) — `OpenMath/Chapter4/Section404.lean`
- [x] `thm:410B` **Order Condition for Linear Multistep Methods (410B)** (§410) — `OpenMath/Chapter4/Section410.lean` (cycle 075)
- [x] `lem:406B` **Convergence condition sufficiency bound** (§406) — `OpenMath/Chapter4/Section404.lean`
- [x] `thm:405C` **Convergent Linear Multistep Implies Consistency** (§405) — `OpenMath/Chapter4/Section405.lean` (cycle 070)
- [x] `thm:410C` **Order condition via generating functions** (§410) — `OpenMath/Chapter4/Section410.lean` (cycle 076)
- [ ] `thm:422A` **The underlying one-step method (LMM)** (§422)
- [ ] `thm:441C` **Maximum order bound for stable linear multistep methods** (§441)
- [ ] `lem:441B` **Maximum order coefficients negativity** (§441)
- [x] `thm:405A` **Necessity of conditions for convergence** (§405) — `OpenMath/Chapter4/Section405.lean` (cycle 072)
- [x] `thm:406C` **Global error bound for linear multistep methods** (§406)
- [x] `thm:410A` **Criteria for order** (§410) — `OpenMath/Chapter4/Section410.lean` (cycle 074)
- [ ] `thm:422C` **Convergence of Linear Multistep Methods** (§422)
- [ ] `lem:441A` **Maximum order for a convergent k-step method** (§441)
- [x] `thm:405B` **Convergent linear multistep method is preconsistent** (§405) — `OpenMath/Chapter4/Section405.lean` (cycle 069)
- [x] `thm:406D` **Convergence from Stability and Consistency** (§406)
- [x] `thm:410D` **Order Condition for Linear Multistep Methods (410D)** (§410) — `OpenMath/Chapter4/Section410.lean` (cycle 079)
- [ ] `thm:443A` **Order arrows for linear multistep methods** (§441)
- [ ] `thm:443B` **A stability error constant upper bound** (§441)

---

## Chapter 5 — General Linear Methods  (35 entities)

- [ ] `cor:550C` **Inverse of companion matrix derivative basis** (§550)
- [ ] `def:530A` **non-degenerate** (§530)
- [x] `def:510A` **preconsistency vector** (§510) — `OpenMath/Chapter5/Section510.lean`
- [x] `def:510C` **stable** (§510) — `OpenMath/Chapter5/Section510.lean`
- [ ] `def:530B` **Order relative to starting method (530B)** (§530)
- [x] `def:510B` **consistent (GLM)** (§510) — `OpenMath/Chapter5/Section510.lean`
- [ ] `def:530C` **Order relative to starting method (530C)** (§530)
- [x] `def:512A` **convergent (GLM)** (§512) — `OpenMath/Chapter5/Section512.lean`
- [x] `def:520A` **Introduction** (§520) — `OpenMath/Chapter5/Section520.lean`
- [ ] `thm:523A` **Non-linear stability** (§523)
- [x] `def:520C` **stability function** (§520) — `OpenMath/Chapter5/Section520.lean`
- [x] `thm:513A` **The necessity of stability** (§513) — `OpenMath/Chapter5/Section513.lean` (cycle 093, axiom-clean)
- [~] `thm:515D` **Stability and Consistency Imply Convergence (515D)** (§515) — OpenMath/Chapter5/Section515.lean (cycle 113: 1 sorry remaining at `aux_515D_output_tendsto` body line ~1803; sub-lemmas A/B/C all closed cycles 112–113; cycle-113 added `aux_515D_construct_ell_U_phi_A` M-matrix-based constructor helper for the side-condition vectors; body composition + signature strengthening deferred to cycle 115 — cycle 113 audit identified §514 cascade conflict with the strategy's proposed `IsConvergent` strengthening, see issue cycle_113_isconvergent_strengthening_514_blocker.md)
- [ ] `thm:550B` **Doubly companion matrix similarity transformation** (§550)
- [x] `def:521A` **Methods with maximal stability order** (§521)
- [x] `lem:515A` **Stability and consistency imply convergence (515A)** (§515) — `OpenMath/Chapter5/Section515.lean` (cycle 102 closure: 515a + 515b axiom-clean)
- [x] `thm:514A` **The necessity of consistency** (§514) — `OpenMath/Chapter5/Section514.lean` (cycle 099 closure; option (ii) sidestep, axiom-clean)
- [ ] `thm:520B` **Stability Matrix for Linear Differential Equation** (§520)
- [ ] `thm:520D` **Instability Region Boundary Characterization** (§520)
- [ ] `thm:550A` **Doubly companion matrices** (§550)
- [x] `def:520E` **A-stable** (§520) — OpenMath/Chapter5/Section520.lean
- [ ] `def:542A` **annihilation conditions** (§542)
- [x] `lem:515B` **Stability and Consistency Imply Convergence (515B)** (§515) — OpenMath/Chapter5/Section515.lean (cycle 107: `aux_515B_eta_contraction` closed via M-matrix comparison principle with explicit `‖(h₀L)·|A|‖<1` Frobenius hypothesis)
- [ ] `thm:521B` **Maximum stability order for given steps** (§521)
- [ ] `thm:523B` **Nonlinear Stability via Positive Semidefiniteness** (§523)
- [x] `def:520F` **L Stability Condition for Linear Methods** (§520) — OpenMath/Chapter5/Section520.lean
- [ ] `def:551A` **Inherent Runge–Kutta stability** (§551)
- [ ] `lem:515C` **Accumulated error estimate for multistep methods** (§515)
- [ ] `thm:535A` **The underlying one-step method (GLM)** (§535)
- [ ] `thm:551B` **Single Non Zero Eigenvalue Stability** (§551)
- [ ] `thm:553A` **Derivation of methods with IRK stability** (§553)
- [ ] `thm:532A` **Algebraic analysis of order** (§532)
- [ ] `thm:534A` **The order of a G-symplectic method** (§534)
- [ ] `thm:541A` **The types of DIMSIM methods** (§541)
- [ ] `def:525A` **G-symplectic methods** (§525)

---
