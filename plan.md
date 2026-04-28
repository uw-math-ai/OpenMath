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

**Progress: 0 / 175** entities done (5 chapters; 1 entity deferred cross-chapter)

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

- [ ] `def:110A` **Lipschitz condition in its second variable** (§110)
- [ ] `def:142A` **power-boundedness** (§142)
- [ ] `thm:101A` **The Kepler problem** (§101)
- [ ] `thm:123B` **Area invariance for Hamiltonian parallelograms** (§123)
- [ ] `thm:142D` **Convergence Equivalence for Matrix Powers** (§142)
- [ ] `def:112A` **one-sided Lipschitz condition** (§112)
- [ ] `def:142B` **convergent (matrix)** (§142)
- [ ] `lem:110B` **Contraction Mapping Fixed Point Existence** (§110)
- [ ] `thm:123A` **Further Hamiltonian problems** (§123)
- [ ] `thm:142E` **Stable Matrix Perturbation Power Bound** (§142)
- [ ] `thm:110C` **Existence and uniqueness of solutions** (§110)
- [ ] `thm:112B` **One Sided Lipschitz Solution Difference Bound** (§112)
- [ ] `thm:142C` **Stability and Minimal Polynomial Zeros Condition** (§142)
- [ ] `thm:111A` **inhomogeneous term** (§111)
- [ ] `thm:142F` **Stable Matrix Perturbation Bound** (§142)
- [ ] `thm:140A` **Linear difference equations** (§140)
- [ ] `thm:141A` **Constant coefficients** (§141)

---

## Chapter 2 — Numerical Differential Equation Methods  (4 entities; 1 deferred)

- [ ] `thm:212A` **Global truncation error (Euler)** (§212)
- [ ] `thm:213A` **Convergence of the Euler method** (§213)
- [ ] `thm:213B` **Euler method uniform convergence theorem** (§213)

### Deferred to after Chapter 4
- [!] `thm:243A` **Consistency, stability and convergence** (§243) — depends on `def:402A`, `def:403A`, `def:404B` (Ch.4 §§402–404). Resume after those are formalized.

---

## Chapter 3 — Runge–Kutta Methods  (92 entities)

- [ ] `def:350A` **A-stability, A(α)-stability and L-stability** (§350)
- [ ] `def:381B` **Φ-equivalent** (§380)
- [ ] `def:381D` **P -reducible** (§380)
- [ ] `lem:322A` **Methods of order 4** (§322)
- [ ] `lem:383C` **Existence of Left and Right Inverses** (§383)
- [ ] `thm:301A` **Functions on trees** (§301)
- [ ] `thm:302C` **Rooted Tree Enumeration Formulas** (§302)
- [ ] `thm:342C` **Gaussian Quadrature Order Conditions Equivalence** (§342)
- [ ] `thm:343A` **Reflected methods** (§343)
- [ ] `thm:351B` **A Stability Criterion for Runge Kutta Methods** (§351)
- [ ] `thm:356C` **AN stability necessary conditions** (§356)
- [ ] `cor:342D` **Gaussian Quadrature Runge Kutta Order Condition** (§342)
- [ ] `cor:356D` **Positive weights for DJ irreducible methods** (§356)
- [ ] `def:310A` **elementary differential** (§310)
- [ ] `def:355A` **down arrows** (§355)
- [ ] `def:381E` **reduced method (381E)** (§380)
- [ ] `lem:342B` **Gaussian quadrature exactness degree** (§342)
- [ ] `lem:351A` **Criteria for A-stability** (§351)
- [ ] `thm:302A` **Some combinatorial questions** (§302)
- [ ] `def:356B` **reduced method (356B)** (§356)
- [ ] `def:381C` **0-reduced method** (§380)
- [ ] `def:381F` **P -equivalent** (§380)
- [ ] `lem:342A` **Methods based on Gaussian quadrature** (§342)
- [ ] `thm:302B` **Rooted Tree Generating Function Identity** (§302)
- [ ] `thm:311B` **Taylor expansion exact solution formula** (§311)
- [ ] `thm:314A` **Independence of the elementary differentials** (§314)
- [ ] `thm:355F` **A stability condition for Runge Kutta methods** (§355)
- [ ] `def:356A` **irreducibility in the sense of Dahlquist and Jeltsch** (§356)
- [ ] `lem:319A` **Global truncation error (RK)** (§319)
- [ ] `lem:359A` **The V and W transformations** (§359)
- [ ] `thm:304A` **Enumerating non-rooted trees** (§304)
- [ ] `thm:306A` **Taylor’s theorem** (§306)
- [ ] `thm:344A` **Methods based on Radau and Lobatto quadrature** (§344)
- [ ] `thm:381G` **Irreducible Runge Kutta Stage Distinguishability** (§380)
- [ ] `thm:381H` **Runge Kutta Equivalence Conditions** (§380)
- [ ] `def:357A` **B-stability** (§357)
- [ ] `def:381A` **equivalent** (§380)
- [ ] `lem:310B` **Elementary Differential Weight Formula** (§310)
- [ ] `thm:319B` **Global truncation error bound via local error accumulation** (§319)
- [ ] `thm:352E` **V function recurrence relation** (§352)
- [ ] `def:357B` **algebraically stable** (§357)
- [ ] `lem:311A` **The Taylor expansion of the exact solution** (§311)
- [ ] `lem:312B` **Elementary Weight Summation Formula** (§312)
- [ ] `lem:313A` **The Taylor expansion of the approximate solution** (§313)
- [ ] `lem:383A` **The Runge–Kutta group** (§383)
- [ ] `thm:317A` **Independence of elementary weights** (§317)
- [ ] `thm:352D` **Pade approximation recurrence relation** (§352)
- [ ] `thm:388B` **Equivalence of Additive and Multiplicative Perturbations** (§388)
- [ ] `cor:359B` **W transformation preserves orthogonality conditions** (§359)
- [ ] `def:312A` **derivative weights** (§312)
- [ ] `lem:383B` **Associativity of multiplicative forest mappings** (§383)
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
- [ ] `thm:357C` **Algebraic Stability Implies BN Stability** (§357)
- [ ] `thm:363A` **Singly implicit methods** (§363)
- [ ] `thm:384A` **A homomorphism between two groups** (§384)
- [ ] `def:388F` **Algebraic condition for group commutators** (§388)
- [ ] `thm:315A` **Conditions for order** (§315)
- [ ] `thm:353A` **A-stability of Gauss and related methods** (§353)
- [ ] `thm:355B` **Order arrow tangency directions theorem** (§355)
- [ ] `thm:358A` **BN-stability of collocation methods** (§358)
- [ ] `thm:382B` **Runge Kutta method composition inverse** (§380)
- [ ] `thm:386A` **Recursive formula for the product** (§386)
- [ ] `def:323A` **internal order q** (§323)
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
- [ ] `def:370A` **Maintaining quadratic invariants** (§370)
- [ ] `thm:372A` **Order conditions** (§372)

---

## Chapter 4 — Linear Multistep Methods  (27 entities)

- [ ] `def:404A` **preconsistent** (§404)
- [ ] `def:451A` **G-stable** (§451)
- [ ] `thm:431A` **Stability regions** (§431)
- [ ] `def:402A` **convergent (LMM)** (§402)
- [ ] `def:422B` **underlying one-step method** (§422)
- [ ] `def:442A` **principal sheet** (§441)
- [ ] `thm:454A` **Concluding remarks on G-stability** (§454)
- [ ] `def:404B` **consistent (LMM)** (§404)
- [ ] `def:403A` **stability in the sense of Dahlquist** (§403)
- [ ] `def:406A` **local truncation error** (§406)
- [ ] `thm:410B` **Order Condition for Linear Multistep Methods (410B)** (§410)
- [ ] `lem:406B` **Convergence condition sufficiency bound** (§406)
- [ ] `thm:405C` **Convergent Linear Multistep Implies Consistency** (§405)
- [ ] `thm:410C` **Order condition via generating functions** (§410)
- [ ] `thm:422A` **The underlying one-step method (LMM)** (§422)
- [ ] `thm:441C` **Maximum order bound for stable linear multistep methods** (§441)
- [ ] `lem:441B` **Maximum order coefficients negativity** (§441)
- [ ] `thm:405A` **Necessity of conditions for convergence** (§405)
- [ ] `thm:406C` **Global error bound for linear multistep methods** (§406)
- [ ] `thm:410A` **Criteria for order** (§410)
- [ ] `thm:422C` **Convergence of Linear Multistep Methods** (§422)
- [ ] `lem:441A` **Maximum order for a convergent k-step method** (§441)
- [ ] `thm:405B` **Convergent linear multistep method is preconsistent** (§405)
- [ ] `thm:406D` **Convergence from Stability and Consistency** (§406)
- [ ] `thm:410D` **Order Condition for Linear Multistep Methods (410D)** (§410)
- [ ] `thm:443A` **Order arrows for linear multistep methods** (§441)
- [ ] `thm:443B` **A stability error constant upper bound** (§441)

---

## Chapter 5 — General Linear Methods  (35 entities)

- [ ] `cor:550C` **Inverse of companion matrix derivative basis** (§550)
- [ ] `def:530A` **non-degenerate** (§530)
- [ ] `def:510A` **preconsistency vector** (§510)
- [ ] `def:510C` **stable** (§510)
- [ ] `def:530B` **Order relative to starting method (530B)** (§530)
- [ ] `def:510B` **consistent (GLM)** (§510)
- [ ] `def:530C` **Order relative to starting method (530C)** (§530)
- [ ] `def:512A` **convergent (GLM)** (§512)
- [ ] `def:520A` **Introduction** (§520)
- [ ] `thm:523A` **Non-linear stability** (§523)
- [ ] `def:520C` **stability function** (§520)
- [ ] `thm:513A` **The necessity of stability** (§513)
- [ ] `thm:515D` **Stability and Consistency Imply Convergence (515D)** (§515)
- [ ] `thm:550B` **Doubly companion matrix similarity transformation** (§550)
- [ ] `def:521A` **Methods with maximal stability order** (§521)
- [ ] `lem:515A` **Stability and consistency imply convergence (515A)** (§515)
- [ ] `thm:514A` **The necessity of consistency** (§514)
- [ ] `thm:520B` **Stability Matrix for Linear Differential Equation** (§520)
- [ ] `thm:520D` **Instability Region Boundary Characterization** (§520)
- [ ] `thm:550A` **Doubly companion matrices** (§550)
- [ ] `def:520E` **A-stable** (§520)
- [ ] `def:542A` **annihilation conditions** (§542)
- [ ] `lem:515B` **Stability and Consistency Imply Convergence (515B)** (§515)
- [ ] `thm:521B` **Maximum stability order for given steps** (§521)
- [ ] `thm:523B` **Nonlinear Stability via Positive Semidefiniteness** (§523)
- [ ] `def:520F` **L Stability Condition for Linear Methods** (§520)
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
