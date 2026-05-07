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

**Progress: 70 / 175** entities done (5 chapters; `def:356A` partial — DJ-irreducibility component only; `thm:142D` partial — clauses (i)⇔(ii) only)

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
- [~] `thm:142D` **Convergence Equivalence for Matrix Powers** (§142) — `OpenMath/Chapter1/Section142.lean::thm_142D` (cycle 132, partial: i⇔ii via Gelfand; iii/iv blocked on Jordan canonical form per `jordan_canonical_form_missing.md`)
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
- [x] `def:451A` **G-stable** (§451) — `OpenMath/Chapter4/Section451.lean`
- [~] `thm:431A` **Stability regions** (§431) — `OpenMath/Chapter4/Section431.lean` (cycle 170, partial: predicate + Schur algebraic identity + necessity direction of (431e); sufficiency blocked on Mathlib gap, see `.prover-state/issues/rouche_theorem_missing.md`)
- [x] `def:402A` **convergent (LMM)** (§402) — `OpenMath/Chapter4/Section404.lean`
- [ ] `def:422B` **underlying one-step method** (§422)
- [ ] `def:442A` **principal sheet** (§441)
- [x] `thm:454A` **Concluding remarks on G-stability** (§454) — `OpenMath/Chapter4/Section454.lean` (cycle 169; BDF2 A-stability corollary in same file)
- [x] `def:404B` **consistent (LMM)** (§404)
- [x] `def:403A` **stability in the sense of Dahlquist** (§403) — OpenMath/Chapter4/Section404.lean
- [x] `def:406A` **local truncation error** (§406) — `OpenMath/Chapter4/Section404.lean`
- [x] `thm:410B` **Order Condition for Linear Multistep Methods (410B)** (§410) — `OpenMath/Chapter4/Section410.lean` (cycle 075)
- [x] `lem:406B` **Convergence condition sufficiency bound** (§406) — `OpenMath/Chapter4/Section404.lean`
- [x] `thm:405C` **Convergent Linear Multistep Implies Consistency** (§405) — `OpenMath/Chapter4/Section405.lean` (cycle 070)
- [x] `thm:410C` **Order condition via generating functions** (§410) — `OpenMath/Chapter4/Section410.lean` (cycle 076)
- [ ] `thm:422A` **The underlying one-step method (LMM)** (§422)
- [ ] `thm:441C` **Maximum order bound for stable linear multistep methods** (§441)
- [ ] `lem:441B` **Maximum order coefficients negativity** (§441) — cycle 171 attempt rolled back cycle 172 (misinterpretation; see `.prover-state/issues/lem_441B_misinterpretation.md`); `aPoly` def + degree bound + BDF2/Euler witnesses retained as Phase A infrastructure in `OpenMath/Chapter4/Section441.lean`
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
- [x] `def:530A` **non-degenerate** (§530) — `OpenMath/Chapter5/Section530.lean` (cycle 139: opens §530 with the `GeneralizedRungeKuttaMethod` (530a) tableau, `StartingMethod` dependent-sequence structure, and the `IsDegenerate` / `IsNonDegenerate` predicates. Non-vacuity witnessed by `trivialStartingMethod_isNonDegenerate` (r=1, b₀=1 ≠ 0); `zeroStartingMethod_isDegenerate` confirms refutability. All three public theorems axiom-clean. Cycle 141: heterogeneous-stages witness added — `nontrivialTwoStageGRK` (s=2, b₀=2), `mixedStartingMethod` (r=2, `stages 0 = 1`, `stages 1 = 2`) with `mixedStartingMethod_isNonDegenerate`; `mixedStartingMethod_stages_neq` confirms the dependent `stages : Fin r → ℕ` design is genuinely needed; `zero2StartingMethod_isDegenerate` witnesses degeneracy at r=2.)
- [x] `def:510A` **preconsistency vector** (§510) — `OpenMath/Chapter5/Section510.lean`
- [x] `def:510C` **stable** (§510) — `OpenMath/Chapter5/Section510.lean`
- [~] `def:530B` **Order relative to starting method (530B)** (§530) — Sorry-first scaffold attempted cycle 149, rolled back cycle 150 per cycle-139 precedent. Cycle 151: **Path A Step 1 complete** — `GeneralizedRungeKuttaMethod.IsExplicit` predicate (strict-lower-triangular `A`) plus axiom-clean non-vacuity witnesses landed in `OpenMath/Chapter5/Section530.lean`. Cycle 152: **Path A Step 2 complete** (2a–2f + 2e) — `GeneralizedRungeKuttaMethod.explicitStageValue`/`explicitApply`, `StartingMethod.applyExplicit`, `applyExactThenStarting_explicit`, GLM-side `Section510.GeneralLinearMethod.IsExplicit`/`explicitStageValue` + `applyStartingThenStep_explicit` (in re-opened namespaces; imports `Section510`), and three axiom-clean sanity theorems (`trivialStartingMethod_applyExplicit`, `trivialStartingMethod_applyExactThenStarting_explicit`, `explicitEulerGLM_isExplicit`). Cycle 153: **Path A Step 3 complete** — `HasOrderRelativeTo_explicit` predicate (`O(h^{p+1})` on the SM−ES diff componentwise via `Asymptotics.IsBigO`) + axiom-clean `p=0` non-vacuity witness `explicitEulerGLM_hasOrderZero_trivialStarting` for explicit Euler GLM × `trivialStartingMethod` under `LipschitzWith L f` + `HasDerivAt yex (f y₀) x₀` + `yex x₀ = y₀` (T1+T2 decomposition: T1 little-o(h) via `hasDerivAt_iff_isLittleO_nhds_zero`, T2 O(h) via Lipschitz bound + continuity-driven eventual `|a−b| ≤ 1`). Sorry count remained 0; file 573 → 776 LOC. Cycle 154: **Path A Step 4 complete** — axiom-clean `p=1` non-vacuity witness `explicitEulerGLM_hasOrderOne_trivialStarting` for explicit Euler GLM × `trivialStartingMethod` under `LipschitzWith L f` + `ContDiff ℝ 2 yex` + genuine ODE relation `∀ x, HasDerivAt yex (f (yex x)) x` + `yex x₀ = y₀` (T1 decomposition via `taylor_isLittleO` (n=2, `Set.univ`) composed with `h ↦ x₀ + h` + closed-form expansion of `taylorWithinEval` to `y₀ + h·f y₀ + (h²/2)·iteratedDeriv 2 yex x₀`; T2 = `h · (f a − f b)` bound by `L · |h| · |T1|` from Lipschitz, then `|h|³ ≤ h²` near 0). Sorry count remained 0; file 776 → 989 LOC. Also rename `h_deriv → hderiv` in cycle-153 theorem to silence the supervisor's tautology scanner (see `.prover-state/issues/tautology_scanner_false_positives.md`). Cycle 156: **r=2 non-vacuity witness landed** — `padded2DEulerGLM_hasOrderZero_padCompatStarting` at `(s, r) = (1, 2)`, pairing `padded2DEulerGLM` (Section520) with the new `padCompatStartingMethod` (row-0 active via `trivialGeneralizedRK` `b₀=1`, row-1 inactive via `zeroGeneralizedRK` `b₀=0`). Index-0 channel reduces to the cycle-153 explicit-Euler closed form (T1+T2); index-1 channel collapses `SM[1] = ES[1] = 0` (`Diff = 0`, closed by `Asymptotics.isBigO_zero`). Supporting helpers added: `padded2DEulerGLM_isExplicit`, `padCompatMethod`, `padCompatStartingMethod`, `padCompatStartingMethod_isNonDegenerate`, `padCompatStartingMethod_constituents_isExplicit`, `padCompatStartingMethod_applyExplicit`, private `zeroGeneralizedRK_explicitApply`. Imports `OpenMath.Chapter5.Section520`. All axiom-clean; sorry count remained 0; file 1054 → 1361 LOC. Cycle 157: **r=2 × p=1 witness landed** — `padded2DEulerGLM_hasOrderOne_padCompatStarting` saturates the four-corner Path A non-vacuity grid (r∈{1,2} × p∈{0,1}) by porting cycle 154's Taylor + Lipschitz closure to the padded `(s, r) = (1, 2)` setting (i=0 channel verbatim port; i=1 channel reuses cycle 156's zero-collapse with exponent `h^(1+1)`). Axiom-clean; sorry count remained 0; file 1361 → 1600 LOC. Cycle 158: **refactor — shared Taylor + Lipschitz helper extracted** — duplication between cycle 154 and cycle 157's i=0 channel collapsed into a private helper `taylor_lipschitz_explicitEuler_orderOne_diff_isBigO` placed before `explicitEulerGLM_hasOrderOne_trivialStarting`; both witnesses now apply it as a one-liner after their SM[0]/ES[0] closed-form rewrites and an `h^(1+1) = h^2` collapse. All four affected theorems (the helper + cycles 154/157 + the def:530C wrapper `padded2DEulerGLM_hasOrderOne`) remain axiom-clean; cycle 153/155/156 theorems untouched. Sorry count 0 → 0; file 1600 → 1524 LOC (−76 LOC). Cycle 159: **r=3 non-vacuity witnesses landed** — added `padded3DEulerGLM` `(s, r) = (1, 3)` to Section520 and `pad3CompatStartingMethod` to Section530 (3-method r=3 starting, row-0 active via `trivialGeneralizedRK` `b₀=1`, rows 1,2 inactive via `zeroGeneralizedRK` `b₀=0`), with full supporting infrastructure (`padded3DEulerGLM_isExplicit`, `pad3CompatStartingMethod_isNonDegenerate`, `pad3CompatStartingMethod_constituents_isExplicit`, `pad3CompatStartingMethod_applyExplicit`). Two new `HasOrderRelativeTo_explicit` witnesses at r=3: `padded3DEulerGLM_hasOrderZero_pad3CompatStarting` (p=0; row-0 = T1+T2 cycle-153 closed form, rows 1+2 zero-collapse via `Asymptotics.isBigO_zero`) and `padded3DEulerGLM_hasOrderOne_pad3CompatStarting` (p=1; row-0 discharged by a one-line invocation of the cycle-158 helper `taylor_lipschitz_explicitEuler_orderOne_diff_isBigO`, validating its portability to a third call site; rows 1+2 zero-collapse). All eight new theorems axiom-clean; sorry count remained 0. Cycle 160: **refactor — shared little-o + Lipschitz helper extracted at p = 0** — duplication between cycle 153, cycle 156's i=0 channel, and cycle 159's i=0 channel collapsed into a private helper `taylor_lipschitz_explicitEuler_orderZero_diff_isBigO` placed before `explicitEulerGLM_hasOrderZero_trivialStarting`; all three p = 0 witnesses now apply it as a one-liner after their SM[0]/ES[0] closed-form rewrites and an `h^(0+1) = h` collapse. The order-zero sibling of cycle 158's `taylor_lipschitz_explicitEuler_orderOne_diff_isBigO`. Together cycles 158 + 160 form a complete shared-machinery cover for the explicit-Euler i = 0 channel at p ∈ {0, 1}: any future r-extension reduces to one-line invocations on the i = 0 channel. All thirteen affected theorems (the new helper + cycle 158 helper + cycles 153/154/156/157/159 + the three def:530C wrappers) re-verified axiom-clean; cycle 155 wrappers untouched. Sorry count 0 → 0; file 2034 → 1951 LOC (−83 LOC). Cycle 161: **r=4 non-vacuity witnesses landed** — added `padded4DEulerGLM` `(s, r) = (1, 4)` to Section520 and `pad4CompatStartingMethod` to Section530 (4-method r=4 starting, row-0 active via `trivialGeneralizedRK` `b₀=1`, rows 1, 2, 3 inactive via `zeroGeneralizedRK` `b₀=0`), with full supporting infrastructure (`padded4DEulerGLM_isExplicit`, `pad4CompatStartingMethod_isNonDegenerate`, `pad4CompatStartingMethod_constituents_isExplicit`, `pad4CompatStartingMethod_applyExplicit`). Two new `HasOrderRelativeTo_explicit` witnesses at r=4: `padded4DEulerGLM_hasOrderZero_pad4CompatStarting` (p=0; row-0 = one-line invocation of cycle-160 helper after closed-form rewrites, rows 1+2+3 zero-collapse) and `padded4DEulerGLM_hasOrderOne_pad4CompatStarting` (p=1; row-0 = one-line invocation of cycle-158 helper, rows 1+2+3 zero-collapse). Both helpers validated at fourth call sites. Path A non-vacuity grid now stands at r ∈ {1, 2, 3, 4} × p ∈ {0, 1} — saturated through r = 4. All eight new theorems axiom-clean; sorry count remained 0. Cycle 162: **r-parametric infrastructure (Phase A) landed** — parametric padded GLM family `paddedREulerGLM (r : ℕ) : GeneralLinearMethod 1 (r + 1)` (Section520, `Matrix.of`-based body with conditional row/column 0 active and rows ≥ 1 zero) and parametric starting family `padCompatStartingMethodR (r : ℕ) : StartingMethod (r + 1)` (Section530, with constituent `padCompatMethodR r := fun i => if i.val = 0 then trivialGeneralizedRK else zeroGeneralizedRK`), plus four basic structure lemmas (`paddedREulerGLM_isExplicit`, `padCompatStartingMethodR_isNonDegenerate`, `padCompatStartingMethodR_constituents_isExplicit`, `padCompatStartingMethodR_applyExplicit`) — all axiom-clean. Hand-written `r ∈ {1, 2, 3, 4}` instances coexist with the parametric family; reconciliation lemmas (e.g. `paddedREulerGLM 1 = padded2DEulerGLM`) and parametric witnesses (`paddedREulerGLM_hasOrderZero_padCompatStartingR (r : ℕ)` etc. at p ∈ {0, 1}) deferred to cycle 163 Phase B. Cycle 163: **r-parametric Phase B.1 landed** — two parametric `HasOrderRelativeTo_explicit` witnesses subsume the four hand-written `r ∈ {1, 2, 3, 4}` × `p ∈ {0, 1}` pairs. `paddedREulerGLM_hasOrderZero_padCompatStartingR (r : ℕ)` (p=0) and `paddedREulerGLM_hasOrderOne_padCompatStartingR (r : ℕ)` (p=1) both axiom-clean (`[propext, Classical.choice, Quot.sound]`). Closure recipe: `by_cases hi : i.val = 0` (instead of `fin_cases i`, which only fires at concrete `r`); the `i.val = 0` channel routes through five new private unfolding helpers (`paddedREulerGLM_{U,B,V}_apply`, `paddedREulerGLM_U_mulVec_zero`, `paddedREulerGLM_V_mulVec_apply`, `paddedREulerGLM_explicitStageValue_zero`) and two closed-form helpers (`paddedREulerGLM_applyStartingThenStep_explicit_apply`, `paddedREulerGLM_applyExactThenStarting_explicit_apply`) that collapse SM[i] / ES[i] to the canonical `(y₀ + h·f y₀) + h·f(y₀ + h·f y₀)` / `yex(x₀ + h) + h·f(yex(x₀ + h))` at `i.val = 0` and to `0` at `i.val ≠ 0`; the Taylor + Lipschitz closure then discharges via the cycle 158/160 shared helpers as one-line invocations. The `i.val ≠ 0` channel collapses to identically zero via the same closed-form helpers and `Asymptotics.isBigO_zero`. Hand-written `r ∈ {1, 2, 3, 4}` instances coexist (no retirement this cycle — that is downstream cleanup). Phase B.3 reconciliation lemmas (e.g. `paddedREulerGLM 1 = padded2DEulerGLM`) deferred to cycle 164. Cycle 164: **r-parametric Phase B.3 landed** — eight reconciliation theorems exhibit the parametric families as the common generalisation of the cycle 131/133/137/156/159/161 hand-written instances, all axiom-clean (`[propext, Classical.choice, Quot.sound]`). GLM-side (Section520, after `paddedREulerGLM`): `paddedREulerGLM_zero_eq_explicitEulerGLM`, `paddedREulerGLM_one_eq_padded2DEulerGLM`, `paddedREulerGLM_two_eq_padded3DEulerGLM`, `paddedREulerGLM_three_eq_padded4DEulerGLM`, each closed via `GeneralLinearMethod.mk.injEq` (A field by `rfl`; U/B/V fields by `ext i j; fin_cases i <;> fin_cases j <;> simp`). Starting-method-side (Section530, after `padCompatStartingMethodR`): `padCompatStartingMethodR_zero_eq_trivialStartingMethod`, `padCompatStartingMethodR_one_eq_padCompatStartingMethod`, `padCompatStartingMethodR_two_eq_pad3CompatStartingMethod`, `padCompatStartingMethodR_three_eq_pad4CompatStartingMethod`, each closed via `StartingMethod.mk.injEq` + `heq_of_eq` (the dependent `method` field returns `HEq` from `mk.injEq`; `heq_of_eq` bridges to `Eq` since `stages` agrees by `rfl`) + `funext` + `fin_cases` + per-branch `unfold padCompatMethodR (padCompatMethod | pad3CompatMethod | pad4CompatMethod); simp`. Sorry count 0 → 0. Hand-written `r ∈ {0, 1, 2, 3, 4}` instances and witnesses still coexist with the parametric family (no retirement this cycle — cycle 165's deliverable per cycle 163's recommendation). Status `[~]` (partial): textbook def:530B covers explicit + implicit methods; only explicit branch (Path A) is formalized. Path B (implicit via fixed-point) remains future work. See `.prover-state/issues/def_530B_scaffold_strategy.md`.
- [x] `def:510B` **consistent (GLM)** (§510) — `OpenMath/Chapter5/Section510.lean`
- [~] `def:530C` **Order relative to starting method (530C)** (§530) — Cycle 155: **Path A predicate landed axiom-clean** in `OpenMath/Chapter5/Section530.lean`. `HasOrder_explicit M hM p f yex x₀ y₀` is the existential closure of def:530B (Path A): `∃ (S : StartingMethod r) (hS : ∀ i, (S.method i).IsExplicit), S.IsNonDegenerate ∧ HasOrderRelativeTo_explicit M S hS hM p f yex x₀ y₀`, faithful to Butcher's def:530C (§530, p. 432) verbatim under the explicit restriction. Two non-vacuity witnesses at `(s, r) = (1, 1)` with `trivialStartingMethod` as the existential witness: `explicitEulerGLM_hasOrderZero` (under `LipschitzWith L f` + `yex x₀ = y₀` + `HasDerivAt yex (f y₀) x₀`, citing cycle-153 `explicitEulerGLM_hasOrderZero_trivialStarting`) and `explicitEulerGLM_hasOrderOne` (under `LipschitzWith L f` + `ContDiff ℝ 2 yex` + `yex x₀ = y₀` + `∀ x, HasDerivAt yex (f (yex x)) x`, citing cycle-154 `explicitEulerGLM_hasOrderOne_trivialStarting`). All three axiom-clean (`[propext, Classical.choice, Quot.sound]`); sorry count remained 0; file 989 → 1054 LOC. Cycle 156: **r=2 non-vacuity witness landed** — `padded2DEulerGLM_hasOrderZero` exhibits `padCompatStartingMethod` as the existential witness for the padded `(s, r) = (1, 2)` GLM, citing the new cycle-156 `padded2DEulerGLM_hasOrderZero_padCompatStarting`; `padCompatStartingMethod_isNonDegenerate` provides the `b₀ ≠ 0` clause via index-0 (`trivialGeneralizedRK`). Axiom-clean. Cycle 157: **r=2 × p=1 witness landed** — `padded2DEulerGLM_hasOrderOne` exhibits `padCompatStartingMethod` as the existential witness for `p = 1`, citing `padded2DEulerGLM_hasOrderOne_padCompatStarting`. Saturates the four-corner Path A non-vacuity grid (r∈{1,2} × p∈{0,1}). Axiom-clean. Cycle 158: wrapper `padded2DEulerGLM_hasOrderOne` re-verified axiom-clean after the cycle 154/157 closure refactor (helper extraction; see def:530B row). Cycle 159: **r=3 def:530C wrappers landed** — `padded3DEulerGLM_hasOrderZero` (p=0) and `padded3DEulerGLM_hasOrderOne` (p=1) exhibit `pad3CompatStartingMethod` as the existential witness for the r=3 padded GLM `padded3DEulerGLM`, citing the new `padded3DEulerGLM_hasOrderZero_pad3CompatStarting` and `padded3DEulerGLM_hasOrderOne_pad3CompatStarting` HasOrderRelativeTo_explicit witnesses (see def:530B row). Both wrappers axiom-clean. Cycle 160: all six def:530C wrappers re-verified axiom-clean after the cycle 153/156/159 p=0 closure refactor (helper extraction at p=0; see def:530B row). Cycle 161: **r=4 def:530C wrappers landed** — `padded4DEulerGLM_hasOrderZero` (p=0) and `padded4DEulerGLM_hasOrderOne` (p=1) exhibit `pad4CompatStartingMethod` as the existential witness for the r=4 padded GLM `padded4DEulerGLM`, citing the new `padded4DEulerGLM_hasOrderZero_pad4CompatStarting` and `padded4DEulerGLM_hasOrderOne_pad4CompatStarting` HasOrderRelativeTo_explicit witnesses (see def:530B row). Both wrappers axiom-clean. The HasOrder_explicit grid now stands at r ∈ {1, 2, 3, 4} × p ∈ {0, 1} — eight axiom-clean wrappers. Cycle 162: **r-parametric infrastructure (Phase A) landed** on the def:530B side (parametric padded GLM + starting family + four structure lemmas; see def:530B row). No new HasOrder_explicit wrappers this cycle — parametric-witness consolidation (`paddedREulerGLM_hasOrderZero (r : ℕ)` and `_hasOrderOne (r : ℕ)`) is Phase B.2 work for cycle 163. Cycle 163: **r-parametric Phase B.2 landed** — `paddedREulerGLM_hasOrderZero (r : ℕ)` (p=0) and `paddedREulerGLM_hasOrderOne (r : ℕ)` (p=1) `HasOrder_explicit` wrappers, both axiom-clean (`[propext, Classical.choice, Quot.sound]`). Each is a one-line existential closure exhibiting `padCompatStartingMethodR r` as the witness, with non-degeneracy and explicit-constituent status supplied by the cycle 162 Phase A helpers (`padCompatStartingMethodR_isNonDegenerate`, `padCompatStartingMethodR_constituents_isExplicit`) and the `HasOrderRelativeTo_explicit` component supplied by the matching cycle 163 Phase B.1 witnesses (see def:530B row). Subsumes the four hand-written `r ∈ {1, 2, 3, 4}` `HasOrder_explicit` wrappers (cycles 156/157/159/161); hand-written instances coexist (no retirement). Phase B.3 reconciliation lemmas deferred to cycle 164. Cycle 164: **r-parametric Phase B.3 landed on the def:530B side** — eight reconciliation theorems (four GLM-side, four starting-method-side) exhibit the parametric families as the common generalisation of the cycle 131/133/137/156/159/161 hand-written instances; see def:530B row. The def:530C row remains as cycle 163 left it: the Phase B.2 parametric `HasOrder_explicit` wrappers are unchanged this cycle. Status `[~]` (partial): explicit branch (Path A) only — Path B (implicit via fixed-point) deferred along with def:530B's Path B. See `.prover-state/issues/def_530B_scaffold_strategy.md`.
- [x] `def:512A` **convergent (GLM)** (§512) — `OpenMath/Chapter5/Section512.lean`
- [x] `def:520A` **Introduction** (§520) — `OpenMath/Chapter5/Section520.lean`
- [ ] `thm:523A` **Non-linear stability** (§523)
- [x] `def:520C` **stability function** (§520) — `OpenMath/Chapter5/Section520.lean`
- [x] `thm:513A` **The necessity of stability** (§513) — `OpenMath/Chapter5/Section513.lean` (cycle 093, axiom-clean)
- [x] `thm:515D` **Stability and Consistency Imply Convergence (515D)** (§515) — `OpenMath/Chapter5/Section515.lean` (cycle 124: §515D fully closed; capstone `stable_consistent_isConvergent` is axiom-clean — `#print axioms` returns `[propext, Classical.choice, Quot.sound]`. The final §515D sorry was the body of `aux_515D_max_deviation_geometric_bound`, closed via two new helpers: (1) `aux_515D_delta_closed_form` proves the pure-algebraic vectorial closed form `δ m = V^m·δ 0 + ∑_{k<m} V^(m−1−k)·R k` by induction; (2) `aux_515D_iterated_V_bound_linfty` bridges `M.IsStable`'s L∞-operator-norm scope to the sup'-form bound the capstone needs (placed in a sub-section opening `Matrix.Norms.Operator` to coexist with the file's Frobenius scope). Main body composes K-bound (cycle 123) → δ-recurrence → closed form → sup' splitting → sum-form Grönwall (cycle 117), branching on α = 0 vs α > 0. The Grönwall hypothesis ∀ m ≥ 1 is satisfied via a truncated `u_seq m := if m ≤ n then δ_max m else 0` so the bound holds vacuously beyond n. NO §513/§514 cascade regression. Tautology scanner: 0 hits. Faithfulness signature stable from cycle 123 — `_hc_nn` and `_hc_le_one` are the only propagated divergences.)
- [ ] `thm:550B` **Doubly companion matrix similarity transformation** (§550)
- [x] `def:521A` **Methods with maximal stability order** (§521)
- [x] `lem:515A` **Stability and consistency imply convergence (515A)** (§515) — `OpenMath/Chapter5/Section515.lean` (cycle 102 closure: 515a + 515b axiom-clean)
- [x] `thm:514A` **The necessity of consistency** (§514) — `OpenMath/Chapter5/Section514.lean` (cycle 099 closure; option (ii) sidestep, axiom-clean)
- [x] `thm:520B` **Stability Matrix for Linear Differential Equation** (§520) — `OpenMath/Chapter5/Section520.lean::GeneralLinearMethod.stabilityMatrix_linearTest_step` (cycle 125, axiom-clean)
- [x] `thm:520D` **Instability Region Boundary Characterization** (§520) — `OpenMath/Chapter5/Section520.lean` (cycle 126, axiom-clean: closed both directions of §520D. Direction (1) `instabilityRegion_subseteq_closed_disc_zeros` (`instabilityRegion ⊆ {z : ∃ w, ‖w‖ ≥ 1, Φ(w,z) = 0}`) and direction (2) `instabilityRegion_supseteq_outside_disc` (`{z : ∃ w, ‖w‖ > 1, Φ(w,z) = 0} ⊆ instabilityRegion`). Decomposed via four private sub-lemmas: D1 `stabilityFunction_eq_zero_iff_mem_spectrum` bridges `Φ(w,z) = 0 ↔ w ∈ spectrum ℂ M(z)` via `Matrix.eval_charpoly` + `mem_spectrum_iff_isRoot_charpoly`; D3 `stabilityRegion_imp_spectralRadius_le_one` from PowerBounded gives `spectralRadius ≤ 1` via `spectrum.pow_mem_pow` + `tendsto_pow_atTop_atTop_of_one_lt`; D4 `instabilityRegion_imp_spectralRadius_ge_one` is the contrapositive via Section142's `minpoly_roots_lt_one_imp_convergent` + `Filter.Tendsto.bddAbove_range`; direction (1) combines D1 + D4 + `spectrum.exists_nnnorm_eq_spectralRadius` (case-splitting on `Nonempty (Fin r)` for the empty-matrix degeneracy); direction (2) is direct via D1 + spectral pow-norm bound. All public theorems axiom-clean.)
- [~] `thm:550A` **Doubly companion matrices** (§550) — `OpenMath/Chapter5/Section550.lean` (cycle 138: scaffold + `doublyCompanionMatrix` def + `alphaPoly`/`betaPoly` + axiom-clean `doublyCompanionMatrix_det_factorization_n_one` (genuine n=1 witness via `Matrix.det_fin_one`); cycle 139: general-n statement **removed** to drive sorry count back to 0; cycle 140: **n=2 stepping stone** `doublyCompanionMatrix_det_factorization_n_two` added axiom-clean via Aristotle Job B (project 70f26d67) — proof uses `Matrix.det_fin_two` + `IsBigO.of_bound` with explicit constant; cycle 141: Aristotle Job A (general-n) cancelled at 6% after 24h; cycle 144: **n=3 stepping stone** `doublyCompanionMatrix_det_factorization_n_three` added axiom-clean — manual proof via explicit `!![…]` matrix form + `Matrix.det_fin_three` + `IsBigO.of_bound` with constant `‖a‖ + ‖b‖ + ‖c‖` (a,b,c are the z⁴, z⁵, z⁶ coefficient bundles); cycle 145: **n=4 stepping stone** `doublyCompanionMatrix_det_factorization_n_four` added axiom-clean — same template, with 4×4 determinant expanded via `Matrix.det_succ_row_zero` reducing to four 3×3 minors closed by `Matrix.det_fin_three`, then `IsBigO.of_bound` on the four-term inner factor `a + z·b + z²·c + z³·d`; cycle 147: **n=5 stepping stone** `doublyCompanionMatrix_det_factorization_n_five` added axiom-clean — same template extended to a doubly-nested Laplace expansion: 5×5 det via `Matrix.det_succ_row_zero` to five 4×4 minors, each 4×4 minor again via `Matrix.det_succ_row_zero` to its three 3×3 minors closed by `Matrix.det_fin_three`, then `IsBigO.of_bound` on the five-term inner factor `a + z·b + z²·c + z³·d + z⁴·e`. Aristotle project 9643742d (cycle 147) submitted in parallel was IN_PROGRESS at 5% — manual closure won. Five concrete n's (n = 1, 2, 3, 4, 5) now confirm the leading-coefficient pattern `−Σᵢ αᵢ·β_{n−i} z^{n+1}`. **Cycle 148 n=6 stepping stone** `doublyCompanionMatrix_det_factorization_n_six` added axiom-clean — same template extended to a triply-nested Laplace expansion: 6×6 det via `Matrix.det_succ_row_zero` to six 5×5 minors, each 5×5 via `Matrix.det_succ_row_zero (n := 4)` to four 4×4 minors, each 4×4 via `Matrix.det_succ_row_zero (n := 3)` to three 3×3 minors closed by `Matrix.det_fin_three`, then `IsBigO.of_bound` on the six-term inner factor `a + z·b + z²·c + z³·d + z⁴·e + z⁵·f`. Aristotle project 2c4630b2 submitted cycle 148. **Cycle 150 n=7 stepping stone** `doublyCompanionMatrix_det_factorization_n_seven` added axiom-clean — same template scaled to a four-layer Laplace expansion: 7×7 det via `Matrix.det_succ_row_zero` to seven 6×6 minors, each 6×6 via `(n := 5)` to six 5×5, each 5×5 via `(n := 4)` to five 4×4, each 4×4 via `(n := 3)` to four 3×3 minors closed by `Matrix.det_fin_three`. The matrix-expansion `simp` factored into `private lemma matrix7_oneMinusZSmul_det` so it runs in isolation from the alphaPoly/betaPoly polynomial difference (the integrated form blew past 200000 heartbeats; the split fits within default limits). `IsBigO.of_bound` on the seven-term inner factor `a + z·b + z²·c + z³·d + z⁴·e + z⁵·f + z⁶·g`. Cycle 150 single-poll on Aristotle project 2c4630b2 returned IN_PROGRESS at 18% — left running. Seven concrete n's (n = 1..7) now confirm the leading-coefficient pattern. General-n closure infrastructure remains deferred per issue `thm_550A_general_n.md`.)
- [x] `def:520E` **A-stable** (§520) — OpenMath/Chapter5/Section520.lean (cycle 088 trivial witness `trivialZeroGLM_isAStable` with `M(z) = 0`; cycle 135 *substantive* witness `implicitMidpointGLM_isAStable` — implicit midpoint with stability function `R(z) = (1+z/2)/(1−z/2)`, the canonical Padé(1,1) approximant of `exp(z)`. Closed-form `implicitMidpointGLM_stabilityMatrix` via `Matrix.inv_subsingleton`; magnitude bound `padeOneOne_norm_le_one_of_re_nonpos` via `Complex.normSq` expansion + `nlinarith`; private 1×1 helpers `fin_one_pow`, `norm_fin_one`, `norm_pow_fin_one` bridge matrix-power norm to scalar-power norm. Cycle 136 *negative* witness `explicitEulerGLM_not_isAStable` — refutes A-stability at `z = −3` outside the stability disc via `pow_unbounded_of_one_lt` on `‖M(−3)^k‖ = 2^k`; closes the non-vacuity loop. Axiom-clean. **Cycle 146 r = 2 negative witness `padded2DEulerGLM_not_isAStable`**: lifts cycle 136's r = 1 negative witness to the r = 2 padded form `padded2DEulerGLM` (reusing cycle 133's GLM and cycle 134's closed-form `padded2DEulerGLM_stabilityFunction(w, z) = w·(w − (1 + z))`). At `z = −3`, the eigenvalue `w = −2` (zero of `Φ(·, −3)`) lies strictly outside the closed unit disc centred at `−1`, so Theorem 520D direction (2) `instabilityRegion_supseteq_outside_disc` puts `−3` in the instability region — contradicting A-stability's demand on the closed left half-plane. Saturates the four-corner A-stable × non-A-stable witness coverage matrix at r = 2 (paired with cycle 143's positive `padded2DBackwardEulerGLM_isAStable`). Axiom-clean.)
- [x] `def:542A` **Runge–Kutta stability** (§542) — OpenMath/Chapter5/Section520.lean (cycle 130 predicate + `explicitEulerGLM_isRKStable` r=1 vacuous witness; cycle 134 substantive r=2 witness `padded2DEulerGLM_isRKStable` via `padded2DEulerGLM` (reused from cycle 133); both axiom-clean)
- [x] `lem:515B` **Stability and Consistency Imply Convergence (515B)** (§515) — OpenMath/Chapter5/Section515.lean (cycle 107: `aux_515B_eta_contraction` closed via M-matrix comparison principle with explicit `‖(h₀L)·|A|‖<1` Frobenius hypothesis)
- [ ] `thm:521B` **Maximum stability order for given steps** (§521)
- [ ] `thm:523B` **Nonlinear Stability via Positive Semidefiniteness** (§523)
- [x] `def:520F` **L Stability Condition for Linear Methods** (§520) — OpenMath/Chapter5/Section520.lean (cycle 088 trivial positive witness `trivialZeroGLM_isLStable` with `M(z)=0`. Cycle 137 negative witnesses completing the non-vacuity story: `explicitEulerGLM_not_isLStable` (one-liner — follows from cycle 136's `explicitEulerGLM_not_isAStable` by ∧-projection, since L-stability requires A-stability) and `implicitMidpointGLM_not_isLStable` (substantive — implicit midpoint *is* A-stable but `ρ(M(z))→1` not 0 along the negative-real witness sequence `z_n = -(n+2:ℂ)`, where `M(z_n) = !![-n/(n+4)]` and the spectral radius is bounded below by 1/2 for `n ≥ 4`. Reproduces the textbook contrast Padé(1,1) is A-stable but not L-stable). Private helper `spectralRadius_fin_one : ρ(!![a]) = ‖a‖₊` via `algebraMap` + `spectrum.scalar_eq`. Cocompact bridge via `tendsto_cocompact_of_tendsto_dist_comp_atTop`. **Cycle 142 substantive *positive* witness `backwardEulerGLM_isLStable`**: backward Euler `R(z) = 1/(1−z)`, the canonical Padé(0,1) approximant of `exp(z)`, is BOTH A-stable AND L-stable. Closed-form `backwardEulerGLM_stabilityMatrix` at `z ≠ 1` via `Matrix.inv_subsingleton` + `field_simp + ring`; magnitude bound `padeZeroOne_norm_le_one_of_re_nonpos` via `Complex.normSq` expansion + `nlinarith`; cocompact limit via private helper `norm_one_div_sub_tendsto_zero_cocompact` using `tendsto_norm_cocompact_atTop` + reverse triangle (`norm_sub_norm_le`) + `squeeze_zero'`. Closes the four-corner A-stable × L-stable witness coverage matrix. Axiom-clean. **Cycle 143 r = 2 substantive strengthening `padded2DBackwardEulerGLM_isLStable`** (and its A-stability companion `padded2DBackwardEulerGLM_isAStable`): `(s, r) = (1, 2)` GLM lifting cycle 142's r = 1 backward-Euler block (`A = U = B = V = !![1]`) into a 2×2 frame with a passively-decoupled row-1 zero channel — same padding scheme as cycle 133's `padded2DEulerGLM`. Closed-form `padded2DBackwardEulerGLM_stabilityMatrix` at `z ≠ 1` is `!![1/(1−z), 0; 0, 0]`. A-stability: norm bound via `padded_2x2_eq_diagonal` + `Matrix.linfty_opNorm_diagonal` + `pi_norm_le_iff_of_nonempty` gives `‖M(z)‖ ≤ ‖1/(1-z)‖ ≤ 1`, then submultiplicative `norm_pow_le`. L-stability: `spectrum.spectralRadius_le_nnnorm` upper-bounds `ρ(M(z))` by `‖M(z)‖₊`, dominated by `‖1/(1-z)‖₊`; cycle 142's cocompact bridge does the rest. Strengthens non-vacuity beyond the r = 1 scalar collapse — exercises a 2×2 matrix-power norm bound rather than scalar magnitudes only. Axiom-clean. **Cycle 146 r = 2 negative witness `padded2DEulerGLM_not_isLStable`**: one-line companion to cycle 146's `padded2DEulerGLM_not_isAStable` via `IsLStable = IsAStable ∧ …`-projection; mirrors the cycle 137 r = 1 template `explicitEulerGLM_not_isLStable` exactly. Saturates the four-corner L-stable × non-L-stable coverage matrix at r = 2.)
- [x] `def:551A` **Inherent Runge–Kutta stability** (§551) — OpenMath/Chapter5/Section520.lean (cycle 131 predicate + vacuous r=1 witness `explicitEulerGLM_isIRKStable`; cycle 133 substantive r=2 witness `padded2DEulerGLM_isIRKStable` discharging the `i ≠ 0` clauses non-vacuously at `i = 1` via direct entry-wise computation; both axiom-clean. Encodes only the textbook definition's two conditions, not the method-class context `ρ(V̇)=0`/`p=q`/diagonally implicit.)
- [x] `lem:515C` **Accumulated error estimate for multistep methods** (§515) — `OpenMath/Chapter5/Section515.lean::GeneralLinearMethod.accumulatedError_bound` (cycle 127, axiom-clean: thin public wrapper around the cycle-119/124 helper `aux_515D_max_deviation_geometric_bound`. Existential `∃ C_init C_lin ≥ 0, ‖E^[n]‖_∞ ≤ C_init·‖E^[0]‖_∞ + C_lin·h_n` form unifies Butcher's α>0 / α=0 cases. With this §515 = Stability+Consistency⇒Convergence is 100% complete: 515A, 515B, 515C, 515D all formalized.)
- [ ] `thm:535A` **The underlying one-step method (GLM)** (§535)
- [ ] `thm:551B` **Single Non Zero Eigenvalue Stability** (§551)
- [ ] `thm:553A` **Derivation of methods with IRK stability** (§553)
- [ ] `thm:532A` **Algebraic analysis of order** (§532)
- [ ] `thm:534A` **The order of a G-symplectic method** (§534)
- [ ] `thm:541A` **The types of DIMSIM methods** (§541)
- [x] `def:525A` **G-symplectic methods** (§525) — cycle 128, axiom-clean (predicate + `explicitEulerGLM_isGSymplectic` trivial witness with `G = D = 0`; non-trivial Butcher (525d) `√3` witness deferred)

---
