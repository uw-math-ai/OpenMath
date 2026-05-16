# Cycle 311 Results

## Worked on

Phase 3.2 of the §342 ↔ §321 Gauss–Legendre `RKTableau` lift: shipping
the `D(n)` prong of `cor:342D` via the textbook polynomial-antiderivative
+ IBP recipe (Butcher §342 p. 240). Cycle 310 had shipped `C(n)`; cycle
309 had shipped `B(2n)`. Cycle 311 closes the `D(n)` half.

Deliverables (all in `OpenMath/Chapter3/Section342.lean`, appended after
cycle 310's `butcherGaussLegendreRK_satisfiesC` non-vacuity witnesses):

* `butcherShiftedLegendre_lagrangeAntideriv (n : ℕ) (j : Fin n) : Polynomial ℝ`
  — Phase A: explicit polynomial antiderivative of the Lagrange basis
  `L_j := Lagrange.basis Finset.univ (butcherShiftedLegendre_zeros n) j`.
  Built term-by-term from `Polynomial.as_sum_range L_j`:
  `F_j := ∑ k ∈ range (L_j.natDegree + 1), C(L_j.coeff k / (k+1)) · X^(k+1)`.
* `butcherShiftedLegendre_lagrangeAntideriv_derivative` (Phase A.1) —
  `(F_j).derivative = L_j`. Recipe: `Polynomial.derivative_sum` +
  per-summand `Polynomial.derivative_C_mul_X_pow` (which gives
  `C(a · ↑(k+1)) · X^k` for our summand `C(c_k/(k+1)) · X^(k+1)`)
  + cast + `field_simp` to collapse the coefficient to `c_k`,
  then `Polynomial.as_sum_range L_j` + `Polynomial.C_mul_X_pow_eq_monomial`
  to reconstitute `L_j` as a sum of monomials.
* `butcherShiftedLegendre_lagrangeAntideriv_eval_zero` (Phase A.2) —
  `F_j.eval 0 = 0` via `Polynomial.eval_finset_sum` +
  `zero_pow (Nat.succ_ne_zero k)` per summand.
* `butcherShiftedLegendre_lagrangeAntideriv_natDegree_le` (Phase A.3) —
  `F_j.natDegree ≤ n`. `Polynomial.natDegree_sum_le_of_forall_le` +
  per-summand bound `natDegree_mul_le` + `Lagrange.natDegree_basis` =
  `n - 1`. Uses `0 < n` derived from `j : Fin n` via
  `lt_of_le_of_lt (Nat.zero_le _) j.isLt`.
* `butcherShiftedLegendre_lagrangeAntideriv_eval_integral` (Phase A.4) —
  FTC bridge: `F_j.eval c = ∫₀^c L_j(x) dx` for any `c : ℝ`. Routes
  through `intervalIntegral.integral_eq_sub_of_hasDerivAt` +
  `Polynomial.hasDerivAt` (lifted via Phase A.1's derivative identity).
* `butcherShiftedLegendre_integral_X_pow_lagrange_basis` (Phase B) —
  `∫₀¹ x^k · L_j(x) dx = b_j · c_j^k` for `k ≤ n`. Apply cycle 304's
  `butcherShiftedLegendre_quadrature_exact_lt_two_n` on the polynomial
  `φ := X^k · L_j` (which has `natDegree ≤ k + (n-1) ≤ 2n − 1 < 2n`);
  collapse the resulting quadrature sum via the Kronecker-delta
  property `L_j(c_i) = δ_{ij}` (`Lagrange.eval_basis_self`,
  `Lagrange.eval_basis_of_ne`, exactly as cycle 305's uniqueness proof).
* **Headline** `butcherGaussLegendreRK_satisfiesD (n : ℕ) :
  (butcherGaussLegendreRK n).SatisfiesD n` (Phase C) — the §321 `D(n)`
  adjoint order condition holds for the general-`n` Gauss–Legendre
  `RKTableau`. Recipe: substitute `A_ij = F_j(c_i)` (Phase A.4 at
  c = c_i); recognise LHS as the `2n`-degree-exact quadrature of
  `φ := X^(k-1) · F_j` (since `F_j.natDegree ≤ n` and `(k-1) + n ≤
  2n - 1`); equate to `∫₀¹ x^(k-1) · F_j(x) dx`; IBP via the file's
  existing `poly_ibp` helper with `u := F_j`, `v := C(1/k) · X^k`;
  boundary terms `F_j(1) = ∫₀¹ L_j = b_j` (Phase A.4 at c = 1)
  and `F_j(0) = 0` (Phase A.2); remainder
  `∫₀¹ L_j(x) · (1/k) · x^k dx = (1/k) · b_j · c_j^k` (Phase B
  pulled through `intervalIntegral.integral_const_mul`). Final
  `field_simp; ring` closes the arithmetic identity
  `b_j / k - (1/k) · b_j · c_j^k = b_j / k · (1 - c_j^k)`.
* Non-vacuity examples: `(butcherGaussLegendreRK 2).SatisfiesD 2` and
  `gaussLegendre1Stage.SatisfiesD 1` (round-trip through cycle 308's
  coincidence theorem `butcherGaussLegendreRK_one_eq_gaussLegendre1Stage`).

## Approach

Followed the strategy's Phase A → B → C decomposition verbatim. The
non-trivial design decisions:

1. **`butcherGaussLegendreRK_satisfiesD` signature drops `(hn : 0 < n)`**.
   The strategy proposed `(hn : 0 < n)` in the signature, but `SatisfiesD`
   on `Fin n` is already vacuous at `n = 0` (no `j : Fin 0`). Derived
   `hn` inside the proof from `j : Fin n` via
   `lt_of_le_of_lt (Nat.zero_le _) j.isLt`. Matches cycle 310's
   `butcherGaussLegendreRK_satisfiesC` signature exactly (no `hn`).
2. **`set v / set L` carefully**. After `set v := butcherShiftedLegendre_zeros n`,
   downstream tactics sometimes show the unfolded `butcherShiftedLegendre_zeros n`
   instead of `v` (because `set` uses `let` and Lean can normalise through
   it). Avoided `rw [hv_def]` patterns that fail when the term has already
   been unfolded; substituted with `have hL_eq : L = Lagrange.basis ... ` +
   `rw [hL_eq]` when crossing into the Phase B lemma call.
3. **No Aristotle this cycle**. Strategy §E (Risk register) explicitly
   excluded Aristotle for this cycle: D(n) is a structural IBP proof,
   not a premise-search problem. Cycle 282's (342f) Aristotle attempt
   stalled twice for similar reasons.

## Result

**SUCCESS — full Phase A + B + C + non-vacuity examples shipped.**

* `lake env lean OpenMath/Chapter3/Section342.lean` exits 0.
* `lake env lean OpenMath/Chapter3.lean` (aggregator) exits 0.
* `grep -c sorry OpenMath/Chapter3/Section342.lean` returns 0.
* `lean_verify OpenMath.Chapter3.Section342.butcherGaussLegendreRK_satisfiesD`
  returns `[propext, sorryAx, Classical.choice, Quot.sound]` — same
  axiom profile as cycle 310's `satisfiesC` (and cycles 308/309's
  `satisfiesB`). The `sorryAx` is the pre-existing upstream leak from
  cycle 301's `_rootsInIoo_card_ge`, not a cycle 311 regression.
* Both non-vacuity witnesses compile (`SatisfiesD 2` at `n = 2` and the
  `gaussLegendre1Stage.SatisfiesD 1` round-trip).

LOC delta: roughly **+340 LOC** (Phase A ~120, Phase B ~50, Phase C ~110,
section header + comments + non-vacuity ~60). File grew from 7097 to
roughly 7440 LOC.

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

* **`butcherShiftedLegendre_lagrangeAntideriv`** (private noncomputable def):
  Internal construction (no `entities/` JSON). Captures the standard
  textbook polynomial antiderivative of `L_j` via term-by-term
  integration of `as_sum_range`. The four lemmas (A.1–A.4) prove its
  defining algebraic and analytic properties.
* **`butcherShiftedLegendre_integral_X_pow_lagrange_basis`** (Phase B):
  Internal lemma. Specialisation of Butcher's Gaussian quadrature
  exactness (`lem:342B`) to the test polynomial `X^k · L_j`. Captures:
  same content as the textbook reduction.
* **`butcherGaussLegendreRK_satisfiesD`** (headline):
  Entity ID `cor:342D` partial — third prong (D(n)) only. From
  `extraction/formalization_data/entities/cor_342D.json` the corollary's
  full statement is the iff "order 2s ⇔ (i) c = P_s^* zeros + (ii) B(s) +
  (iii) C(s)", but Butcher's proof routes through D(s) as an
  intermediate (`E(s,s) + B(2s) ⇒ D(s)`), and §342 uses the `D(s)`
  predicate in its own derivation. The `D(n)` adjoint condition is
  defined in `OpenMath/Chapter3/Section321.lean`:111–114 exactly as in
  Butcher §321 equation (321d): `∀ j, ∀ k ∈ [1, ζ], ∑ᵢ bᵢ cᵢ^{k-1} aᵢⱼ
  = (bⱼ/k)(1 - cⱼ^k)`. Our theorem says the canonical Gauss–Legendre
  RKTableau (collocation A, Lagrange weights b, shifted Legendre zeros
  c) satisfies this. Lean statement captures: **same content as the
  textbook D(n) condition specialised to the canonical Gauss–Legendre
  tableau.** No divergence; no extra hypothesis (`hn` derived from
  `j : Fin n`).

No `axiom` or `constant` declarations introduced. No `class` or
`structure` introduced. No tautologies (conclusion ≠ any hypothesis
for every new theorem; final goal `b_j/k · (1 - c_j^k)` does not appear
verbatim as a hypothesis). No identity proofs (`:= h_*`, `exact h_*`,
`:= id` patterns absent in cycle 311 additions). No definition smuggling
(the antiderivative is an *explicit polynomial*, not a Prop-field
structure).

## Dead ends

* Initial Phase B closure used `Lagrange.eval_basis_of_ne hij ...` —
  failed because the lemma's argument order needs `hij.symm`
  (the basis-index goes second in `Lagrange.basis _ v j`, the eval-point
  index goes first in `eval (v i)`). Fixed by routing through a `have
  h0 : ... = 0 := Lagrange.eval_basis_of_ne hij.symm (Finset.mem_univ i)`
  then `rw [h0]`.
* Initial Phase C used `rw [hL_def, hv_def]` to recover the
  `Lagrange.basis Finset.univ (butcherShiftedLegendre_zeros n) j` form
  before applying the Phase B lemma. The `rw [hv_def]` failed because
  `v` had been definitionally unfolded by intermediate tactics. Fixed
  by replacing with an explicit `have hL_eq : L = Lagrange.basis ...
  (butcherShiftedLegendre_zeros n) j := by rw [hL_def]` and `rw
  [hL_eq]` (a one-step rewrite that doesn't depend on `v` being
  syntactically present).
* Initial `Nat.add_sub_cancel` usage assumed Mathlib's signature
  matches the auto-derived one — actual lemma is
  `Nat.add_sub_cancel : ∀ (n m : ℕ), n + m - m = n` (no implicit args),
  but at the use site Lean wanted `k + 1 - 1 = k`. Swapped to `by omega`.

## Discovery

* **`Polynomial.derivative_C_mul_X_pow` gives the right shape for
  term-by-term polynomial integration**: it produces `C (a · ↑n) · X^(n-1)`
  which collapses cleanly when `a := c_k/(k+1)` and `n := k+1`, yielding
  `C c_k · X^k` after `field_simp` + cast. The combo
  `Polynomial.derivative_C_mul_X_pow` + `Polynomial.as_sum_range` +
  `Polynomial.C_mul_X_pow_eq_monomial` is the cleanest path for proving
  derivative identities on explicit polynomial antiderivatives.
* **The file's existing `poly_ibp` helper** (line 1377, private) — clean
  specialisation of `intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt`
  to polynomial evaluations on `[0, 1]` — was exactly the right primitive
  for Phase C. Used as-is without modification. Strategy §D-R4 flagged
  the IBP-signature risk but the file's helper sidesteps it entirely.
* **`set v` with let-binding does NOT survive arbitrary tactic chains**.
  When `rw` produces a term containing `v`, subsequent tactics
  (especially congr-based ones from `intervalIntegral.integral_congr`)
  may definitionally normalise `v` back to its body. The robust pattern
  is to use `have hL_eq : L = <full expression>` + `rw [hL_eq]` rather
  than relying on `rw [hL_def, hv_def]` to recover the unfolded form.

## Suggested next approach

Cycle 312 priorities (in order):

1. **`thm:342C`** — the iff "RK order 2s ⇔ B(2s) + C(s) + D(s)". With
   cycles 309/310/311 supplying the three RHS prongs for the canonical
   Gauss–Legendre tableau, the forward direction (⟸) of `thm:342C`
   would now follow from the §321 "simplifying assumptions theorem"
   (currently unformalized). The reverse direction is a Vandermonde
   argument. Plausible 1–2 cycle target after a quick scan of §321's
   simplifying-assumptions infrastructure.
2. **§314A elementary-weight argument** — prerequisite for the full
   `cor:342D` iff statement. Multi-cycle (per strategy §F.2).
3. **`cor:342D` end-to-end** — once both `thm:342C` and `thm:314A`
   are available, the iff is a several-line corollary.
4. **`sorryAx` cleanup audit** — the cycle 301
   `_rootsInIoo_card_ge` upstream leak propagates through every §342
   theorem consuming `_zeros`. Auditing and closing that sorry would
   clean up the axiom profile of every cycle 308–311 deliverable.
   Recommended as a defensive cycle after `thm:342C` lands.

Also worth considering: an `E(n, n)` lift companion to the cycle
311 `D(n)` lift, which would close the §342 ↔ §321 bridge for the
full four-prong B/C/D/E quadrature characterisation. The IBP recipe
in Phase C generalises to `E(n, n)` via a double-sum manipulation;
plausible 2-cycle target.
