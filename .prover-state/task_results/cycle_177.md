# Cycle 177 Results

## Worked on

`lem:441A` Phase B.3 Step 1 — `ρ > 0` on `(1, ∞)` for stable
preconsistent k-step LMMs (Butcher §441 p. 376, the implicit step
between "no real root > 1" + "ρ(1) = 0" + "ρ → +∞" and the
`ρ'(1) > 0` consequence).

## Approach

Followed the cycle 177 strategy verbatim:

1. **Verified the cycle 176 phantom**: `git rev-parse HEAD = origin/Main/Experiments = 0b171c9`,
   Section441.lean has all 3 cycle-176 theorems at lines 531/599/689,
   `lake env lean` exits 0 with 0 sorries. Cycle 176 landed.

2. **Built four private leading-coefficient helpers**
   (in `OpenMath.Chapter4.Section404` namespace):

   * `LinearMultistepMethod.ρPoly_coeff_top_eq_one`: `M.ρPoly.coeff k = 1`.
     Used `Polynomial.coeff_sub_eq_left_of_lt` after bounding the
     subtracted-sum natDegree by `k − 1` via
     `Polynomial.natDegree_sum_le_of_forall_le` + each summand's
     `natDegree_C_mul_X_pow_le _ _ ≤ k − (i.val + 1) ≤ k − 1`. Closed
     with `Polynomial.coeff_X_pow` + `if_pos rfl`. ~25 LOC.

   * `LinearMultistepMethod.ρPoly_natDegree_eq_k`: `M.ρPoly.natDegree = k`.
     `Nat.le_antisymm` of cycle 172's `ρPoly_natDegree_le` and a
     `Polynomial.le_natDegree_of_ne_zero` lift of Helper 1's `coeff k = 1`.
     ~5 LOC.

   * `LinearMultistepMethod.ρPoly_leadingCoeff_eq_one`: combine the
     definition `leadingCoeff = coeff natDegree` with Helpers 1+2.
     ~3 LOC body.

   * `LinearMultistepMethod.ρPoly_tendsto_atTop`: `(fun z : ℝ => ρ.eval z) → +∞`
     via `Polynomial.tendsto_atTop_of_leadingCoeff_nonneg M.ρPoly hdeg hlc`.
     `hdeg : 0 < ρ.degree` from `degree_eq_natDegree` + Helper 2 + `hk`
     (with the side proof `ρ ≠ 0` from Helper 1). `hlc : 0 ≤ leadingCoeff`
     trivially from Helper 3's `= 1`. ~15 LOC.

3. **Main theorem `LinearMultistepMethod.ρPoly_pos_on_Ioi_one`**:
   by contradiction — if `ρ(z) ≤ 0` for `z > 1`, then either `ρ(z) = 0`
   (a real root > 1, ruled out by cycle 175's `ρPoly_no_real_root_gt_one`)
   or `ρ(z) < 0`. In the latter case Helper 4 gives `w' = max w z + 1` with
   `ρ(w') ≥ 1`; `intermediate_value_Icc` (with
   `Polynomial.continuous.continuousOn` on `Icc z w'`) yields `ζ ∈ [z, w']`
   with `ρ(ζ) = 0` and `ζ ≥ z > 1`, again contradicting cycle 175.
   `_hPre` is propagated but unused (matches downstream signatures). ~35 LOC.

4. **BDF2 sanity witness `bdf2LMM_ρPoly_pos_at_two`** (Section441
   namespace): `0 < bdf2LMM.ρPoly.eval 2` by `unfold + simp + norm_num`
   (yields `5/3`). Numerical sanity; doesn't route through
   `ρPoly_pos_on_Ioi_one` to avoid pulling in `bdf2LMM.IsStable`. ~5 LOC.

## Result

**SUCCESS.** All four helpers + main + sanity witness compile clean.

* `lake env lean OpenMath/Chapter4/Section441.lean` → exit 0, no warnings.
* Sorry count: 0 → 0 (still none in Section441.lean).
* Tautology scanner: clean (`grep -E ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$'`
  returns no matches).
* Axiom check: both `ρPoly_pos_on_Ioi_one` and `bdf2LMM_ρPoly_pos_at_two`
  depend only on `[propext, Classical.choice, Quot.sound]`. Axiom-clean.

Net Section441.lean LOC: 695 → 838 (+143). Within the ~150 LOC budget.

## Faithfulness check

* **`LinearMultistepMethod.ρPoly_coeff_top_eq_one` (private helper)**
  - Textbook content: leading-monomial structure
    `ρ(z) = z^k − …` from the definition on Butcher §441 p. 375.
  - Lean statement captures: identical (`M.ρPoly.coeff k = 1`).
  - No definition smuggling.

* **`LinearMultistepMethod.ρPoly_natDegree_eq_k` (private helper)**
  - Textbook content: `ρ` has degree exactly `k`.
  - Lean statement captures: identical.

* **`LinearMultistepMethod.ρPoly_leadingCoeff_eq_one` (private helper)**
  - Textbook content: `ρ` is monic.
  - Lean statement captures: identical.

* **`LinearMultistepMethod.ρPoly_tendsto_atTop` (private helper)**
  - Textbook content: "`limz→∞ ρ(z) = ∞`" (Butcher §441 p. 376,
    quoted: `\lim_{z\to\infty} \rho(z) = \infty`).
  - Lean statement captures: identical (`Tendsto (·.eval) atTop atTop`
    on `ℝ`).

* **`LinearMultistepMethod.ρPoly_pos_on_Ioi_one` (public)**
  - Entity ID: `lem:441A` (Phase B.3 Step 1, implicit step in Butcher's
    `\rho(1) = 0 ∧ \lim ρ = +∞ ⇒ ρ'(1) > 0` argument).
  - Textbook content: not a stand-alone textbook statement; this is
    the load-bearing intermediate `ρ > 0` on `(1, ∞)` that Butcher's
    one-paragraph proof uses to deduce `ρ'(1) ≥ 0` from the right.
  - Lean statement captures: same content, with `0 < k`,
    `M.IsStable`, and `M.IsPreconsistent` (textbook implicitly assumes
    all three for `lem:441A`).
  - Tautology check: NO. Conclusion `0 < ρ.eval z` is not among
    the hypotheses; derived via IVT + cycle 175.
  - Identity check: NO. Multi-step proof with case split + IVT.
  - Hypothesis-strength check: `_hPre` is unused in this proof but
    propagated for downstream-signature alignment (cycle 178 Phase
    B.3 Step 2 + cycle 179 Phase B.4 will both require it). Underscore
    prefix silences unused-binder warnings. `0 < k` is genuinely
    required (Helper 4's `0 < ρ.degree` step needs it; a `k = 0`
    polynomial is constant and `tendsto_atTop` would fail).
    `M.IsStable` is required (drives cycle 175's `ρPoly_no_real_root_gt_one`).

* **`bdf2LMM_ρPoly_pos_at_two` (public sanity witness)**
  - Textbook content: numerical sanity for BDF2 (`k = 2`,
    `α₁ = 4/3, α₂ = -1/3`); not a textbook entity.
  - Lean statement captures: numerical evaluation
    `bdf2LMM.ρPoly.eval 2 = 5/3 > 0`.

## Dead ends

1. **First attempt at Helper 1 used `refine Polynomial.natDegree_sum_le_of_forall_le _ ?_`
   followed by `intro i _`**: failed with `typeclass instance problem is stuck:
   Semiring ?m.77`. The `_` placeholder for the function argument left the
   semiring unresolved at refine-time. **Fix**: passed all three named
   arguments (`s := Finset.univ`, `f := ...`, `n := k - 1`) explicitly,
   then closed with a single closure `(by intro i _; ...)`.

2. **First attempt at Helper 4 used `refine Polynomial.tendsto_atTop_of_leadingCoeff_nonneg ?_ ?_`
   with two anonymous goals**: failed with `typeclass instance problem
   is stuck: OrderTopology ?m.16`. Same metavariable issue — the polynomial
   `P` was not pinned down in the refine call, leaving `𝕜` as a metavariable.
   **Fix**: built `hdeg` and `hlc` as separate `have` statements, then
   passed `M.ρPoly` explicitly: `exact Polynomial.tendsto_atTop_of_leadingCoeff_nonneg
   M.ρPoly hdeg hlc`. (`P` is an explicit `variable` declared at the top
   of `Mathlib/Analysis/Polynomial/Basic.lean`, so this is the canonical
   call form.)

## Discovery

* **`Polynomial.tendsto_atTop_of_leadingCoeff_nonneg` takes its polynomial
  as the first explicit argument**, not implicit. The Mathlib file declares
  `variable {𝕜 : Type*} [...] (P Q : 𝕜[X])` — so `P` is explicit. Calls
  via `refine ... ?_ ?_` leave `𝕜` ambiguous; build the proof object
  with `exact ... M.ρPoly hdeg hlc` for clean unification.
* **`Polynomial.natDegree_sum_le_of_forall_le` has the same explicit-arg
  pattern** under `variable {ι} {S : Type*} [Semiring S]` — passing
  `(s := ...) (f := ...) (n := ...)` named-arg style sidesteps the
  semiring metavariable. The `Polynomial.natDegree_sum_le_of_forall_le`
  is the right tool for proving `(∑ i, fᵢ).natDegree ≤ n` given a uniform
  bound `∀ i, (fᵢ).natDegree ≤ n` — and accepts the `Finset.univ` case via
  the implicit `s`.
* **The IVT step on closed intervals** is `intermediate_value_Icc` (file
  `Mathlib/Topology/Order/IntermediateValue.lean:543`). Its conclusion is
  `Icc (f a) (f b) ⊆ f '' Icc a b`, so the standard usage is
  `obtain ⟨ζ, hζ_mem, hζ_eval⟩ := intermediate_value_Icc hab hcont hzero_mem`
  where `hzero_mem : 0 ∈ Icc (f a) (f b)`.
* **Helper 1's natDegree bound on the subtracted sum is `≤ k − 1`,
  not just `< k`**: this is necessary because `Polynomial.natDegree_sum_le_of_forall_le`
  yields `≤ n` for some fixed `n`, and `< k` requires combining `≤ k − 1`
  with `k − 1 < k` (which needs `0 < k`). The `omega` after the `have hsum_le`
  handles both steps in one shot.

## Suggested next approach

**Cycle 178 (Phase B.3 Step 2 — `ρ'(1) > 0`)**: combine cycle 177's
`ρPoly_pos_on_Ioi_one` with cycle 174's `ρPoly_eval_one_eq_zero_of_preconsistent`
(`ρ(1) = 0`) and `Polynomial.hasDerivAt` (file
`Mathlib/Analysis/Calculus/Deriv/Polynomial.lean:66`) to derive
`ρ'(1) ≥ 0` via the one-sided difference quotient `(ρ(1+h) − ρ(1))/h ≥ 0`
for `h > 0` (numerator non-negative since `ρ(1+h) > 0` for `h > 0` and
`ρ(1) = 0`; denominator positive). Take `h → 0⁺` and use `ge_of_tendsto`
(file `Mathlib/Topology/Order/OrderClosed.lean`) for "limit of
non-negatives is non-negative". Strengthen to `> 0` via cycle 176's
`ρPoly_deriv_eval_one_ne_zero_of_stable_preconsistent`. Watch out for:

* Right-derivative vs two-sided: `Polynomial.hasDerivAt` is two-sided;
  to get a one-sided limit-of-difference-quotient, use
  `HasDerivAt.tendsto_slope` and restrict to `Filter.Ioi 1` /
  `nhdsWithin 1 (Set.Ioi 1)`.
* The `≥ 0 → > 0` upgrade: from `ρ'(1) ≥ 0` and `ρ'(1) ≠ 0`, conclude
  `0 < ρ'(1)` by `lt_of_le_of_ne hge (Ne.symm hne)` or `hge.lt_of_ne hne`.

**Cycle 179 (Phase B.4 — close `lem:441A` `a₁ > 0`)**: one-line
corollary via cycle 174's
`aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent` applied
to cycle 178's strict positivity. Should fit in 5 LOC.

**Cycle 180+ (Phase C — aᵢ ≥ 0 for i ≥ 2)**: switches to the complex-root
decomposition argument (Butcher §441 p. 376 "Write ζ for a possible
zero of a..."). New machinery: complex roots of `aPoly` mapped via
`(1−ζ)/(1+ζ)` to roots of `α`, `Re(·) ≤ 0` constraint from Routh-Hurwitz-style
arguments, factorization into real / conjugate-pair factors with
non-positive real parts. Multi-cycle. Defer until Phase B fully closes.
