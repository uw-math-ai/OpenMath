# Cycle 176 Results

## Worked on

`lem:441A` Phase B.2 — `M.IsStable ∧ M.IsPreconsistent ⇒ M.ρPoly.derivative.eval 1 ≠ 0`
(simple-root-at-1 condition).

Plus: BDF2 sanity witness `bdf2LMM_ρPoly_deriv_eval_one_eq` (`ρ'(1) = 2/3`) on
the canonical `k = 2` example, which numerically confirms the Phase B.2
non-vanishing claim and consolidates with cycle 175's `bdf2LMM_aPoly_coeff_one_eq`
(`a₁ = 4/3 = 2 · 2/3`) — the cycle 174 bridge `a₁ = 2·ρ'(1)` made fully concrete.

## Approach

Followed the cycle 176 strategy verbatim — no fallback path needed:

1. **Aux helper** — Added a private auxiliary lemma
   `idSeq_isHomogeneousSolution_of_preconsistent_ρPoly_deriv_zero`: under
   preconsistency `Σᵢ αᵢ = 1` plus `ρ'(1) = 0`, the unbounded sequence
   `y_n := (n : ℝ)` solves the (403a) homogeneous recurrence. Proof
   recipe: extract `Σᵢ αᵢ = 1` from preconsistency; rewrite
   `M.ρPoly_deriv_eval_one_unconditional` with `hDeriv` and use
   `Finset.mul_sum` + `Finset.sum_sub_distrib` to derive
   `Σᵢ αᵢ·(i+1) = 0`; expand the (403a) RHS using `Nat.cast_sub` for the
   well-defined `m + k - (i.val + 1)` (since `i.val + 1 ≤ k ≤ m + k`),
   collapse via the two algebraic identities.

2. **Main theorem** —
   `LinearMultistepMethod.ρPoly_deriv_eval_one_ne_zero_of_stable_preconsistent`:
   `∀ M : LinearMultistepMethod k, M.IsStable → M.IsPreconsistent →
   M.ρPoly.derivative.eval 1 ≠ 0`. Proof: contradiction. From
   `hDeriv : ρ'(1) = 0`, build the unbounded homogeneous solution
   `n ↦ (n : ℝ)` (via aux helper), apply `hStable` to extract a
   uniform bound `C`, then `exists_nat_gt C` finds an `n` with
   `n > C` while `|n| = n ≤ C` — contradiction.

3. **BDF2 numerical witness** — `bdf2LMM_ρPoly_deriv_eval_one_eq`:
   `bdf2LMM.ρPoly.derivative.eval 1 = 2/3`. One-line proof rewriting
   with the cycle 174 unconditional closed form, then
   `simp [bdf2LMM, Fin.sum_univ_two]; norm_num`. Witnesses cycle 176's
   main theorem numerically on the canonical `k = 2` example.

## Result

**SUCCESS** — all three items closed on first attempt; no fallbacks
needed. `lake env lean OpenMath/Chapter4/Section441.lean` exits cleanly
with no diagnostics. Sorry count remains 0.

## Faithfulness check

For each new theorem introduced this cycle:

* **Aux helper** `idSeq_isHomogeneousSolution_of_preconsistent_ρPoly_deriv_zero`
  (private):
  - **Entity ID and textbook statement**: helper for `lem:441A`'s
    proof step "ρ has only simple roots" (Butcher §441 p. 376); not
    a textbook entity in its own right.
  - **Lean statement captures**: same content — the standard
    "characteristic-eq derivative-zero → polynomial solution `n`"
    link, parallel to cycle 175's
    `geomSeq_isHomogeneousSolution_of_ρPoly_isRoot`.
  - **Definition smuggling check**: NO. The conclusion
    `M.IsHomogeneousSolution (fun n : ℕ => (n : ℝ))` is a different
    proposition from the hypotheses (`hPre`, `hDeriv`); proof does
    real algebraic work via `Finset.sum_sub_distrib`.

* **Main theorem**
  `LinearMultistepMethod.ρPoly_deriv_eval_one_ne_zero_of_stable_preconsistent`:
  - **Entity ID and textbook statement** (`lem:441A`, Butcher §441 p. 376):
    > "[ρ] has no real zeros greater than 1, and hence, because ρ(1) = 0
    > and because limz→∞ ρ(z) = ∞, it is necessary that ρ′(1) > 0."
    >
    > [The simple-root claim is implicit in "z = 1 is a single root
    > at z = 1" earlier in the proof.]
  - **Lean statement captures**: weaker — Phase B.2 of the four-phase
    plan. Cycle 176 proves the *non-vanishing* `ρ'(1) ≠ 0`; the strict
    sign `ρ'(1) > 0` is deferred to cycle 177 (Phase B.3, IVT-style).
    Cycle 178 (Phase B.4) will then close `lem:441A`'s `a₁ > 0` half
    via the cycle 174 bridge `a₁ = 2·ρ'(1)`.
  - **Definition smuggling check**: NO. The conclusion `≠ 0` is a
    proper Prop, not a hypothesis re-export. The proof does real
    work via stability + Archimedean unboundedness.
  - **Hypothesis strength check**: matches the textbook's "stable
    method" + implicit preconsistency (`ρ(1) = 0`) preconditions.
    Both are necessary: without `IsStable` an unstable method admits
    unbounded `n ↦ n`-style solutions and `ρ'(1)` may vanish; without
    `IsPreconsistent` the claim is not even formulated in the textbook
    (preconsistency is what makes `z = 1` a root in the first place).

* **BDF2 numerical witness** `bdf2LMM_ρPoly_deriv_eval_one_eq`:
  - **Entity ID and textbook statement**: numerical sanity, no
    direct textbook entity. Direct corollary of cycle 174's
    `ρPoly_deriv_eval_one_unconditional` evaluated at the BDF2
    coefficients `(α₁, α₂) = (4/3, -1/3)`.
  - **Lean statement captures**: numerical evaluation —
    `ρ'(1) = 2 - [(4/3)·1 + (-1/3)·0] = 2/3`. Independently
    verifiable; consistent with `a₁ = 4/3 = 2 · 2/3` from cycle 175.

**Tautology check** — no theorem conclusion appears verbatim as one of
its own hypotheses. The aux helper has hypotheses
`hPre : M.IsPreconsistent`, `hDeriv : M.ρPoly.derivative.eval 1 = 0`
and concludes `M.IsHomogeneousSolution (fun n => (n : ℝ))` — distinct.
The main theorem has `hStable, hPre` and concludes `≠ 0` — distinct.

**Identity check** — no `exact h` proofs; all proofs do real work.

## Dead ends

None this cycle. The proof template from cycle 175 transferred directly:
the only delicate step (the Nat-cast splitting `(m + k - (i.val + 1) : ℕ)
→ (m : ℝ) + (k : ℝ) - ((i.val : ℝ) + 1)`) was anticipated in the cycle 176
strategy and the `rw [h1]; push_cast [Nat.cast_sub hile]; ring` recipe
worked first try. No fallbacks (per-summand cast helper, m=0 branch,
or induction on m) needed.

## Discovery

* **Cycle 175's proof template ports cleanly to the polynomial-derivative
  setting.** The argument structure
  ```
  contradiction ← unbounded homogeneous solution ← root condition + algebraic identity
  ```
  is robust under swapping the underlying sequence (geometric `z₀^n` vs
  identity `(n : ℝ)`) and the underlying root condition (`ρ(z₀) = 0` vs
  `ρ'(1) = 0` under preconsistency). Phase B.3 (cycle 177's `ρ'(1) > 0`)
  will need a *different* template — the IVT-style argument cannot be
  built from "homogeneous solution → contradiction" — but Phase B.4 (cycle
  178's `a₁ > 0`) is a one-line corollary via the cycle 174 bridge.

* **`exists_nat_gt` is the natural Archimedean entry point for
  unbounded `n ↦ (n : ℝ)`-type contradictions.** Cycle 175 used
  `pow_unbounded_of_one_lt` for the geometric case; cycle 176 needed
  the `ℕ`-Archimedean variant. Both are clean one-step extracts of
  the bound-violator natural number.

* **The `Finset.mul_sum` + `Finset.sum_sub_distrib` + `ring` triad**
  closes any "α-times-(constant-minus-(i+1))" type expansion cleanly,
  and was reused verbatim three times this cycle (in the aux helper
  and twice in the main rewrite chain). This is the same triad that
  closed cycle 174's
  `ρPoly_deriv_eval_one_eq_neg_alpha_deriv_at_one_of_preconsistent`.

## Suggested next approach

**Cycle 177 (Phase B.3 — `ρ'(1) > 0` via IVT-style sign analysis)**:
strengthen Phase B.2's `≠ 0` to `> 0` using:

1. Cycle 175's `ρPoly_no_real_root_gt_one` (no real root in `(1, ∞)`).
2. Cycle 174's `ρPoly_eval_one_eq_zero_of_preconsistent` (`ρ(1) = 0`).
3. New: continuity of `ρ` (free from `Polynomial.continuous`).
4. New: `ρ → +∞` as `z → +∞` (need `Polynomial.tendsto_atTop_*`
   Mathlib lemma — verify signature via `lean_local_search`).
5. Combine via IVT-style sign analysis: `ρ > 0` on `(1, ∞)` ⇒
   `ρ'(1) ≥ 0` (one-sided derivative argument); strengthen to `> 0`
   via cycle 176's
   `ρPoly_deriv_eval_one_ne_zero_of_stable_preconsistent`.

The leading-coefficient-positive property of `ρ` (the `X^k` term)
needs to be proven separately — `M.ρPoly.coeff k = 1` should be a
near-rfl lemma but worth stating explicitly. May want to verify the
appropriate Mathlib `Polynomial.tendsto_atTop` flavour first via
`lean_loogle` to scope the cycle 177 plan.

**Cycle 178 (Phase B.4 — close `lem:441A` `a₁ > 0` half)**: one-line
corollary via cycle 174's `aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent`
applied to cycle 177's `ρPoly_deriv_eval_one_pos_of_stable_preconsistent`.

**Cycle 179+ (Phase C — `aᵢ ≥ 0` for `i ≥ 2`)**: switches to the
complex-root decomposition argument of `aPoly` (Butcher §441 p. 376
"Write ζ for a possible zero of a..."). Different machinery —
defer until Phase B is fully closed.
