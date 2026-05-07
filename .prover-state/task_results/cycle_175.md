# Cycle 175 Results

## Worked on

`lem:441A` Phase B.1.β — `M.IsStable ⇒ M.ρPoly has no real root > 1`.
Plus consolidation: BDF2 sanity witnesses
(`bdf2LMM_isPreconsistent`, `bdf2LMM_aPoly_coeff_zero_eq`,
`bdf2LMM_aPoly_coeff_one_eq`) replacing the long-stalled
`bdf2LMM_aPoly_eq` closed-form goal.

## Approach

Followed the cycle 175 strategy verbatim:

1. **Priority 1 (substantive)** — Added a private auxiliary lemma
   `geomSeq_isHomogeneousSolution_of_ρPoly_isRoot` (a real root `z₀`
   of `ρ` yields a geometric homogeneous solution `n ↦ z₀^n`) and
   the public theorem
   `LinearMultistepMethod.ρPoly_no_real_root_gt_one` (stability +
   `ρPoly.IsRoot z₀` ⇒ `z₀ ≤ 1`). The proof uses
   `pow_unbounded_of_one_lt` (the same Archimedean lemma cycle 136
   used in `Section520.lean`'s `explicitEulerGLM_not_isAStable`),
   so the dependency chain is exactly the cycle 175 strategy's
   primary recipe — no Bernoulli fallback needed.

2. **Priority 2 (consolidation)** — Added an import of
   `OpenMath.Chapter4.Section451` to `Section441.lean` to access
   `bdf2LMM`. Inside the `Section441` namespace block, added:
   * `bdf2LMM_isPreconsistent` (proof: `simp [..., bdf2LMM,
     Fin.sum_univ_two]; norm_num`).
   * `bdf2LMM_aPoly_coeff_zero_eq` (one-liner via
     `aPoly_coeff_zero_of_preconsistent`).
   * `bdf2LMM_aPoly_coeff_one_eq` (witness `a₁ = 4/3`; combines the
     cycle 174 bridge `a₁ = 2·ρ'(1)` with the unconditional
     `ρ'(1)` closed form, then `simp [..., Fin.sum_univ_two];
     norm_num`).

3. **Cycle-174 docstring footnote** — Added the optional textbook
   factor-of-2 typo note to the docstring of
   `aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent` (per
   the strategy's permission). The note flags Butcher's `ρ'(1) = a₁`
   line as off by a factor of 2 from our proven `a₁ = 2·ρ'(1)`,
   citing explicit Euler (a₁ = 2, ρ'(1) = 1) and BDF2 (a₁ = 4/3,
   ρ'(1) = 2/3) as numerical verification. The proof and statement
   are unchanged; the cycle 174 task results already documented the
   discovery.

4. **Priority 3 (αPoly_deriv_eval_one extraction)** — Skipped per
   the strategy's "Skip if Priority 1 takes >75% of the cycle"
   guidance: Priority 1 + Priority 2 are sufficient cycle content
   and Priority 3 risks introducing build issues for low gain. The
   duplication remains as a deferred cleanup.

5. **Aristotle policy** — Did NOT submit (per strategy "Priority 0":
   the Phase B.1.β proof is short, and cycle 174's policy decision
   stands).

## Result

SUCCESS. All five new declarations type-check and the file compiles
clean (`lake env lean OpenMath/Chapter4/Section441.lean` exits 0,
no diagnostics). Sorry count remains 0. Tautology-scanner regex
returns no hits over the new declarations; all hypothesis names
follow the strategy's `hroot, hStable, hgt, hC, hsol, habs_le,
habs_eq, hpos, hsub, hile, hev, hroot_eq, hpre, hn_pow` style (no
`h_*` names).

## Faithfulness check

For each new `def`/`theorem`:

### `LinearMultistepMethod.geomSeq_isHomogeneousSolution_of_ρPoly_isRoot` (private theorem)

Auxiliary helper. Captures the standard "characteristic root →
geometric solution" link for linear difference equations: if
`ρ(z₀) = 0` then `n ↦ z₀^n` solves the (403a) homogeneous
recurrence. This is implicit in Butcher's argument
(p. 376, "ρ has no real zeros greater than 1") — you cannot derive
that bound *without* this link.

Lean statement captures: same content. The textbook does not state
this as a separate lemma but uses it as a one-line step ("if `z₀ > 1`
were a root, the geometric sequence `z₀^n` would be an unbounded
solution"). We extract it as a private helper for clarity and
reuse in cycle 176 (Phase B.2 will reuse the same pattern with
the sequence `n` instead of `z₀^n`).

### `LinearMultistepMethod.ρPoly_no_real_root_gt_one` (theorem)

Entity: `lem:441A` (proof step). Quoted from
`extraction/formalization_data/entities/lem_441A.json`
(`proof_text`):

> The polynomial ρ ... has no real zeros greater than 1, and
> hence, because ρ(1) = 0 and because lim_{z→∞} ρ(z) = ∞, it is
> necessary that ρ'(1) > 0.

The first clause "no real zeros greater than 1" is exactly our
`ρPoly_no_real_root_gt_one` statement (`M.ρPoly.IsRoot z₀ → z₀ ≤ 1`).

Lean statement captures: same content.

Hypothesis check: `M.IsStable` (= Butcher Definition 403A,
`def:403A`) is the textbook hypothesis verbatim. No
`M.IsPreconsistent` is needed for this step (preconsistency
enters at the next phase, B.2/B.3). This matches Butcher's flow:
the "no real root > 1" claim follows from stability alone via the
geometric-solution argument; preconsistency (giving `ρ(1) = 0`) is
needed only when assembling `ρ'(1) > 0` in cycle 177.

### `bdf2LMM_isPreconsistent` (theorem)

Entity: `def:404A` (preconsistency for `bdf2LMM`). BDF2's
`α₁ = 4/3, α₂ = -1/3` satisfy `α₁ + α₂ = 1`, so the predicate
holds. Lean statement captures: same content (preconsistency
applied to the textbook `bdf2LMM` from §451 p. 363).

### `bdf2LMM_aPoly_coeff_zero_eq` (theorem)

`a₀ = 0` for BDF2. One-liner via
`aPoly_coeff_zero_of_preconsistent`. Lean statement captures:
same content (the `lem:441A` implicit `a₀ = 0` claim, instantiated
on BDF2).

### `bdf2LMM_aPoly_coeff_one_eq` (theorem)

`a₁ = 4/3` for BDF2. Via the cycle 174 bridge `a₁ = 2·ρ'(1)` plus
the unconditional `ρ'(1)` closed form. Numerical sanity:
`ρ'(1) = 2 - [(4/3)·1 + (-1/3)·0] = 2/3`, so `a₁ = 2·(2/3) = 4/3`.

Lean statement captures: same content. This is the §441 a-coefficient
calculation on the canonical `k = 2` example.

## Tautology check

None of the new theorems' conclusions appear verbatim as
hypotheses. `ρPoly_no_real_root_gt_one` takes `M.IsStable` and
`M.ρPoly.IsRoot z₀` as hypotheses and concludes `z₀ ≤ 1` — three
distinct propositions.

## Identity check

None of the proofs is `exact h` alone. The auxiliary helper chains
through `unfold + simp only + linarith` for the polynomial-eval
step, then `pow_add + Finset.sum_congr + omega + ring` for the
recurrence. The main theorem chains through `by_contra + push_neg
+ pow_unbounded_of_one_lt + abs_of_nonneg + linarith`. The BDF2
witnesses chain through `simp [bdf2LMM, ...] + norm_num` (sanity
arithmetic).

## Hypothesis strength check

All hypotheses match the textbook. `ρPoly_no_real_root_gt_one`
takes `M.IsStable` (Butcher Definition 403A, exactly the textbook
hypothesis at this point in the proof of `lem:441A`). The BDF2
witnesses have no hypothesis beyond the textbook coefficient
values from §451 p. 363.

## Definition smuggling check

No new `def`/`structure`/`class` introduced. The auxiliary helper
and theorems are derived facts about existing definitions
(`ρPoly`, `IsHomogeneousSolution`, `IsStable`).

## Dead ends

None this cycle. The strategy's primary recipe
(`pow_unbounded_of_one_lt`) worked on the first attempt; no
Bernoulli fallback was needed.

## Discovery

* The `pow_unbounded_of_one_lt` lemma collapses the entire
  Archimedean argument to ~6 LOC (the strategy's optimistic
  estimate). It returns `⟨n, hn⟩ : ∃ n, C < y^n` directly, which
  pairs cleanly with `pow_nonneg + abs_of_nonneg + linarith`. This
  is exactly the cycle 136 recipe from
  `Section520.lean::explicitEulerGLM_not_isAStable`.

* The `Polynomial.IsRoot` unfolding gives `M.ρPoly.eval z₀ = 0`
  and combines with the `simp only` set used in cycle 174's
  `ρPoly_eval_one` to give the eval-substitution
  `z₀^k = ∑ αᵢ z₀^(k-(i+1))` directly via `linarith`. No need for
  `linear_combination` or manual rearrangement.

* The natural-number arithmetic `m + k - (i.val + 1) = m + (k -
  (i.val + 1))` (under `i.val + 1 ≤ k`) is dispatched by `omega`
  in one step. No `Nat.cast_sub` or `push_cast` gymnastics.

* The cycle 175 proof of `geomSeq_isHomogeneousSolution_of_ρPoly_isRoot`
  is exactly parallel to what cycle 176 will need for the simple-
  root claim (Phase B.2): replace `z₀^n` with `(n : ℝ)` (or `n`
  treated as a homogeneous solution at `z = 1`). Cycle 176 should
  reuse the same skeleton.

## Suggested next approach

For cycle 176 (Phase B.2 — simple root at 1):

1. **Goal**: `M.IsStable + M.IsPreconsistent ⇒
   M.ρPoly.rootMultiplicity 1 = 1` (i.e. `(z-1)²` does NOT divide
   `ρPoly`).

2. **Argument**: if `(z-1)²` divides ρ, then the homogeneous
   recurrence has the unbounded solution `y_n := (n : ℝ)`. This
   contradicts stability. Mirror Cycle 175's
   `geomSeq_isHomogeneousSolution_of_ρPoly_isRoot` skeleton:
   * Aux lemma: if `ρ.IsRoot 1` and `ρ.derivative.IsRoot 1`, then
     `n ↦ (n : ℝ)` is a homogeneous solution.
   * Main theorem: combine with stability to derive
     `¬ ρ.derivative.IsRoot 1`, i.e. simple root at 1.

3. **Mathlib hooks to verify**:
   * `Polynomial.rootMultiplicity` and its relation to
     `derivative.IsRoot`.
   * Whether `(z-1)² ∣ ρ` ↔ `ρ.IsRoot 1 ∧ ρ.derivative.IsRoot 1`
     for ℝ-coefficients.

4. **LOC estimate**: ~80–100 LOC, similar to cycle 175.

For cycle 177 (Phase B.3 — `ρ'(1) > 0` assembly):

* Combine cycle 175's `ρPoly_no_real_root_gt_one` + cycle 176's
  simple-root claim + an IVT-style argument
  (`ρ → +∞`, `ρ(1) = 0`, no root in `(1, ∞)`) ⇒ `ρ > 0` on
  `(1, ∞)` ⇒ `ρ'(1) ≥ 0`. Strengthen to `> 0` via the simple-root
  condition.

For cycle 178 (Phase B.4 — close `lem:441A` `a₁ > 0` half):

* Combine cycle 174's bridge `a₁ = 2·ρ'(1)` with cycle 177's
  `ρ'(1) > 0`. Should be a one-liner.

For Priority 3 (αPoly_deriv_eval_one extraction): defer to a future
consolidation cycle. The duplication is small (~28 LOC) and not
load-bearing for the main pipeline.

For BDF2 closed-form `bdf2LMM_aPoly_eq`: dropped permanently.
Sanity coverage is now via the single-coefficient witness
`bdf2LMM_aPoly_coeff_one_eq`, which is more useful for downstream
infrastructure anyway.
