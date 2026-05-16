# Cycle 301 Results

## Worked on

`lem:342A` clause (342g) **general case**: `P_n^*` has `n` distinct
real zeros in `(0, 1)` for every `n : ℕ`. Branch A (Aristotle returned
COMPLETE).

## Approach

Per cycle 301 strategy §A: single-poll Aristotle project
`5939f28b-c890-4b7f-be4f-ed0f31f0d0b5` via
`mcp__aristotle__get_status`.

* **Aristotle observation**: `status: COMPLETE`, `percent_complete: 100`,
  `last_updated_at: 2026-05-16T00:37:03Z` (created 2026-05-15T22:11Z;
  total wall-clock ≈ 2h26m from cycle 300's 30% snapshot through
  COMPLETE in cycle 301). Branch A.

Following strategy §D:

1. Downloaded the result archive via `mcp__aristotle__extract_result`
   to `.prover-state/aristotle_results/cycle_301/`. Read
   `ARISTOTLE_SUMMARY.md`: Aristotle proved
   `butcherShiftedLegendre_n_distinct_real_zeros (n : ℕ) : ∃ xs : Finset ℝ, xs.card = n ∧ (∀ x ∈ xs, x ∈ Set.Ioo 0 1) ∧ (∀ x ∈ xs, P_n^*.eval x = 0)`
   via the textbook sign-change / orthogonality contradiction strategy.

2. **Extracted generic helpers to new file**
   `OpenMath/Chapter3/Section342DistinctRootsHelpers.lean` (mirrors
   the cycle 281 `Section342NormSqHelpers.lean` pattern). The three
   generic polynomial-sign lemmas (purely about `Polynomial ℝ`, not
   `butcherShiftedLegendre`-specific) live there:
   - `poly_nonneg_or_nonpos_near_even_mult_root`
   - `poly_constant_sign_of_even_mult_roots`
   - `prod_linear_factors_dvd_of_roots`

3. **Specialised to `butcherShiftedLegendre` in `Section342.lean`**:
   - `butcherShiftedLegendre_ne_zero (n : ℕ)` (immediate from
     `P_n^*(1) = 1 ≠ 0`)
   - `butcherShiftedLegendre_rootsInIoo (n : ℕ) : Finset ℝ` — the
     finite set of real roots in `(0,1)`
   - `butcherShiftedLegendre_rootsInIoo_subset`,
     `_rootsInIoo_are_roots`
   - `butcherShiftedLegendre_rootsInIoo_card_le` — open-interval-
     filtered upper bound, refining cycle 294's
     `butcherShiftedLegendre_card_roots_le`
   - `butcherShiftedLegendre_rootsInIoo_card_ge` — the load-bearing
     lower bound, ~250 LOC of sign-change contradiction
   - **`butcherShiftedLegendre_n_distinct_real_zeros`** — the headline
     `∃ xs, ...` via `le_antisymm (_card_le _) (_card_ge _)`.

4. **Two surgical corrections** to make Aristotle's proof compile
   under the CLAUDE.md `maxHeartbeats := 200000` default (Aristotle
   used `set_option maxHeartbeats 800000` defensively):

   a. **`IsBezout` synth failure** at
      `Irreducible.coprime_iff_not_dvd` (needed for the
      `IsCoprime (X - C r) (X - C s)` step in
      `prod_linear_factors_dvd_of_roots` and inside
      `poly_constant_sign_of_even_mult_roots`'s factor-extraction).
      Replaced with the direct
      `Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (sub_ne_zero_of_ne hrs).isUnit`
      (from `Mathlib.Algebra.Polynomial.RingDivision`), which avoids
      the `IsBezout` instance entirely.

   b. **`simp +zetaDelta at *` heartbeat blow-up** at the
      `0 < volume (Set.Ioo (max 0 (x-ε)) (min 1 (x+ε)))` step (twice
      — once in the `+` branch, once in the `−` branch of
      `rootsInIoo_card_ge`). Replaced with explicit case-splits via
      `rcases le_or_gt (x - ε) 0` / `rcases le_or_gt 1 (x + ε)`
      then `rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.mpr _`.

5. Verified compilation: `lake env lean OpenMath/Chapter3/Section342.lean`
   exit 0, `lake build OpenMath.Chapter3.Section342` exit 0,
   `lake env lean OpenMath/Chapter3.lean` (aggregator) exit 0.

6. Verified axiom-cleanness directly via `#print axioms`:
   - `butcherShiftedLegendre_n_distinct_real_zeros` → `[propext, Classical.choice, Quot.sound]`
   - `butcherShiftedLegendre_rootsInIoo_card_ge` → `[propext, Classical.choice, Quot.sound]`
   - `butcherShiftedLegendre_rootsInIoo_card_le` → `[propext, Classical.choice, Quot.sound]`
   (The MCP `lean_verify` tool initially reported `sorryAx` on the
   former two; a fresh `lake build` + direct `lake env lean ... #print
   axioms` confirmed the report was stale. No sorry exists anywhere
   in the new code — `grep -nE "sorry|sorryAx" Section342.lean
   Section342DistinctRootsHelpers.lean` empty.)

7. Updated `extraction/formalization_data/lean_status.json`:
   `lem:342A` `partial` → `formalized`,
   `lean_symbol: "OpenMath.Chapter3.Section342.butcherShiftedLegendre_n_distinct_real_zeros"`,
   appended cycle 300 + cycle 301 entries to `cycle_trace`.

8. Updated `plan.md`: `[~] lem:342A` → `[x] lem:342A`, appended
   cycle 301 closure paragraph.

9. Added `OpenMath.Chapter3.Section342DistinctRootsHelpers` to the
   `OpenMath/Chapter3.lean` aggregator.

10. Closed `.prover-state/issues/lem_342A_g_zeros_scoping.md` by
    appending a "Cycle 301 closure" section.

## Result

**SUCCESS.** `lem:342A` is now `formalized` in `lean_status.json` and
`[x]` in `plan.md`. All seven clauses (342a)–(342g) of Butcher's
shifted Legendre characterisation are closed over cycles 271–301,
axiom-clean.

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `butcherShiftedLegendre_rootsInIoo`

- Entity ID and textbook statement (quoted from
  `extraction/formalization_data/entities/lem_342A.json` clause 342g):
  > `P_n^*` has `n` distinct real zeros in the interval `(0, 1)`,
  > `n = 0, 1, 2, …`.
- Lean statement captures: this is a `def`, the auxiliary `Finset ℝ`
  of P_n^*'s roots in `(0,1)`. Not a theorem; no faithfulness concern.

### `butcherShiftedLegendre_ne_zero (n : ℕ) : butcherShiftedLegendre n ≠ 0`

- Helper lemma, not a textbook entity. Stated as the minimum needed
  for `Polynomial.mem_roots` to apply. No textbook divergence.

### `butcherShiftedLegendre_rootsInIoo_subset (n : ℕ) : ∀ x ∈ butcherShiftedLegendre_rootsInIoo n, x ∈ Set.Ioo 0 1`

- Helper lemma extracting half of the open-interval-filter property
  by construction. No textbook divergence.

### `butcherShiftedLegendre_rootsInIoo_are_roots`

- Helper lemma extracting the root property. No textbook divergence.

### `butcherShiftedLegendre_rootsInIoo_card_le (n : ℕ) : (butcherShiftedLegendre_rootsInIoo n).card ≤ n`

- Upper-bound half of (342g). Same content as cycle 294's
  `butcherShiftedLegendre_card_roots_le` but refined to the open-
  interval filter. Lean statement captures: same content (`≤ n` is
  the textbook's exact-equality combined with the lower-bound half).

### `butcherShiftedLegendre_rootsInIoo_card_ge (n : ℕ) : n ≤ (butcherShiftedLegendre_rootsInIoo n).card`

- Lower-bound half of (342g) — the key non-trivial direction.
- Entity ID textbook statement: same (342g) above.
- Lean statement captures: same content as the textbook clause
  combined with the upper-bound `_card_le`. Proof is by the textbook
  sign-change contradiction argument cited in Butcher §342, p. 236.

### `butcherShiftedLegendre_n_distinct_real_zeros (n : ℕ) : ∃ xs : Finset ℝ, xs.card = n ∧ (∀ x ∈ xs, x ∈ Set.Ioo 0 1) ∧ (∀ x ∈ xs, P_n^*.eval x = 0)`

- **The (342g) headline**.
- Entity ID and textbook statement (clause 342g, verbatim from
  `entities/lem_342A.json`):
  > `P_n^*` has `n` distinct real zeros in the interval `(0, 1)`,
  > `n = 0, 1, 2, …`.
- Lean statement captures: **same content**. The existential witness
  `xs : Finset ℝ` realises "n distinct real zeros" (Finset elements
  are distinct, `card = n`), the second conjunct realises "in `(0, 1)`"
  (`x ∈ Set.Ioo 0 1`), the third conjunct realises "zeros of `P_n^*`"
  (`(butcherShiftedLegendre n).eval x = 0`). Textbook quantifies over
  all `n = 0, 1, 2, …`; the Lean theorem is unconditional in `n : ℕ`
  with the `n = 0` case trivially witnessed by `∅ : Finset ℝ`.
- Hypothesis-strength check: only `n : ℕ`, matching the textbook's
  unconditional statement. No extra hypotheses.
- Tautology check: conclusion contains existentials over `xs`, the
  three conjuncts characterise it; nothing matches any hypothesis
  verbatim. Not a tautology.
- Identity check: proof is `⟨butcherShiftedLegendre_rootsInIoo n,
  le_antisymm (...) (...), ..., ...⟩` — the witness is the constructed
  `Finset`, not a re-export.

### Generic helpers in `Section342DistinctRootsHelpers.lean`

These are not textbook entities — they are reusable polynomial
machinery. Faithfulness applies trivially.

- `poly_nonneg_or_nonpos_near_even_mult_root` — at an even-multiplicity
  root, locally constant sign. Pure analysis fact.
- `poly_constant_sign_of_even_mult_roots` — even-multiplicity roots
  + nonzero endpoints ⇒ constant sign on `[0, 1]`. Standard real-
  analysis lemma.
- `prod_linear_factors_dvd_of_roots` — `∏ (X − C r) ∣ p` when each
  `r` is a root. Standard polynomial fact.

## Dead ends

* **Initial helpers compile failed** with
  `IsBezout ?m.303[X]` synthesis errors at the
  `EuclideanDomain.mul_div_cancel'` and `Finset.prod_dvd_of_coprime`
  call sites in `poly_constant_sign_of_even_mult_roots` and
  `prod_linear_factors_dvd_of_roots`. Aristotle's path used
  `Irreducible.coprime_iff_not_dvd` (from
  `Mathlib.RingTheory.PrincipalIdealDomain`), which has an
  `[IsBezout R]` instance argument. The elaborator could not pin the
  metavariable `R` to `Polynomial ℝ` from the bare `_` placeholder
  inside Aristotle's pipe chain
  `Polynomial.irreducible_X_sub_C _ |> fun h => h.coprime_iff_not_dvd...`.
  Fix: switched to `Polynomial.isCoprime_X_sub_C_of_isUnit_sub` (in
  `Mathlib.Algebra.Polynomial.RingDivision`) which has signature
  `IsUnit (a - b) → IsCoprime (X - C a) (X - C b)` over any
  `CommRing`. No `IsBezout` needed.

* **`simp +zetaDelta at *` timed out** at 200000 heartbeats inside
  `rootsInIoo_card_ge`'s `h_interval_pos_measure` sublemma. Aristotle
  had `set_option maxHeartbeats 800000 in` covering the whole theorem,
  which masked this. Replaced the two affected sites with explicit
  `rcases le_or_gt (x - ε) 0` / `rcases le_or_gt 1 (x + ε)`
  case-splits on the `max` / `min`, then `rw [Real.volume_Ioo]; exact
  ENNReal.ofReal_pos.mpr _`. After that fix, the entire theorem
  compiles at the project default 200000 maxHeartbeats with no bump
  required.

* **`le_or_lt` is not the standard name** for the order dichotomy in
  the current Mathlib — it's `le_or_gt`. Multiple usages had to be
  search-and-replaced after the first compile attempt.

* **`hyR : y < 1` vs goal `y ≤ 1` in the inl branch** — the inl
  branch's `MeasureTheory.measure_mono` target uses `Set.Ioc 0 1`
  membership (after the `intervalIntegral.integral_of_le zero_le_one`
  rewrite), which requires `y ≤ 1` not `y < 1`. Fix: `exact hyR.le`
  instead of `exact hyR`.

## Discovery

* **`Polynomial.isCoprime_X_sub_C_of_isUnit_sub`** (in
  `Mathlib.Algebra.Polynomial.RingDivision`) is the right primitive
  for `IsCoprime (X - C a) (X - C b)` when `a ≠ b`. Avoids the
  `Irreducible.coprime_iff_not_dvd` path's `IsBezout` synth requirement.
  Worth noting for future polynomial-coprimality proofs.

* **Aristotle's `set_option maxHeartbeats 800000` bumps were
  defensive**, not load-bearing. Both `poly_constant_sign_of_even_
  mult_roots` and `rootsInIoo_card_ge` compile at the project default
  200000 heartbeats once the two surgical fixes (Bezout, volume_Ioo)
  land. Always worth attempting Aristotle's proofs at the project
  ceiling before committing to a decomposition or escalation.

* **MCP `lean_verify` can report stale axiom information** even after
  a fresh `lake build`. The ground truth is `#print axioms <name>` run
  via `lake env lean`. For axiom-cleanness audits, prefer the latter.

* **`norm_num at *` auto-splits `a * b ≠ 0` into `a ≠ 0 ∧ b ≠ 0`**.
  After Aristotle's
  `rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff'] at
  h_integral_zero <;> norm_num at *`, the hypothesis
  `h_integrand_nonzero : ∃ x ∈ Set.Ioo 0 1, eval x P * eval x Q ≠ 0`
  gets reshaped to `∃ x, 0 < x ∧ x < 1 ∧ ¬eval x P = 0 ∧ ¬eval x Q = 0`,
  which destructures with 4 (not 3) patterns:
  `obtain ⟨x, hx₁, hx₂, hx₃⟩`. Earlier confusion about why Aristotle's
  destructuring had 4 patterns was resolved by tracing the auto-split.

## Suggested next approach

* **Cycle 302 pivot candidate**: with `lem:342A` fully closed, the
  natural next §342 entity is `lem:342B` (Gaussian quadrature
  exactness degree). It is direct-blocked on (342g)'s existence of
  `n` distinct zeros in `(0,1)` — which is now available as
  `butcherShiftedLegendre_n_distinct_real_zeros`. The textbook proof
  is short (degrees-of-freedom counting on the quadrature error
  polynomial). Recommended.

* **Alternative pivot**: `lem:310B` Phase A.3 (TreeAutomorphism
  strengthening) is a continuation thread from earlier in 2026. Less
  immediately fruitful — `lem:342B` is the natural follow-on now
  that (342g) is settled.

* **Tooling note**: the `MCP lean_verify` tool's stale-cache
  behaviour is worth bug-reporting upstream. For cycle 302+, prefer
  `#print axioms` via `lake env lean` for the pre-commit faithfulness
  audit step.

* **Empirical anchors retention**: per strategy §D.6, the cycle 295–
  300 `_one`, `_three`, `_five`, `_seven`, `_nine`, `_eleven`,
  `_thirteen` `_roots` empirical anchors were retained as defensive
  regression witnesses (they provide explicit closed-form sub-
  interval brackets that the existential headline lacks). No future
  cycle should delete them without replacement.
