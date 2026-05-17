# Cycle 347 Results

## Worked on

**Phase D′ Step 1 — `coef_β ↔ βPoly.derivative.eval 1` bridge**
(β-side analog of cycle 344's α-side bridge).

Three new declarations + two anonymous `example` non-vacuity
witnesses shipped to `OpenMath/Chapter4/Section422.lean`:

* `coef_β_eq_βPoly_deriv_at_one` — REQUIRED Priority 0 bridge.
* (anonymous `example`) — BDF2 sanity witness (P1).
* (anonymous `example`) — explicit Euler sanity witness (P2).
* `βPoly_deriv_eval_one_nonneg_of_β_nonneg` — Priority 3 stretch
  corollary, combining the bridge with cycle 346's
  `coef_β_nonneg_of_β_nonneg`.

Plus: added `import OpenMath.Chapter4.Section410` at file head.

## Approach

Mirrored cycle 178's `ρPoly_deriv_eval_one_unconditional` proof
recipe at `Section441.lean:375`:

1. `unfold βPoly`.
2. `rw [Polynomial.derivative_sum, Polynomial.eval_finset_sum]`.
3. `Finset.sum_congr rfl` + `intro i _` to land at per-summand
   goal.
4. `rw [Polynomial.derivative_C_mul_X_pow, Polynomial.eval_mul,
   Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
   one_pow, mul_one]`.
5. Close with `ring`.

The strategy note about `i.val - 1` Nat-subtraction underflow at
`i = 0` was a non-issue: `Polynomial.derivative_C_mul_X_pow`
produces `C ↑n * (C a * X^(n-1))` for the `(C a * X^n).derivative`
shape, but when `n = 0` the resulting `(0 : ℝ) * …` collapses
under `ring` on the eval side, and the LHS coefficient
`(↑0 : ℝ) * M.β 0 = 0` matches.

Sanity witnesses:
* BDF2: `rw [← coef_β_eq_βPoly_deriv_at_one]; simp [bdf2LMM,
  Fin.sum_univ_three]`.
* Explicit Euler: `rw [βPoly_explicitEuler]; simp` (uses
  Section410's cycle 73 `βPoly_explicitEuler = X` rewrite,
  no need to go through the bridge).

## Result

**SUCCESS.** All four deliverables ship and compile cleanly:

* `lake env lean OpenMath/Chapter4/Section422.lean` exits 0.
* `lake build OpenMath.Chapter4.Section422` succeeds (247s warm
  rebuild after the §410 import addition).
* `#print axioms` returns `[propext, Classical.choice, Quot.sound]`
  for both named theorems (`coef_β_eq_βPoly_deriv_at_one` and
  `βPoly_deriv_eval_one_nonneg_of_β_nonneg`).
* `grep -c sorry OpenMath/Chapter4/Section422.lean = 0`.
* Tautology-scanner regex `:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$`
  returns 0 hits on Section422.

LOC trajectory: Section422.lean grew 931 → 1004 (+73 LOC,
including docstrings; ≈25 LOC of pure tactic body).

## Faithfulness check

### `coef_β_eq_βPoly_deriv_at_one`

* **Helper lemma, not a textbook entity.** Bridges cycle 340's
  internal `coef_β(M) = Σ_{i:Fin (k+1)} i · M.β i` notation
  (used in `Eq422a` from §422 cycle 340) to Section410 cycle
  73's `βPoly`. No `<entity>.json` to reference; this is a
  meta-bridge identity introduced as scaffolding for the
  multi-cycle `def:422B` Phase D′ derivation.
* **Tautology check**: PASS. Conclusion
  `(∑ i · M.β i) = βPoly.derivative.eval 1` is a substantive
  arithmetic identity, not a re-export of a hypothesis (there
  are no hypotheses other than the LMM data).
* **Identity check**: PASS. Proof is a 7-line tactic chain
  (`unfold`, three `rw`s, `apply Finset.sum_congr rfl`,
  `intro i _`, another `rw`, another `rw`, `ring`), not
  `:= h_*` or `:= id`.
* **Hypothesis strength check**: PASS. No preconsistency
  hypothesis needed (this is the headline simplification over
  the α-side cycle 344 bridge). The textbook β-polynomial is
  `Σ β_i · X^i`, so its derivative at 1 expands directly to
  `Σ i · β_i` without invoking `Σ α_i = 1`.

### `βPoly_deriv_eval_one_nonneg_of_β_nonneg`

* **Stretch corollary, no textbook entity.** Restates cycle
  346's `coef_β_nonneg_of_β_nonneg` in the polynomial language
  via cycle 347's bridge.
* **Tautology check**: PASS. Conclusion
  `0 ≤ βPoly.derivative.eval 1` differs syntactically and
  semantically from the hypothesis
  `∀ i, 0 ≤ M.β i`.
* **Identity check**: PASS. Proof composes the new bridge
  (cycle 347) with cycle 346's coefficient-form helper —
  real mathematical work passing through both lemmas, not
  `:= h_*`.
* **Hypothesis strength check**: PASS. The non-negativity
  hypothesis on `M.β` is exactly what cycle 346's
  `coef_β_nonneg_of_β_nonneg` consumes, and is strictly weaker
  than the eventual Phase D′ Step 2 goal of deriving this from
  `IsStable + IsConsistent` alone.

### Two anonymous `example` non-vacuity witnesses

* BDF2 witness: `βPoly.derivative.eval 1 = 0` for `bdf2LMM`.
  Numerical check: `β = (2/3, 0, 0)`, `coef_β = 0·(2/3) + 1·0 +
  2·0 = 0`. Matches `βPoly'(1) = 0`. ✓
* Explicit Euler witness: `βPoly.derivative.eval 1 = 1` for
  `explicitEulerLMM`. Numerical check: `β = (0, 1)`,
  `coef_β = 0·0 + 1·1 = 1`. Matches `βPoly = X` ⇒
  `βPoly' = 1` ⇒ eval at 1 = `1`. ✓

## Dead ends

None. The cycle 178 α-side template applied cleanly with the
expected simplifications (no `Nat.cast_sub` needed; no
canonicalization step needed on the LHS shape). The plan's pre-
flight risks (signature drift, `i.val - 1` underflow,
`push_cast` complications, warm rebuild time) all came in low,
as expected.

## Discovery

* **β-side derivative is genuinely easier than α-side.** The
  strategy doc's prediction held: cycle 344's α-side proof at
  Section422.lean:703 needed `Nat.cast_sub` + a custom
  `Finset.sum_congr` canonicalization step + a distributive
  rewrite of `α · (k - (i+1))` before closing with `ring`. The
  β-side closes directly with `ring` after the per-summand
  `derivative_C_mul_X_pow` chain — no canonicalization needed,
  no preconsistency hypothesis needed. The whole bridge is
  ≈7 tactic lines vs cycle 344's ≈18.
* **`Polynomial.derivative_C_mul_X_pow` is stable on the β-side.**
  Even at `i = 0` (where the LHS contribution `(↑0 : ℝ) * M.β 0`
  vanishes), Mathlib's `derivative_C_mul_X_pow` produces an RHS
  that `ring` can close after the eval chain. No special-cased
  match needed.
* **`βPoly_explicitEuler` (cycle 73) was already what cycle 347
  Priority 2 needed.** The explicit Euler witness composes
  cleanly via `rw [βPoly_explicitEuler]; simp` — no need to go
  through the new `coef_β_eq_βPoly_deriv_at_one` bridge. This
  is a useful independent double-check that the bridge's
  prediction matches a directly-computed evaluation.

## Suggested next approach

The strategy doc enumerates four candidates for cycle 348+:

**A — Phase D′ Step 2 scoping** (multi-cycle, MEDIUM-HIGH):
write a scoping doc (analog of `lem_441A_phase_C_scoping.md`)
for deriving `0 ≤ βPoly.derivative.eval 1` from
`IsStable + IsConsistent` alone — i.e., a non-trivial
strengthening that drops the `hβ : ∀ i, 0 ≤ M.β i` premise
used by `coef_β_nonneg_of_β_nonneg`. The textbook β-side
characterization for stable consistent LMMs is not as standard
as the α-side `ρ'(1) > 0` story (which had a clean
"no-real-root > 1" + "simple root at 1" + monotonicity
argument). Unless Butcher §403 / §441 provides a clean
characterization, this may require a different routing — e.g.,
via consistency (`C 1 = 0` ⇔ `Σ β_i = coef_α / coef_α' ⋅ k`
or similar) rather than via Schur/Routh root location. Worth
2–3 cycles of investigation before scaffolding.

**B — Phase D.3 inductive solver scoping** (multi-cycle, HIGH):
per `def_422B_path.md` §6.2, with D.2 well-founded recursion
shipped (cycle 343), draft a 3–5 cycle plan for the recursive
construction of `η : RootedTree → ℝ` from the (422a) linear
isolations at each tree. HIGH-risk because the constructor
arithmetic involves products over children indexed by
`RootedTree`'s nested-list-of-children structure, and the
required Mathlib lemmas on `Multiset.prod` over `Σ`-types of
subtree-indexed values are not all in place. Cycle 200/201
rollback precedent forbids attempting this without a phased
decomposition.

**C — Pivot to a fresh entity** (low-medium): with `def:422B`
having absorbed 12 consecutive cycles (336–347), a planner
might reasonably break the §422 streak. Candidates from
`cycle_336_pivot_options.md` (referenced in cycle 346 results):
`def:451A` (G-stability), `thm:535A` (one-step underlying
method for GLMs), `thm:541A` (DIMSIM types). Trade-off: stops
compounding the §422 investment, but may unblock orthogonal
parts of the textbook.

**D — BDF3 / Adams-Bashforth sanity expansion** (low,
sideline): expand the §404 LMM non-vacuity surface with one
more concrete method's `IsStable / IsConsistent` witnesses.
Useful as a cycle palate-cleanser but doesn't compound toward
`thm:422A` / `thm:422C` closure.

**Recommendation**: cycle 348 starts a **scoping** rather than
an **implementation** cycle. Either A or B is fine; A is
strictly easier per the cycle 178 α-side template precedent, B
is the only path to `def:422B` closure. Letter the planner
decide based on whether `def:422B`'s 12-cycle streak warrants
continued investment.
