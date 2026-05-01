# Cycle 050 Results

## Worked on
Added `recentSum_swap_bound` — the index-arithmetic adapter that
bridges the per-step bound from cycle 045
(`globalError_recurrence_bound_textbook`, uses a single `Mmax`
upper-bounding `|ε(n-(j+1))|` over `j : Fin k`), the per-i sum bound
from cycle 048 (`sum_theta_psi_contraction`, takes `Sε i`), and the
discrete Grönwall recurrence from cycle 046 (`discrete_gronwall_exp_bound`,
wants `Σ_{i ∈ Ico 1 n} u i`). Inserted immediately before
`LinearMultistepMethod.stable_consistent_isConvergent` (now at
line 1947).

The lemma states:
```
(g : ℕ → ℝ) (hg : ∀ i, 0 ≤ g i) (k n : ℕ)
⊢ (∑ i ∈ Finset.Ico k n, ∑ j : Fin k, g (i - (j.val + 1)))
    ≤ (k : ℝ) * ∑ p ∈ Finset.Ico 0 n, g p
```

Pure index-juggling infrastructure (no new Butcher entity); not in
the textbook. Comparable in role to cycle 048's `sum_theta_psi_contraction`.

## Approach
Per the strategy:
1. Submitted ONE Aristotle job at the start of the cycle (single
   lemma; the strategy explicitly said not to split).
2. While Aristotle ran, sketched the manual proof and tested it via
   `lean_run_code`.

The manual proof took the following route:
* `obtain rfl | hkpos := Nat.eq_zero_or_pos k` — handle `k = 0`
  trivially (empty `Fin 0` makes the inner sum 0).
* `Finset.sum_comm` to swap the outer `∑ i` with the inner `∑ j`.
* Rewrite the RHS `(k : ℝ) * ∑ p, g p` as `∑ _j : Fin k, ∑ p, g p`
  using `Finset.sum_const`, `Finset.card_univ`, `Fintype.card_fin`,
  `nsmul_eq_mul`.
* `Finset.sum_le_sum` reduces to a per-`j` inequality:
  `∑_{i ∈ Ico k n} g(i - (j+1)) ≤ ∑_{p ∈ Ico 0 n} g p`.
* For each `j : Fin k`, derive `j.val + 1 ≤ k` from `j.isLt`. Show
  the map `i ↦ i - (j.val + 1)` is `Set.InjOn` on `Ico k n` (since
  `k ≥ j.val + 1`, no `Nat`-subtraction truncation, hence injective).
* `Finset.sum_image` to rewrite the LHS as a sum over
  `(Ico k n).image (· - (j.val + 1))`.
* `Finset.sum_le_sum_of_subset_of_nonneg` to enlarge the index set
  to `Ico 0 n` (image membership ⇒ `0 ≤ p ≤ n - 1` by `omega`).

## Result
SUCCESS.

* `recentSum_swap_bound` compiles cleanly (verified via
  `lean_diagnostic_messages`: no errors, no new warnings).
* Sorry count remains at 1 (line 1947's
  `stable_consistent_isConvergent` scaffold is unchanged this cycle,
  per the strategy's explicit "do not attempt to close" directive).
* Axiom check via `lean_verify`:
  `OpenMath.Chapter4.Section404.recentSum_swap_bound` uses only
  `[propext, Classical.choice, Quot.sound]` — clean.
* Total file warnings: only the four pre-existing ones (568, 627,
  1204 unused-variable + 1947 sorry).

Aristotle independently produced a working proof (status
`COMPLETE_WITH_ERRORS` was misleading; the summary said "builds
cleanly with no `sorry` and no non-standard axioms"). Aristotle's
proof took a different but equivalent route: it shifted the LHS to
an `image` of `Ico 0 (n - (j+1))` shifted by `+ (j+1)`, then bounded
via subset. Since the manual proof was already in place and is
slightly cleaner (uses the more direct `i ↦ i - (j+1)` reindexing),
we kept the manual proof and archived Aristotle's at
`.prover-state/aristotle_results/cycle_050/recentSum_swap_bound_aristotle/`.

## Faithfulness check
For `recentSum_swap_bound` (the only new declaration this cycle):

- Entity ID and textbook statement: **N/A** — not a Butcher entity.
  This is internal index-juggling infrastructure for the upcoming
  outer assembly of `thm:406D`. Documented in the docstring exactly
  as `sum_theta_psi_contraction` (cycle 048) was, citing the
  cycles 045/046/048 consumers.
- Tautology check: PASS — the conclusion is a non-trivial sum
  inequality involving a swap of summation, not one of the
  hypotheses.
- Identity check: PASS — the proof is real combinatorial work
  (case-split on `k = 0`, summation swap, per-`j` reindexing,
  subset enlargement).
- Class/structure check: N/A — no new class/structure.
- Definition smuggling check: N/A — no new `def`.
- Hypothesis strength check: PASS — `hg` (nonnegativity) is the
  minimal hypothesis needed for `sum_le_sum_of_subset_of_nonneg`;
  no extra hypotheses.

## Dead ends
* Initial attempt used `Finset.sum_le_sum_nbij'` (from the
  strategy's "Approach A"). That name does NOT exist in Mathlib —
  the actual lemma is `Finset.sum_nbij'` (an equality, not an
  inequality). Falling through to "Approach B" (`Finset.sum_image` +
  `Finset.sum_le_sum_of_subset_of_nonneg`) worked on the first try.

## Discovery
* `Finset.sum_le_sum_nbij'` does not exist. The closest Mathlib
  lemma is `Finset.sum_nbij'` (an equality between two sums under
  a bijection between two finsets). For the inequality
  variant we needed, the route is:
  1. `← Finset.sum_image hinj` to express the LHS as a sum over
     the image of the reindexing function.
  2. `Finset.sum_le_sum_of_subset_of_nonneg` to bound by the larger
     sum.
  Future planners should drop the "Approach A" path and recommend
  Approach B directly.
* `simp only` (no lemmas) is needed AFTER `intro a ha b hb hab` in
  a `Set.InjOn` proof to reduce `(fun i => i - c) a = (fun i => i - c) b`
  to `a - c = b - c`, before `omega` can close it. Without the
  beta-reduction step, omega sees an opaque function application
  and fails.
* `j.isLt` for `j : Fin k` directly gives `j.val + 1 ≤ k` — no
  need for `Nat.succ_le_of_lt`.

## Suggested next approach
Cycle 051 should build the **stretch goal** from cycle 050's
strategy: `globalError_per_step_sum_form`. Plan:

1. Take the cycle 045 lemma `globalError_recurrence_bound_textbook`
   and instantiate `Mmax := ∑ j : Fin k, |ε(n-(j+1))|`.
2. The hypothesis `Mmax ≥ |ε(n-(j+1))|` for each `j : Fin k` reduces
   to "max ≤ sum" for nonnegatives — provable via
   `Finset.single_le_sum` after isolating the single `j` term.
3. Conclude:
   `|ψ_n| ≤ Cₕ · (∑_{j:Fin k} |ε(n-(j+1))|) + Dₕ · h²`
   directly suited as the per-step input to cycle 048's
   `sum_theta_psi_contraction` (with
   `Sε(i) := ∑_{j:Fin k} |ε(i-(j+1))|`).

Then cycle 052 can begin the outer assembly of
`stable_consistent_isConvergent` proper, using:
* `IsConvergent` unfolding,
* cycle 045's `globalError_recurrence_bound_textbook` (now via
  cycle 051's per-step sum form),
* cycle 048's `sum_theta_psi_contraction` (with
  `Sε(i) := ∑_{j:Fin k} |ε(i-(j+1))|`),
* cycle 050's `recentSum_swap_bound` to collapse `∑ Sε i` to
  `k · ∑_{p < n} |ε p|`,
* cycle 046's `discrete_gronwall_exp_bound`,
* `theta_bounded_of_isStable`,
* cycle 049's `starting_error_sum_tendsto_zero` for the φ(h) → 0
  limit.

Estimated 3 more cycles (051: per-step sum form; 052: outer
assembly skeleton with intermediate sorry's; 053: close the
final Tendsto algebra) to close `thm:406D` and unblock
`thm:243A`.
