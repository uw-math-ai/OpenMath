# Cycle 052 Results

## Worked on
Added the cycle 052 helper `globalError_eq_linRec` (the algebraic
identity expressing the LMM global error sequence as a
`Section141.linRec`) plus the stretch-goal helper
`globalError_closed_form` (one-liner composition with
`linRec_closed_form`). Both are private helpers inserted between
`globalError_per_step_sum_form` (cycle 051) and the
`stable_consistent_isConvergent` scaffold (cycle 047).

The line-2014/2106 `sorry` (`stable_consistent_isConvergent`) is
untouched — the cycle 053+ outer-assembly target.

## Approach
1. Verified prior commit landed and sorry count was 1
   (`git log --oneline -5`, `grep -n sorry`). Phantom-failure check
   passed — no recovery work needed.
2. Read `Section141` API for `linRec`, `linRec_of_lt`, `linRec_of_ge`
   to confirm signatures and convention (`α j = α_{j+1}`).
3. Submitted ONE Aristotle job in the background with the abstracted
   identity (see `aristotle_jobs/cycle_052_global_error_eq_linRec.txt`
   for the prompt; project_id `7baff4e3-ffad-4dd0-8b1d-8e97e6bb6892`).
4. While Aristotle ran, wrote the manual proof per the planner's
   Step 0 → 1 → 2 outline:
   - Strong induction `Nat.strong_induction_on`.
   - Case `n < k`: `linRec_of_lt` β-reduces to the initial value;
     `rfl` discharges immediately (no fallback needed).
   - Case `n ≥ k`: `linRec_of_ge` unfolds the recurrence; for each
     `j : Fin k`, `n - 1 - j.val < n` (omega from `j.isLt : j.val < k`
     and `k ≤ n`); IH supplies the rewriting equality for each
     `linRec(n - 1 - j.val)`; `simp_rw [h_eq]` followed by `ring`
     closes (the `Σ α · ε` summand on each side cancels).
5. Stretch goal `globalError_closed_form`: one-liner
   `rw [globalError_eq_linRec M n]; exact linRec_closed_form k _ _ _ n`.

## Result
SUCCESS — both lemmas compile cleanly on the first attempt with no
new errors, no new warnings, and clean axioms (`propext`,
`Classical.choice`, `Quot.sound` only — no `sorryAx`, no new axioms).

Verification:
- `lake env lean OpenMath/Chapter4/Section404.lean` → only the four
  pre-existing warnings (unused `hM`/`hh`/`hMmax0` plus the
  documented sorry at the renumbered line 2106).
- `lean_verify globalError_eq_linRec` → standard axioms only.
- `lean_verify globalError_closed_form` → standard axioms only.
- `grep -n sorry OpenMath/Chapter4/Section404.lean` → still one
  actual `sorry` (line 2106, the cycle 047 scaffold).
- Aristotle job is still running but is not needed (manual proof
  landed faster). CLAUDE.md cap of one status check is preserved
  by NOT polling.

## Faithfulness check
Two new declarations, both internal helpers (no Butcher entity
correspondence — they are infrastructure for the `thm:406D` outer
assembly).

### `globalError_eq_linRec`
- Entity ID: N/A (internal helper). Same category as
  `recentSum_swap_bound` (cycle 050),
  `globalError_per_step_sum_form` (cycle 051),
  `sum_theta_psi_contraction` (cycle 048).
- Lean statement captures: pure algebraic identity with the
  natural-shape (`α := M.α j.succ`, `y₀init := ε(j.val)`,
  `ψ := residual`) — no analytic hypotheses, just the equality.
- TAUTOLOGY check: PASS — LHS is `yex(...) - Y(...)`; RHS is the
  recursive `Section141.linRec`. They are not syntactically
  identical.
- IDENTITY check: PASS — proof body is strong induction +
  `linRec_of_lt`/`linRec_of_ge` + `ring`. The `ring` step performs
  real algebraic cancellation (`Σ α · ε` against itself in the `ψ`
  unfolding); not a vacuous re-export.
- HYPOTHESIS STRENGTH check: PASS — the lemma takes only the most
  general data (`M`, `yex`, `Y`, `x₀`, `h`, `n`); no Lipschitz, ODE,
  consistency, or stability hypotheses. None can be weakened.
- DEFINITION SMUGGLING check: N/A (no new `def`/`structure`).
- ABSENT THEOREM check: docstring forward-references cycle 053+'s
  consumer (the outer assembly), not a non-existent theorem.

### `globalError_closed_form` (stretch goal)
- Entity ID: N/A (internal helper). Cycle 053 originally planned to
  do this composition; landing it now means cycle 053 starts from a
  fully-decomposed shape.
- Lean statement captures: explicit `θ`-decomposition of the LMM
  global error, derived from `globalError_eq_linRec` +
  `Section141.linRec_closed_form` (Theorem 141A, cycle 012).
- TAUTOLOGY check: PASS — RHS is the explicit `Σ θ y' + Σ θ ψ`
  decomposition; LHS is the global error.
- IDENTITY check: PASS — proof body is `rw + exact linRec_closed_form`.
  The `linRec_closed_form` step (Theorem 141A, ~80 lines of proof
  in Section141) is the substantive content; this composes it with
  the cycle-052 algebraic identity.
- HYPOTHESIS STRENGTH check: PASS — same as above (only the most
  general data).
- DEFINITION SMUGGLING check: N/A.
- ABSENT THEOREM check: PASS — both `globalError_eq_linRec` (this
  cycle) and `linRec_closed_form` (cycle 012) exist and compile.

## Dead ends
None — the proof landed on the first attempt. The Step 0 fallback
suggested by the planner (β-reduction issues with `rfl`) was not
needed; `rfl` worked immediately because `(⟨n, hn⟩ : Fin k).val = n`
is definitional.

The planner's suggested case-split on `k = 0` vs `k ≥ 1` was also
unnecessary: when `k = 0`, the `intro j` introduces an impossible
`j : Fin 0` and `omega` discharges the `n - 1 - j.val < n` claim
vacuously (omega handles `j.val < 0` as `False`).

## Discovery
1. `Nat.strong_induction_on` with `induction n using ... with | _ n ih`
   syntax handles the `Fin k` indexing of recursive calls cleanly —
   no need for an auxiliary index function.
2. `simp_rw [h_eq]` on a `∀ j : Fin k, linRec _ _ _ _ (n - 1 - j.val) = ...`
   rewriting equation rewrites all the nested `linRec` calls inside
   `∑ j : Fin k, α j * linRec _ _ _ _ (n - 1 - j.val)` in one shot,
   thanks to congruence under `Finset.sum`. This is the right
   pattern for "rewrite each summand by an IH".
3. `ring` after `simp_rw [h_eq]` reliably closes
   `Σ α · ε + (ε - Σ α · ε) = ε` when both sides are in normal form.
   No `linarith` or explicit `calc` was needed.
4. Composing `globalError_eq_linRec` with `linRec_closed_form`
   really is a one-liner — the `_`-holes in the `linRec_closed_form`
   call unify cleanly because the surrounding `rw` already pinned
   down the lambdas.

## Suggested next approach
Cycle 053 outer-assembly is now significantly shorter: with both
`globalError_eq_linRec` and `globalError_closed_form` landed, cycle
053 can start directly from the `Σ θ y' + Σ θ ψ` decomposition.
Recommended cycle 053 plan:

1. Apply `globalError_closed_form` to convert the goal `|ε(n)| → 0`
   into `|Σ θ y' + Σ θ ψ| → 0`.
2. Triangle inequality: bound by `|Σ θ y'| + |Σ θ ψ|`.
3. **First sum (initial-data part)**: `theta_bounded_of_isStable`
   gives `|θ| ≤ Θ`; `yPrime` is determined by the first `k` errors,
   each of which `→ 0` by hypothesis (`IsConvergent` requires the
   starter satisfies this). Use `starting_error_sum_tendsto_zero`
   (cycle 049) once the connection is made explicit.
4. **Second sum (forcing part)**: `sum_theta_psi_contraction`
   (cycle 048) with `ψ_i := globalError_per_step_sum_form`'s
   residual gives `|Σ θ ψ_i| ≤ Θ · (C h Σ Sε + D h² · #range)`.
   Then `recentSum_swap_bound` (cycle 050) collapses the
   nested-window sum, and `discrete_gronwall_exp_bound` (cycle 046)
   gives the final exponential bound.
5. `Filter.Tendsto` algebra (`Tendsto.add`, `squeeze_zero`,
   `Real.exp_continuous`) closes everything.

Expected cycle 053 deliverable: close the `sorry` at line 2106
(`stable_consistent_isConvergent`) — finishing `thm:406D`. If
unification of the `linRec`-shape into the `IsConvergent`
quantifier-shape proves finicky, decompose into a "main-bound"
helper first.

Bonus: cycle 052's `globalError_closed_form` can be made `theorem`
(rather than `private lemma`) and Aristotle-submitted to verify
the closed-form is indeed equivalent to the textbook (406h). This
is purely defensive and not blocking.

## Aristotle plan
ONE submission, project_id `7baff4e3-ffad-4dd0-8b1d-8e97e6bb6892`
(`globalError_eq_linRec_abstract`). No status check performed
(manual proof landed faster). The job will eventually finish; if
its returned proof is shorter than the manual ~25-line one, a
future cycle can swap it in.
