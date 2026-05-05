# Cycle 139 Results

## Worked on

* §550 sorry remediation — drive sorry count 1 → 0 by removing the
  general-`n` statement of `doublyCompanionMatrix_det_factorization`
  (cycle-138 scaffold).
* `def:530A` (Butcher §530, p. 411) — opened a fresh Chapter 5 leaf
  with the `GeneralizedRungeKuttaMethod` (530a) tableau, the
  `StartingMethod` dependent-sequence structure, and the
  `IsDegenerate` / `IsNonDegenerate` predicates. Two non-vacuity
  witnesses.

## Approach

Followed Priority 4 of the cycle-139 strategy verbatim. Concretely:

1. **Aristotle poll (Priority 0).** Checked the two cycle-138 jobs:
   * Job A (general-n, `7062c2a2-4a8b-4fae-b694-9355e06427a9`):
     IN_PROGRESS, 4 % complete (last update 19:28 UTC, 18 min after
     submission).
   * Job B (n=2, `70f26d67-b37e-4eda-b946-64c9f4616612`): IN_PROGRESS,
     3 % complete.
   Neither returned a proof in time for cycle 139. Per CLAUDE.md, did
   not re-poll; jobs left running for a future cycle.
2. **Priority-3 viability assessment.** The manual cofactor-expansion
   + induction route (Step 3a, ~150 LOC over a 2-term Hessenberg
   recursion + induction on n with two `Fin (n+1)` index re-mappings)
   would not converge inside the cycle-139 budget. Did not start the
   attempt — strategy explicitly time-boxes Priority 3 at 90 min and
   prefers Priority 4 over a stalled cofactor proof.
3. **Priority 4a — statement removal.** Edited
   `OpenMath/Chapter5/Section550.lean`: deleted the
   `doublyCompanionMatrix_det_factorization` theorem (general-`n`
   sorry, cycle-138 lines 121–128) and rewrote the file's
   docstring header from "Cycle 138 status" to "Cycle 139 status",
   documenting the removal and the deferral path. Kept all
   definitions, the `_one_eq` simp lemma, and the `_n_one` witness
   theorem. Verified clean: `lake env lean OpenMath/Chapter5/Section550.lean`
   exits silently; `lake build OpenMath.Chapter5` ✓ (2787/2787 jobs).
4. **Priority 4c — open §530.** Created
   `OpenMath/Chapter5/Section530.lean`. Decided on the structure
   layout faithfully: a `GeneralizedRungeKuttaMethod s` carries the
   four tableau fields `c, A, b₀, b` (the textbook (530a) tableau) and
   a `StartingMethod r` carries a *dependent* function
   `stages : Fin r → ℕ` together with
   `method : (i : Fin r) → GeneralizedRungeKuttaMethod (stages i)`,
   capturing the textbook's heterogeneous-`s_i` allowance verbatim.
   Two predicates:
   * `IsDegenerate := ∀ i, (S.method i).b₀ = 0`
   * `IsNonDegenerate := ¬ IsDegenerate`
   plus an unfolding lemma
   `isNonDegenerate_iff_exists_b₀_ne_zero`. Two non-vacuity witnesses:
   * `trivialStartingMethod_isNonDegenerate` (r=1, b₀=1)
   * `zeroStartingMethod_isDegenerate` (r=1, b₀=0) — confirms the
     dichotomy is non-trivial.
5. **Priority 4b — tracking updates.**
   * `extraction/formalization_data/lean_status.json`:
     - `def:530A`: status `formalized`, cycle 139, lean_symbol
       `…StartingMethod.IsNonDegenerate`.
     - `thm:550A`: status `partial`, cycle 139, lean_symbol now
       points at `doublyCompanionMatrix_det_factorization_n_one` (the
       only surviving theorem).
   * `plan.md`: `def:530A` flipped `[ ] → [x]`; `thm:550A` row
     amended to record the cycle-139 statement removal.
   * `.prover-state/issues/thm_550A_general_n.md`: prepended a
     "Status update (cycle 139)" stanza documenting the removal and
     the surviving file state, mirroring the
     `aux_515D_iterated_V_bound.md` pattern.
6. **Priority 4d — fresh Aristotle job.** **Skipped.** Job A from
   cycle 138 is still in flight on the same problem; the strategy's
   "ONE job, not five" guidance plus avoiding duplicate spend favours
   leaving Job A running.
7. **Verification.**
   * `lake build OpenMath.Chapter5` — 2787 jobs all green.
   * `lean_verify` on the three new public theorems
     (`trivialStartingMethod_isNonDegenerate`,
     `zeroStartingMethod_isDegenerate`,
     `doublyCompanionMatrix_det_factorization_n_one`) — all return
     `[propext, Classical.choice, Quot.sound]`. Axiom-clean.
   * `Grep '\bsorry\b' OpenMath/` — only docstring/comment matches
     remain; **no live `sorry` tactic anywhere**. Sorry count 0.
   * Tautology-scan check: the three new theorems do not have any
     conclusion appearing verbatim as a hypothesis.

## Result

**SUCCESS — Tier B**

* `def:530A` opened with axiom-clean predicate + two genuine witnesses
  (one positive, one negative).
* §550 general-`n` sorry removed; sorry count 1 → 0.
* `OpenMath.Chapter5.Section530` registered in the chapter aggregator
  `OpenMath/Chapter5.lean`.
* All public theorems introduced this cycle are axiom-clean; full
  chapter build is clean.
* Net deliverable: one new section file, one removed sorry, two new
  axiom-clean theorems, one new structure pair, one new predicate
  pair, no regressions.

## Faithfulness check

### `def:530A` — `StartingMethod.IsDegenerate` / `IsNonDegenerate`

* Entity ID: `def:530A`. Textbook statement (quoted from
  `entities/def_530A.json`):
  > A starting method `S` defined by the generalized Runge–Kutta
  > methods (530a), for `i = 1, 2, …, r`, is 'degenerate' if
  > `b₀^{(i)} = 0`, for `i = 1, 2, …, r`, and 'non-degenerate'
  > otherwise.
* Lean statement captures: **same content**.
  - `IsDegenerate S` is literally `∀ i : Fin r, (S.method i).b₀ = 0`.
  - `IsNonDegenerate S` is `¬ IsDegenerate S`, i.e. exactly "not
    degenerate" — the textbook's "otherwise".
  - The structure `StartingMethod r` is faithful to "A starting
    method `S` defined by the generalized Runge–Kutta methods (530a),
    for `i = 1, 2, …, r`": a length-`r` dependent sequence of
    `GeneralizedRungeKuttaMethod (stages i)`, where the `stages i`
    field allows the textbook's heterogeneous `s_i` per-method stage
    counts. No uniform-stage hypothesis is silently introduced.
  - The `GeneralizedRungeKuttaMethod s` structure has the four
    textbook (530a) fields `c, A, b₀, b` and nothing else. No `Prop`
    fields, no smuggled hypotheses, no derived consequences masked as
    inputs.
* Tautology check: `IsDegenerate` and `IsNonDegenerate` have no
  hypotheses besides the input `S` — no tautology possible.
* Identity check: `trivialStartingMethod_isNonDegenerate` is a real
  computation — it routes through `isNonDegenerate_iff_exists_b₀_ne_zero`,
  exhibits `i = 0`, and discharges `(1 : ℝ) ≠ 0` via `one_ne_zero`.
  Not a re-export. Similarly `zeroStartingMethod_isDegenerate` does a
  `fin_cases i; rfl`, not a re-export.
* Hypothesis-strength check: predicates take only the starting method
  itself as input; no extra hypotheses beyond what the textbook
  requires.
* Definition-smuggling check: `IsDegenerate` is the textbook's
  characterisation verbatim. `IsNonDegenerate` is `¬ IsDegenerate`,
  which is exactly the textbook's "otherwise".

### §550 — no new theorems introduced; statement removal only

The cycle-139 edits to `Section550.lean` do not introduce a new
`def`, `structure`, or `theorem`. They only:

* Update the file docstring (cosmetic).
* Delete the cycle-138 sorry-bearing
  `doublyCompanionMatrix_det_factorization` general-`n` theorem.

Per CLAUDE.md, statement removal does not require a faithfulness
entry, but the removal is documented in three places (Section550
docstring, `lean_status.json` notes, and the `thm_550A_general_n.md`
issue file) so the deferral is auditable.

## Dead ends

* **Did not attempt the manual cofactor-expansion / induction proof
  for general n.** Strategy explicitly time-boxes that path at 60–90
  minutes and recommends Priority 4 over a stalled attempt; with
  Aristotle Job A still running on the same problem, sinking cycle
  budget into a manual recursion that would have to land axiom-clean
  in one cycle was high-risk.
* **Did not re-submit a fresh Aristotle job for general-n.** Job A
  from cycle 138 is still IN_PROGRESS on the identical problem;
  duplicating it would burn compute and clutter the project list.

## Discovery

* The `StartingMethod` structure is genuinely simpler than expected:
  representing the heterogeneous-`s_i` allowance via a dependent pair
  `(stages : Fin r → ℕ, method : (i : Fin r) → ...)` is clean Lean and
  matches the textbook exactly. Future §530B / §530C work can build
  on this without an awkward uniform-stage compromise.
* `IsNonDegenerate := ¬ IsDegenerate` plus an
  `isNonDegenerate_iff_exists_b₀_ne_zero` unfolding lemma is the
  ergonomic split — `not_forall` discharges the equivalence in one
  step, and downstream proofs can pick whichever form is convenient.
* The strategy's Priority-4-first design explicitly trades off
  "remove sorry, pivot to a fresh leaf" vs. "fight the cofactor
  recursion". The former delivered B-tier in roughly 30 minutes of
  work; the latter would likely have stalled. Confirmed strategy
  guidance is calibrated.

## Suggested next approach

1. **Cycle 140 — re-poll Aristotle Job A and Job B.** Both submitted
   2026-05-05 19:10 UTC; by cycle 140 they will have had ample time
   to converge or fail. If Job A returns a clean general-`n` proof,
   reinstate `doublyCompanionMatrix_det_factorization` together with
   the proof body. If Job B returns a clean n=2 proof, add
   `doublyCompanionMatrix_det_factorization_n_two` as a substantive
   stepping-stone witness alongside `_n_one`.
2. **Cycle 140+ — open `def:530B` (order relative to a starting
   method).** It is the natural next leaf in §530 and depends on
   `def:530A` (now formalized). Per
   `entities/def_530B.json` it asks: "M has order p relative to S if
   the results found from SM and ES agree to within O(p+1)." That
   formalisation needs Taylor-expansion infrastructure for the
   composition `SM` and `ES`, which is non-trivial — likely a
   multi-cycle effort.
3. **If Aristotle still hasn't returned a clean general-n proof by
   cycle 142**, commit to the manual cofactor-expansion recursion
   over 2 cycles (helper lemma in cycle N, induction closure in
   cycle N+1) per the Priority-3 sketch in cycle-139 strategy.
4. **Capture starting-method examples from §531+** as more witness
   tableaux. Once `def:530B` lands, "M has order 1 relative to S" for
   `M = explicitEulerGLM` should be provable as a non-vacuity
   stepping-stone for `def:530B`.
