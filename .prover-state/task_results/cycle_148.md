# Cycle 148 Results

## Worked on

Priority 1: `doublyCompanionMatrix_det_factorization_n_six`
(sixth concrete-`n` axiom-clean stepping stone for `thm:550A`,
Butcher Theorem 550A) in `OpenMath/Chapter5/Section550.lean`.

Priority 2: Aristotle general-`n` parallel submission with all six
n=1..6 closed proofs as in-context templates.

Priority 3: `plan.md`, `lean_status.json`, and
`thm_550A_general_n.md` updated for cycle 148.

## Approach

Followed the cycle 148 strategy verbatim — the cycle 147 n=5 template
extended by three mechanical changes:

1. **Matrix bump to 6×6.** Two explicit `!![…]` reductions (`hX` and
   `hmat`) for `doublyCompanionMatrix α β` and `1 - z • X` at n = 6.
   The textbook last-column pattern `row i, col n-1 = -β (n-i-1)`
   gives `-β 4, -β 3, -β 2, -β 3, -β 0` for rows 1..5 (verified
   against the strategy's sanity gate).
2. **Three-layer Laplace expansion** in the closing simp:
   - outer `Matrix.det_succ_row_zero`: 6×6 → six 5×5 minors;
   - `Matrix.det_succ_row_zero (n := 4)`: 5×5 → five 4×4 minors;
   - `Matrix.det_succ_row_zero (n := 3)`: 4×4 → four 3×3 minors;
   - `Matrix.det_fin_three`: closes every 3×3 minor.
   `Fin.sum_univ_six` exists in Mathlib (verified ahead of time via
   `lean_run_code`), so no manual `Fin.sum_univ_succ` unfolding was
   needed. One-shot `simp […]; ring` closed `h_diff` exactly like
   for n=5.
3. **Six convolution coefficients** in `IsBigO.of_bound`. The
   `set a..f` block follows the cycle 147 pattern with the β-indices
   shifted up by one and an extra `- α 5 · β 0` term in `a`. The
   `h_inner` chain uses five `norm_add_le` steps plus five
   `mul_le_of_le_one_left` sub-bounds (`hyb..hyf`).

`lean_verify` confirms the proof is axiom-clean
(`[propext, Classical.choice, Quot.sound]`). `lake env lean
OpenMath/Chapter5/Section550.lean` exits 0.

For Priority 2, packaged the entire current `Section550.lean`
(including the new n=6 proof) plus a strong-induction sketch and a
single sorry'd general-`n` `theorem` in
`.prover-state/aristotle_submissions/cycle_148/general_n.lean`. Submitted
via `mcp__aristotle__submit_file`. Project ID
`2c4630b2-2998-4d4a-af88-c2f83fbd9eda`. Will not be polled this cycle
per single-poll discipline.

## Result

**SUCCESS** (all three priorities delivered).

- Priority 1: `doublyCompanionMatrix_det_factorization_n_six` axiom-clean.
- Priority 2: Aristotle project `2c4630b2-…` submitted (QUEUED at
  2026-05-06T01:18:52 UTC).
- Priority 3: `plan.md` line 218 (`thm:550A` row), `lean_status.json`
  thm:550A entry, `.prover-state/issues/thm_550A_general_n.md` all
  updated.
- Sorry count remains 0.
- The proof template generalised cleanly without Fallback A (no
  `det_fin_four_explicit` helper required).

## Faithfulness check

For the new theorem `doublyCompanionMatrix_det_factorization_n_six`:

- Entity: `thm:550A`. Textbook statement quoted from
  `extraction/formalization_data/entities/thm_550A.json`:
  > "1 + γ₁z + γ₂z² + ⋯ + γₙzⁿ = det(I − zX) = α(z)β(z) + O(z^{n+1})."
- Lean statement specialises at `n = 6`, so the textbook's `O(z^{n+1})`
  becomes `=O[nhds 0] (z ^ 7)`. **Captures: same content as the
  textbook for the n=6 case.**
- Tautology check: the conclusion is an `IsBigO` claim; `α β : Fin 6
  → ℂ` are universal — no hypothesis matches the conclusion. ✓
- Identity check: proof is a multi-stage matrix-determinant
  computation (explicit `!![…]` reductions, three-layer Laplace
  expansion, `IsBigO.of_bound` with explicit constant), not `exact h`. ✓
- Hypothesis strength: `α, β : Fin 6 → ℂ` are universal in the textbook
  too. ✓
- No new `def`/`structure`/`class` introduced this cycle.

## Dead ends

None. The proof landed first try without Fallback A, mirroring the
cycle 147 result. The strategy's prediction (one cycle per rung,
single-shot `simp […]; ring` after the right simp set) continues to
hold.

## Discovery

Six concrete `n` rungs (n = 1..6) now share the same proof shape:
explicit `!![…]` reduction → Laplace expansion to 3×3 minors → close
by `det_fin_three` → `IsBigO.of_bound` with the convolution
coefficients. The marginal cost per rung is ~50 LOC (cycle 148 added
~155 LOC total but most of that is the docstring and the
`hX`/`hmat`/`set a..f` shapes that scale linearly in n). No new
Mathlib gaps surfaced; `Fin.sum_univ_six` exists and the simp set
needed no extra `Matrix.cons` lemmas (consistent with cycle 145/147).

This consistency strongly suggests the convolution-coefficient
recurrence relative to the (n-1)×(n-1) sub-block (mentioned in the
strategy's "do NOT" list) is the right inductive invariant for a
manual general-`n` closure. But the encoding is multi-cycle
infrastructure work and remains deferred.

## Suggested next approach

For cycle 149, the planner has two open paths:

1. **Continue laddering** to n = 7 (and possibly n = 8) as
   stepping stones, accumulating evidence for the eventual general-`n`
   closure. Each rung is a cycle and adds another piece of in-context
   evidence for Aristotle. Diminishing returns set in around n = 7
   since the proof body length grows linearly while the structural
   insight is unchanged.
2. **Pivot to other §5 work** — e.g. the `def:525A` G-symplectic
   substantive witness, `def:530B/C` order-relative-to-starting-method,
   or `thm:521B` max stability order — which were explicitly listed as
   "do NOT chase" for cycle 148 but become priority candidates once
   the n=6 deliverable is in.
3. **Check Aristotle project `2c4630b2-…`** at the cycle 149 start
   (single-poll). If COMPLETE with a clean general-`n` proof,
   incorporate immediately and close `thm:550A` as `complete`.

A reasonable plan: do (3) at start of cycle 149, then commit to (2)
unless Aristotle returns a usable proof. The n=7 ladder rung (option 1)
is unlikely to be worth the cycle now that the pattern is well
established.
