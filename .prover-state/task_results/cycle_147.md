# Cycle 147 Results

## Worked on

`doublyCompanionMatrix_det_factorization_n_five` — the n=5 stepping
stone for `thm:550A` (Butcher §550, p. 457). Fifth concrete-`n`
axiom-clean witness in the ladder n=1, 2, 3, 4, 5 closing the
factorization `det(I − zX) − α(z)·β(z) = O(z^{n+1})` for the doubly
companion matrix construction.

## Approach

Two-track per the cycle 147 strategy:

1. **Aristotle submission** (Priority 1): Built a self-contained
   snippet at `.prover-state/aristotle_submissions/cycle_147/n_five_factorization.lean`
   containing `doublyCompanionMatrix`, `alphaPoly`, `betaPoly`, the
   verbatim cycle 145 n=4 closed proof as a template, and the n=5
   target with `sorry`. Submitted via `mcp__aristotle__submit_directory`;
   project ID **`9643742d-aac9-4e57-9f7a-2ba69a5f25ee`**.

2. **Manual closure** (Priority 2, attempted in parallel during the
   30-minute Aristotle window): Extended the cycle 145 n=4 template
   verbatim. The proof body has the same two-step structure:

   - **Step 1 — `h_diff` residue factorization**: `funext z`, then
     reduce `doublyCompanionMatrix α β` at n=5 to an explicit `!![…]`
     5×5 matrix (`ext i j; fin_cases i <;> fin_cases j <;> simp
     [doublyCompanionMatrix]`); reduce `1 − z • X` to a second
     explicit 5×5 `!![…]` (a second `fin_cases` block with `first
     | (simp; ring) | simp`); expand the 5×5 determinant via
     `Matrix.det_succ_row_zero` (5×5 → five 4×4 minors), then
     `simp [Fin.sum_univ_five, Fin.sum_univ_four,
     Matrix.det_succ_row_zero (n := 3), Matrix.det_fin_three,
     alphaPoly, betaPoly, …]; ring` collapsed the polynomial identity
     in a single pass (the inner `det_succ_row_zero (n := 3)` simp
     entry handles the second Laplace step into 3×3 minors).

   - **Step 2 — `IsBigO.of_bound`**: explicit constant
     `‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖` where `a..e` are the five
     convolution coefficients; `Metric.eventually_nhds_iff` with
     radius 1; bound `‖a + y·b + y²·c + y³·d + y⁴·e‖` by
     `‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖` via four `norm_add_le` cascades and
     four `mul_le_of_le_one_left` sub-bounds (one for each `y^k * x`
     term).

   The proof body is ~140 LOC inserted between
   `doublyCompanionMatrix_det_factorization_n_four` and
   `end OpenMath.Chapter5.Section550`.

## Result

**SUCCESS — manual closure landed axiom-clean.**

`lake env lean OpenMath/Chapter5/Section550.lean` completed in
8m 11s with no errors or warnings. `mcp__lean-lsp__lean_verify`
on `OpenMath.Chapter5.Section550.doublyCompanionMatrix_det_factorization_n_five`
returned `axioms = [propext, Classical.choice, Quot.sound]` —
axiom-clean.

The single-shot `simp […]; ring` recipe from cycle 145's n=4
proof generalised cleanly to n=5; **Fallback A (private
`det_fin_four_explicit` helper) was not needed**. This is the most
encouraging outcome possible: it suggests the same recipe will lift
to n=6 and n=7 as well, with the per-n cost dominated by transcribing
the (n+1)-many convolution coefficients in the `IsBigO.of_bound`
constant.

Aristotle project `9643742d-aac9-4e57-9f7a-2ba69a5f25ee` was at 5%
IN_PROGRESS at the post-build poll (single poll, per CLAUDE.md;
roughly 11 minutes after submission). Per strategy "If still
IN_PROGRESS at <50%: treat as a miss; rely on manual closure" — so
the manual proof is the committed version. (Per strategy: "if the
manual attempt also closed, prefer the **manual** version
(provenance and reproducibility)" regardless of Aristotle's outcome.)

## Faithfulness check

For the new theorem introduced this cycle:

- Entity ID and textbook statement (quoted from `entities/thm_550A.json`):
  > "The coefficients in the characteristic polynomial of X,
  > det(wI − X) = wⁿ + γ₁wⁿ⁻¹ + γ₂wⁿ⁻² + ⋯ + γₙ, are given by
  > 1 + γ₁z + γ₂z² + ⋯ + γₙzⁿ = det(I − zX) = α(z)β(z) + O(z^{n+1})."

- New Lean theorem name:
  `OpenMath.Chapter5.Section550.doublyCompanionMatrix_det_factorization_n_five`.

- Lean statement captures: **specialisation at `n = 5`**.
  The Lean statement is `(1 - z • doublyCompanionMatrix α β).det
  - alphaPoly α z * betaPoly β z =O[nhds 0] (z ^ 6)` for arbitrary
  `α β : Fin 5 → ℂ`. This is precisely the textbook conclusion
  `det(I − zX) = α(z)·β(z) + O(z^{n+1})` at `n = 5` (so `z^{n+1}` =
  `z^6`), with the convention `(α 0, …, α (n-1)) ↔ (α₁, …, αₙ)`
  (textbook 1-based vs Lean 0-based) explicitly documented in the
  file preamble. **Same content as the textbook for the n=5 case.**

- Tautology check: the conclusion `IsBigO … (z^6)` does NOT appear
  as a hypothesis. The hypotheses are only the arbitrary `α β :
  Fin 5 → ℂ`. ✓

- Identity check: the proof is decidedly not `exact h` — it is a
  multi-stage matrix-determinant calculation closed with a
  ~10-line `IsBigO.of_bound` argument. ✓

- Hypothesis strength check: `α β : Fin 5 → ℂ` are the only
  hypotheses; cannot be weakened (the theorem is universal in
  `α, β`). ✓

- Definition smuggling check: no new definitions introduced — the
  theorem is a pure statement about pre-existing
  `doublyCompanionMatrix`, `alphaPoly`, `betaPoly`. ✓

- Absent theorem check: no comments promise sorry'd content. ✓

No new `def`/`structure`/`class` introduced.

## Dead ends

None encountered this cycle. The cycle 145 template generalised
cleanly to n=5 on the first attempt:

- The `ext + fin_cases <;> simp [doublyCompanionMatrix]` reduction
  worked first try at n=5 (5×5 = 25 entries, all closed by simp).
- The `1 − z • X` reduction with `first | (simp; ring) | simp` worked
  first try.
- The `simp […]; ring` polynomial-identity collapse worked first
  try; no Fallback A needed.
- The `IsBigO.of_bound` step worked first try with the obvious
  five-term cascade.

## Discovery

1. **`Matrix.det_succ_row_zero (n := 3)` as a simp lemma**: explicitly
   passing `(n := 3)` forces the simp engine to apply
   `det_succ_row_zero` to *4×4* minors (after the outer Laplace step
   reduced the 5×5 to four-row submatrices), recursing into 3×3
   sub-determinants closable by `Matrix.det_fin_three`. This is the
   keystone trick that lets the same simp set handle two Laplace
   layers in one pass without a private helper. This generalises the
   cycle 145 single-Laplace recipe.

2. **The simp set scales linearly in matrix size**: the n=4 and n=5
   simp sets are identical except that n=5 needs `Fin.sum_univ_five`
   added to `Fin.sum_univ_four`. This suggests that n=6 will need
   `Fin.sum_univ_six` plus `Matrix.det_succ_row_zero (n := 4)`, with
   no further tactic novelty. (At some point n the simp tree will
   become too deep and timeouts will require Fallback A — but n=5
   was comfortably within heartbeats budget.)

3. **8-minute single-file build time**: `lake env lean
   Section550.lean` took 8m 11s wall-clock (real). This is large
   enough that running multiple verification builds in a single
   cycle is impractical. Per CLAUDE.md, single-file builds are still
   strictly preferred over `lake build`.

4. **Aristotle is slow on this ladder**: at 11 minutes post-
   submission Aristotle was still at 5% on a problem manually closable
   in ~5 minutes of editing + 8 minutes of verification. The submission
   remains useful as a backup but should not be relied on for the
   primary path on stepping-stone-ladder problems.

## Suggested next approach

The next rung of the ladder is **n=6**. Same template:
1. Five 5×5 `!![…]` rewrites (the matrix and its `1 − z·X` form),
   with sub-diagonal of length 5.
2. Three Laplace expansions: `Matrix.det_succ_row_zero` for the 6×6 →
   six 5×5 minors, then `Matrix.det_succ_row_zero (n := 4)` for each
   5×5 → 4×4, then `Matrix.det_succ_row_zero (n := 3)` for each
   4×4 → 3×3, finally `Matrix.det_fin_three` on the 3×3.
3. Six convolution coefficients in the `IsBigO.of_bound` constant
   and a five-step `norm_add_le` cascade.

If n=6 also lands in a single cycle, the planner may judge that the
cofactor-expansion induction (recursive cofactor expansion of
`doublyCompanionMatrix` at the rank level, with strong induction on
n) is now within single-cycle reach for the general statement —
since the per-n proof is now provably mechanical and could be
automated by an inductive `Fin.induction` argument. That would be the
infrastructure path to closing the general-`n` theorem and resolving
issue `thm_550A_general_n.md`.

Alternatively, if the planner judges five concrete data points
sufficient evidence for the pattern, the priority could shift to
the long-deferred high-value targets: `thm:535A` (Underlying one-step
method, GLM; needs rooted-tree-indexed solutions in §5 which we
have not built); `def:530B` (Order relative to starting method;
needs Taylor-expansion residual machinery); or `thm:521B`
(Maximum stability order for given steps).

The Aristotle project `9643742d-aac9-4e57-9f7a-2ba69a5f25ee` is left
running. A future cycle MAY check it once if the cycle budget
permits, mainly for telemetry on Aristotle's behaviour on such
problems; but it is no longer on the critical path.
