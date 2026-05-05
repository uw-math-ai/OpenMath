# Cycle 140 Results

## Worked on

`thm:550A` (Doubly companion matrix factorization, Butcher §550 p. 457),
n=2 stepping-stone closure via Aristotle Job B.

## Approach

Followed the strategy decision tree:

1. **Priority 0 (mandatory poll)** — issued single `get_status` call on
   each of the two in-flight Aristotle projects:
   * Job A (general-`n`, project `7062c2a2-4a8b-4fae-b694-9355e06427a9`):
     **IN_PROGRESS at 4 %**, last update 2026-05-05T19:50:00Z (≈40 min
     after submission). Left running per CLAUDE.md "no re-poll" rule.
   * Job B (n=2, project `70f26d67-b37e-4eda-b946-64c9f4616612`):
     **COMPLETE at 100 %**.
2. **Priority 1B** triggered: extracted Job B's proof archive via
   `extract_result` to
   `.prover-state/aristotle_results/cycle_140_job_B/`. The returned
   `B_n_two_factorization.lean` contained a clean proof of
   `doublyCompanionMatrix_det_factorization_n_two` using the route the
   strategy anticipated: `unfold` + `norm_num [Fin.sum_univ_two,
   Matrix.det_fin_two]` + `ring_nf` to expose the residue, then
   `Asymptotics.IsBigO.of_bound` with an explicit bounding constant
   (`‖-(α 0 * β 1) - β 0 * α 1‖ + ‖α 1 * β 1‖`) over the closed unit
   ball around 0.
3. Inlined the proof verbatim (modulo cosmetic indentation/`refine'` →
   `refine` cleanup) directly after `_n_one` in
   `OpenMath/Chapter5/Section550.lean`. No mechanical adaptation was
   needed beyond style.
4. Verified compilation:
   `lake env lean OpenMath/Chapter5/Section550.lean` — clean.
5. Verified axiom-clean status via `lean_verify`:
   `[propext, Classical.choice, Quot.sound]`.
6. Verified full Chapter 5 build: `lake build OpenMath.Chapter5` —
   2787/2787 jobs green.
7. Updated `lean_status.json` (cycle bumped 139 → 140, lean_symbol now
   lists both `_n_one` and `_n_two`, notes capture the cycle-140
   addition and Job A status).
8. Updated `plan.md` `thm:550A` row with the n=2 stepping-stone note.
9. Prepended a "Cycle 140" status update to
   `.prover-state/issues/thm_550A_general_n.md` documenting the
   resolved n=2 sub-witness and the still-deferred general-`n` work.

## Result

**SUCCESS** — Aristotle Job B's n=2 proof inlined verbatim,
axiom-clean, full Chapter 5 build green, sorry count remains 0 (the
two `sorry` matches in `Section550.lean` are docstring/comment
mentions, not proof bodies).

`thm:550A` now carries two stepping-stone witnesses (n=1 from cycle
138, n=2 from cycle 140). Status remains `partial`; the general-`n`
statement is still absent from the file pending Job A's completion or
manual closure infrastructure.

## Faithfulness check

For each new `def` / `theorem` introduced this cycle:

### `OpenMath.Chapter5.Section550.doublyCompanionMatrix_det_factorization_n_two`

Entity ID: `thm:550A`. Textbook statement (quoted from
`extraction/formalization_data/entities/thm_550A.json`):

> The coefficients in the characteristic polynomial of `X`,
> `det(wI − X) = wⁿ + γ₁wⁿ⁻¹ + γ₂wⁿ⁻² + ⋯ + γₙ`, are given by
> `1 + γ₁z + γ₂z² + ⋯ + γₙzⁿ = det(I − zX) = α(z)β(z) + O(z^{n+1})`.

Lean statement captures: **same content (specialised to `n = 2`)**.

The Lean theorem reads
```
IsBigO (𝓝 0)
  (fun z => (1 - z • doublyCompanionMatrix α β).det
              - alphaPoly α z * betaPoly β z)
  (fun z => z ^ 3)
```
which is the textbook's `det(I − zX) − α(z)β(z) = O(z^{n+1})` at
`n = 2` (so `z^{n+1} = z^3`). The doubly companion matrix definition
(`doublyCompanionMatrix`) and the polynomials `alphaPoly`/`betaPoly`
are the same definitions used in `_n_one` (cycle 138, already
faithfulness-checked then); they encode equation (550a) directly.

This is a genuine specialisation, not a tautology: the closed-form
residue is non-trivially `-(α 0 · β 1 + α 1 · β 0) z³ - (α 1 · β 1) z⁴`,
verified by `Matrix.det_fin_two` + `ring_nf`. The proof would fail
if either definition (`doublyCompanionMatrix` or
`alphaPoly`/`betaPoly`) deviated from the textbook.

## Dead ends

None this cycle — Aristotle's proof inlined cleanly on first try.

A potential dead end was avoided: had Job B's returned proof failed
to compile in our context, the strategy specified at most one round
of mechanical adaptation before falling through to Priority 2
(manual n=2 closure). The verbatim inlining worked, so no
adaptation was needed.

## Discovery

* **Aristotle's `IsBigO.of_bound` route is robust at this scale.**
  Rather than fight Mathlib's calculus combinators (`mul_isBigO`,
  `IsBigO.add`, etc.) for the polynomial-asymptotic step, Aristotle
  produced a self-contained `Metric.eventually_nhds_iff` argument:
  pick `δ = 1`, dominate `‖z⁴ · α 1 β 1‖` by `‖z‖³ · ‖α 1 β 1‖` using
  `‖z‖ ≤ 1`, sum the two contributions, bound by `(C₁ + C₂) · ‖z³‖`.
  This pattern should generalize to any `n` once the residue is
  expressed as `z^{n+1} · g(z)` with `g` polynomial — useful template
  for the eventual general-`n` proof.
* **Aristotle's proof uses `unfold doublyCompanionMatrix` + `norm_num
  [Fin.sum_univ_two, Matrix.det_fin_two]` + `ring_nf` to flatten the
  determinant expression in a single sweep.** This is more aggressive
  than the per-entry `fin_cases` + `simp` approach the strategy
  sketched. Worth remembering: at small fixed `n`, `norm_num` with
  `Fin.sum_univ_<n>` lemmas can resolve all index-arithmetic in one
  pass.
* **Job A (general-`n`) at 4 % after ~24h is a meaningful signal.**
  Aristotle's progress on a hard general-`n` proof is essentially
  flat. This is consistent with the cycle-138/139 expectation that
  general `n` requires multi-cycle infrastructure (cofactor-expansion
  induction or eigenvalue-density argument). A future cycle should
  poll once more; if still stuck, cancel and pursue the manual route.

## Suggested next approach

1. **Poll Aristotle Job A (general-n) once more** in cycle 141. If
   still IN_PROGRESS at low %, cancel via `cancel_project` to free
   the slot.
2. **Pivot to a fresh leaf** for cycle 141. Candidates worth
   considering:
   * **A new `def:530B` / `def:530C` foundation.** These ("order
     relative to a starting method") require Taylor-expansion
     infrastructure for SM/ES composition; the strategy explicitly
     warns against opening them as a single-cycle deliverable, but
     the *first piece* — a `Taylor`-friendly composition lemma for
     starting methods — could be an axiom-clean infrastructure
     building block.
   * **`def:551A` / `cor:550C` / `thm:553A`**, the dependents of
     `thm:550A` listed in its entity JSON. With two stepping stones
     of `thm:550A` in hand, downstream consumers may now be tractable
     even at small `n` if their statements admit such specialisation.
   * **Continue §530** with the B2 mixed-stages witness from the
     cycle-140 strategy: `mixedStartingMethod` with non-constant
     `stages` would exercise the heterogeneous-`s_i` design. Pure
     algebra, ~30 LOC, axiom-clean.
3. **Do NOT** attempt manual general-`n` cofactor-expansion induction
   for `thm:550A` until Aristotle Job A's fate is settled — and even
   then, only as a multi-cycle plan with a written infrastructure
   sketch first.
