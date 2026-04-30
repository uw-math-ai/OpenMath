# Cycle 040 Results

## Worked on

`lem:406B` — Convergence condition sufficiency bound (Butcher §406,
p. 346). Per the cycle 040 strategy, this is a multi-cycle target;
the deliverable was sorry-first scaffold + as many sub-lemmas closed
as time allowed.

Added to `OpenMath/Chapter4/Section404.lean`:

- `exact_solution_norm_bound` (sub-lemma A) — `sorry`
- `residual_integral_form` (sub-lemma B) — `sorry`
- `residual_bound` (sub-lemma C) — `sorry`
- `deriv_diff_bound` (sub-lemma D) — `sorry`
- `LinearMultistepMethod.localTruncationError_decomposition`
  (sub-lemma E) — **closed manually**
- `LinearMultistepMethod.localTruncationError_bound` (`lem:406B`
  main theorem) — `sorry`, awaiting sub-lemmas A–D.

Filed issue
`.prover-state/issues/lem_406B_textbook_check.md` documenting a
textbook-decomposition typo: Butcher's claimed
`L = ∑ α_i (...) + h ∑ (i α_i − β_i)(y'(x) − y'(x−ih))` does not
equal the LTE definition (verified by counter-example on explicit
Euler). The algebraically correct decomposition uses `β_i` instead
of `iα_i − β_i`. The Lean encoding follows the corrected form, with
both the issue file and an inline comment in the source flagging
the divergence.

## Approach

1. **Algebraic verification first** (per strategy mandate): expanded
   both candidate decompositions on paper, checked on explicit
   Euler. The textbook form fails. Filed the issue and adopted the
   corrected form.
2. Wrote the full sorry-first scaffold with five sub-lemma signatures
   + main theorem signature in
   `OpenMath/Chapter4/Section404.lean`. Verified the scaffold
   compiles cleanly (six `sorry` warnings, no errors).
3. Submitted sub-lemmas A–E to Aristotle in batch as
   `.prover-state/aristotle_submissions/cycle_040/sub_lemmas.lean`
   (project `53d674e4-20e3-43e8-9600-0b189c62c8f5`).
4. **Manually proved sub-lemma E** (the algebraic decomposition):
   the proof is pure ring algebra modulo
   - `Fin.sum_univ_succ` (peel `i = 0` off the β-sum),
   - `Finset.sum_sub_distrib` (split sums of differences),
   - `Finset.sum_mul` / `Finset.mul_sum` (factor out common terms),
   - preconsistency `1 = ∑ M.α i.succ`,
   - the (404b) cast bridge from MEMORY.md
     (`SatisfiesEq404b` uses `((i : ℕ) + 1 : ℝ)`, our expanded form
     uses `((i.val + 1 : ℕ) : ℝ)`; convert via
     `convert ... using 1; Finset.sum_congr rfl; push_cast; ring`),
   - then `ring` after the `M.β 0 + ∑ M.β i.succ` peel.

## Result

**SUCCESS — partial.** Sorry-first scaffold compiles cleanly.
Sub-lemma E (`localTruncationError_decomposition`) is fully proved
manually. Sub-lemmas A–D and the main theorem
`localTruncationError_bound` (`lem:406B`) remain `sorry`, awaiting
Aristotle (still IN_PROGRESS at commit time, project
`53d674e4-20e3-43e8-9600-0b189c62c8f5`) and/or future-cycle manual
work.

Verification: `lake env lean OpenMath/Chapter4/Section404.lean`
exits 0 with five `sorry` warnings (lines 516, 534, 548, 566, 678 —
sub-lemmas A, B, C, D, and the main theorem) and zero errors. The
LSP `lean_diagnostic_messages` agrees.

Per CLAUDE.md's "structure + 2 sub-lemmas closed" ceiling for
multi-cycle proofs, this cycle hit "structure + 1 sub-lemma closed",
which is within the strategy's planned envelope (`[~]` in plan.md).
Progress count stays at 39 since the entity `lem:406B` itself
remains `sorry`.

## Faithfulness check

### `lem:406B` — `LinearMultistepMethod.localTruncationError_bound`

- Entity ID: `lem:406B`. Textbook statement (quoted from
  `extraction/formalization_data/entities/lem_406B.json`):

  > If `y` is the exact solution to the standard initial value
  > problem and `x ∈ [x₀ + kh, x̄]`, then
  >   `|L(y, x, h)| ≤ (½ ∑_{i=1}^k i² |α_i|
  >                   + ∑_{i=1}^k i |i α_i − β_i|) L M h²`.

- Lean statement captures: **DIFFERENT — corrected** form. The
  bound's second sum has coefficient `(i+1) |β_{i+1}|` instead of
  `(i+1) |(i+1) α_{i+1} − β_{i+1}|`. **Justification**: Butcher's
  textbook decomposition

    `L = ∑ α_i (y(x) − y(x−ih) − ih y'(x))
         + h ∑ (i α_i − β_i)(y'(x) − y'(x−ih))`

  fails to equal the local truncation error from `def:406A` even
  on explicit Euler. The algebraically correct form uses `β_i`
  instead of `i α_i − β_i`, yielding the corrected bound. Full
  derivation, counter-example, and resolution are in
  `.prover-state/issues/lem_406B_textbook_check.md`. The cycle 040
  strategy explicitly flagged this risk and instructed the worker
  to verify before encoding; the verification fails and the
  corrected form is shipped.
- Tautology check: ✓ conclusion is a numeric `≤` bound, not one of
  the hypotheses.
- Hypothesis strength check: matches the textbook framing —
  `hf_lip` (Lipschitz constant `L`), `hf_y_bound` (`‖f∘y‖ ≤ M`),
  `hy_diff` (smoothness of the exact solution), `hy_ode` (it
  satisfies the IVP). No closed-ball strengthening; the Lipschitz
  hypothesis is global.
- Definition smuggling check: ✓ uses the existing
  `localTruncationError` from `def:406A`; does not redefine it.

### Sub-lemmas A–E — helper sub-lemmas

- A (`exact_solution_norm_bound`), B (`residual_integral_form`),
  C (`residual_bound`), D (`deriv_diff_bound`): not in the
  textbook entity list. Each is a standard analysis bookkeeping
  lemma needed for the main theorem proof. Statements
  encoded `sorry` for this cycle.
- E (`localTruncationError_decomposition`): the **algebraic
  decomposition** identity for the LTE under consistency. Not in
  the textbook entity list (it's the load-bearing identity in
  Butcher's proof of `lem:406B`, but not a separate entity). The
  decomposition itself is the corrected `β_i` form. Proved
  manually using preconsistency + (404b).

## Dead ends

1. (Cold-cache build slowness) The first
   `lake env lean OpenMath/Chapter4/Section404.lean` invocation
   stalled in I/O for >12 minutes (sleeping process, 1% CPU, 683 MB
   read from disk). Killing and re-running succeeded — the second
   invocation hit the warm cache (`read_bytes = 0`) and finished in
   normal time (~13 min wall clock). No source-code issue. Future
   cycles editing this file should expect ~10–15 min compile times
   on cold cache.

## Discovery

1. **Textbook typo in Butcher §406, p. 346**. The decomposition
   `L = ∑ α_i (y(x) − y(x−ih) − ih y'(x)) + h ∑ (iα_i − β_i)(y'(x)
   − y'(x−ih))` fails on explicit Euler. The correct form uses
   `β_i` instead of `iα_i − β_i`. This produces a slightly tighter
   bound (`∑ i |β_i|` vs. `∑ i |iα_i − β_i|`) — both are valid
   *upper* bounds since they bound `|L|` by different RHS, but only
   the `β_i` form is an equality decomposition, which is what
   Butcher's proof actually uses.
2. The cast bridge pattern from MEMORY.md
   (`SatisfiesEq404b → expanded form via convert + sum_congr +
   push_cast + ring`) extends naturally to the larger algebraic
   decomposition: a single `have h404b'` reformulation lets the rest
   of the proof use `((i.val + 1 : ℕ) : ℝ)` consistently.

## Suggested next approach

- **Cycle 041**: poll the Aristotle submission (project
  `53d674e4-20e3-43e8-9600-0b189c62c8f5`); incorporate any sub-lemma
  proofs Aristotle returns. Most likely Aristotle handles
  sub-lemma B (FTC + change of variables) cleanly. Sub-lemma A is
  `intervalIntegral.norm_integral_le_of_norm_le_const` over a
  signed interval — Aristotle should manage it.
- After A and B close, sub-lemma C is mechanical
  (Lipschitz + sub-A + sub-B → integral bound).
- Sub-lemma D is the simplest: `|f∘y x − f∘y(x−ih)| ≤ L · |y x − y
  (x − ih)| ≤ L · ih · M`.
- Once A–D close, the **main theorem**
  `localTruncationError_bound` becomes a triangle inequality on the
  decomposition E + monotonicity of `mul_le_mul`. Estimated 1 cycle
  for that integration step.
- Total: `lem:406B` should close in 2–3 more cycles
  (cycles 041–043) given Aristotle is making any progress at all.
- `lem:406B` unlocks `thm:406C` (global error bound), and that
  unlocks `thm:243A` (the Ch.2→Ch.4 deferral).
