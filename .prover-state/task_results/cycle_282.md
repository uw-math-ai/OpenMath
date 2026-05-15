# Cycle 282 Results

## Worked on

`lem:342A` (342f) three-term recurrence — Butcher §342, p. 236:
`n · P_n^*(x) = (2x − 1)(2n − 1) · P_{n−1}^*(x) − (n − 1) · P_{n−2}^*(x)`
for `n = 2, 3, 4, …`.

Per strategy:
- **P1** — fire-and-forget Aristotle submission for the general theorem.
- **P2** — manual ship of three concrete sanity-check witnesses at
  `n ∈ {2, 3, 4}` via direct polynomial computation.
- **P3** — scoping doc for (342g) distinct real zeros.

## Approach

### P1 — Aristotle submission (general 342f)

Created `.prover-state/aristotle_submissions/cycle_282/342f_recurrence.lean`
bundling cycles 271–281's results as cited axioms (definition +
`eval_one`, `eval_one_sub`, `eval_zero`, `natDegree`, `rodrigues`,
`orthogonal`, `norm_sq`, and explicit `_zero` through `_four` forms).
Target sorry is the general (342f) recurrence theorem
parameterized over `n` with hypothesis `hn : 2 ≤ n`, stated as

```lean
theorem butcherShiftedLegendre_recurrence (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) • butcherShiftedLegendre n =
      Polynomial.C (2 * (n : ℝ) - 1)
        * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
        * butcherShiftedLegendre (n - 1)
      - Polynomial.C ((n : ℝ) - 1) * butcherShiftedLegendre (n - 2) := by sorry
```

Strategy hint included in the file's docstring summarises the
textbook 4-step argument (degree comparison via leading-coefficient
identity `n · C(2n,n) = 2(2n−1) · C(2n−2, n−1)`, parity → `deg(Q) < n−1`,
orthogonality → `Q ⊥ P_k^*` for `k < n−2`, fix `P_{n−2}^*` coefficient
via `x = 1` substitution).

Submitted via `mcp__aristotle__submit_file` — project ID
`c8b8f138-f875-4263-94ec-74533b5120d7`, status `QUEUED` on submission.
**Not polled this cycle** (single-poll discipline; cycle 283 to poll).

### P2 — Concrete recurrence witnesses (n = 2, 3, 4)

For each `n ∈ {2, 3, 4}`, used `Polynomial.funext` reducing the
polynomial equality to the corresponding scalar identity `∀ x : ℝ, …`,
then substituted the explicit forms `butcherShiftedLegendre_{n,
n-1, n-2}` (from cycles 273–275), simplified evals via the
`Polynomial.eval_*` lemmas + `smul_eq_mul`, and closed by `ring`.
Recipe per the strategy's "cycle 180's proven recipe for
explicit-polynomial-arithmetic IDs".

### P3 — (342g) scoping doc

Wrote `.prover-state/issues/lem_342A_g_zeros_scoping.md` (~85 lines
markdown) outlining the sign-change-contradiction proof for (342g),
listing required Mathlib hooks (`Polynomial.roots`, IVT,
`Polynomial.continuous`), LOC budget (~150), risk assessment, and the
cycle 283+ outlook (target via Aristotle once 342f lands).

## Result

**SUCCESS** — P1 + P2 + P3 all delivered.

- **P1**: Aristotle project `c8b8f138-f875-4263-94ec-74533b5120d7`
  submitted with prompt summarizing the goal and citing available
  axioms. Cycle 283 to poll.
- **P2**: 3 new theorems in `OpenMath/Chapter3/Section342.lean`:
  `butcherShiftedLegendre_recurrence_two`,
  `butcherShiftedLegendre_recurrence_three`,
  `butcherShiftedLegendre_recurrence_four`. File compiles
  (`lake env lean OpenMath/Chapter3/Section342.lean`, exit 0;
  `lake build OpenMath.Chapter3.Section342` succeeds). All three
  axiom-clean: `[propext, Classical.choice, Quot.sound]`. File grew
  from 1871 → ~1949 LOC. Repo sorry count: 0 → 0.
- **P3**: `lem_342A_g_zeros_scoping.md` issue file written.

## Faithfulness check

### `butcherShiftedLegendre_recurrence_two`

- Entity ID `lem:342A` (342f); textbook statement (from
  `extraction/formalization_data/entities/lem_342A.json`):
  > `n P_n^*(x) = (2x − 1)(2n − 1) P_{n−1}^*(x) − (n − 1) P_{n−2}^*(x)`,
  > `n = 2, 3, 4, …`.
- Lean statement at `n = 2`:
  `(2 : ℝ) • P_2^* = C 3 · (C 2 · X − C 1) · P_1^* − C 1 · P_0^*`.
  Matches textbook formula evaluated at `n = 2`: `n = 2`, `(2n − 1) = 3`,
  `(n − 1) = 1`. **Same content.**
- Tautology check: conclusion ≠ any hypothesis (no hypotheses; closed
  body). Not a tautology.
- Identity check: proof body is `apply Polynomial.funext; intro x; rw
  [...]; simp [...]; ring`. Genuine polynomial-arithmetic computation,
  not an alias.
- Hypothesis strength: no hypotheses; matches textbook's `n ≥ 2`
  specialization at `n = 2`.
- Definition smuggling: this is a sanity-check witness of the
  textbook formula at a concrete numerical `n`, not a definition or
  reformulation.

### `butcherShiftedLegendre_recurrence_three`

- Same entity / textbook clause as above, evaluated at `n = 3`:
  `(3 : ℝ) • P_3^* = C 5 · (C 2 · X − C 1) · P_2^* − C 2 · P_1^*`
  matches `n = 3`, `(2n − 1) = 5`, `(n − 1) = 2`. **Same content.**
- Tautology/identity/strength/smuggling checks: all pass — same
  shape as `_recurrence_two`.

### `butcherShiftedLegendre_recurrence_four`

- Same entity / textbook clause as above, evaluated at `n = 4`:
  `(4 : ℝ) • P_4^* = C 7 · (C 2 · X − C 1) · P_3^* − C 3 · P_2^*`
  matches `n = 4`, `(2n − 1) = 7`, `(n − 1) = 3`. **Same content.**
- Tautology/identity/strength/smuggling checks: all pass.

## Dead ends

None this cycle. The `Polynomial.funext + ring` recipe worked
first-try for all three witnesses; no fallback to `Polynomial.ext` +
per-coefficient `match` (the cycle 280 template) needed.

## Discovery

- The `Polynomial.funext` recipe with `simp [Polynomial.eval_*, smul_eq_mul]
  + ring` closes explicit-`n` polynomial-arithmetic identities with
  no per-case fiddling, in contrast to the `Polynomial.ext` route
  (which requires per-coefficient `match` on `k`). Confirms cycle
  180's documented preference for the eval-route over the
  coefficient-route for identities of this shape.
- The compile output's "Try this: ring_nf" message is purely a linter
  suggestion on an earlier `simp` invocation in the file (around line
  730–760), not an error — confirmed via
  `mcp__lean-lsp__lean_diagnostic_messages` with `severity: error`
  returning empty.

## Suggested next approach

Cycle 283:
1. **Single-poll** Aristotle project `c8b8f138-f875-4263-94ec-74533b5120d7`
   for the general (342f). Branching:
   - If COMPLETE → integrate analogously to cycle 281's `d4ce527b`
     integration, extracting any helper machinery into a new
     `Section342RecurrenceHelpers.lean` if needed.
   - If IN_PROGRESS at low % → extend the recurrence-witness ladder
     to `n = 5, 6, 7` as Branch B fallback (each ~20 LOC via the
     same `Polynomial.funext + ring` recipe; cycles 278–280's
     explicit forms `_five`/`_six`/`_seven` are already in hand).
2. Once (342f) lands, fire (342g) on Aristotle citing all of
   (342a)–(342f). The scoping doc
   `.prover-state/issues/lem_342A_g_zeros_scoping.md` lays out the
   plan.
3. Alternative pivot: open `lem:342B` (Gaussian quadrature exactness
   degree) which can now consume orthogonality + norm-square +
   recurrence witnesses (cycle 282) as inputs.
