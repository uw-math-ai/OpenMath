# Cycle 282 Strategy

## §A. Status snapshot (post-cycle 281)

- **No pending Aristotle jobs.** Project `d4ce527b` returned COMPLETE
  during cycle 281 and the general (342d) `butcherShiftedLegendre_norm_sq`
  ships axiom-clean at `OpenMath/Chapter3/Section342.lean`
  (with helpers in `Section342NormSqHelpers.lean`).
- **No sorries** repo-wide.
- **§342 / lem:342A progress** (4 of 7 clauses closed; 7 of 7 small-n
  ladder rungs for (342d) shipped):
  - (342a) `butcherShiftedLegendre_orthogonal` — cycle 277, axiom-clean.
  - (342b) `butcherShiftedLegendre_eval_one` — cycle 271, axiom-clean.
  - (342c) `butcherShiftedLegendre_eval_one_sub` (parity) — cycle 271, axiom-clean.
  - (342d) `butcherShiftedLegendre_norm_sq` (general n) — cycle 281, axiom-clean.
  - (342e) `butcherShiftedLegendre_rodrigues` — cycle 272, axiom-clean.
  - Ladder rungs `_norm_sq_{0..7}` — cycles 274–280, axiom-clean.
  - **(342f) three-term recurrence** — OPEN.
  - **(342g) `n` distinct real zeros in (0,1)** — OPEN.
- **plan.md** has `lem:342A` marked `[~]` (partial). Status stays partial
  until both (342f) and (342g) close.

## §B. Cycle 282 priorities

### P1 — fire-and-forget Aristotle on (342f) (5 min setup, no polling this cycle)

**Target**: the Bonnet-style three-term recurrence

```
  n · P_n^*(x) = (2x − 1)(2n − 1) · P_{n−1}^*(x) − (n − 1) · P_{n−2}^*(x),
                                                    n = 2, 3, 4, …
```

This is the textbook (342f) verbatim. Aristotle's track record on §342
this run: (342a) returned COMPLETE in ~3 cycles (project `727396d5`,
cycle 277), (342d) returned COMPLETE in ~7 cycles (project `d4ce527b`,
cycle 281). With orthogonality + norm-square + Rodrigues + leading
coefficient + parity all axiom-clean and citable, (342f) is
well-positioned for a similar trajectory.

**Recipe** (do this first thing in cycle 282):

1. Create `.prover-state/aristotle_submissions/cycle_282/342f_recurrence.lean`
   containing:
   - Header `import Mathlib` and `open Polynomial`.
   - Cycle 271–281 results as **cited axioms** (DO NOT include their
     proofs — just signatures so Aristotle can use them as hypotheses):
     - `butcherShiftedLegendre : ℕ → Polynomial ℝ` (definition).
     - `butcherShiftedLegendre_eval_one`
     - `butcherShiftedLegendre_eval_one_sub` (parity / 342c)
     - `butcherShiftedLegendre_eval_zero`
     - `butcherShiftedLegendre_natDegree`
     - `butcherShiftedLegendre_rodrigues`
     - `butcherShiftedLegendre_orthogonal`
     - `butcherShiftedLegendre_norm_sq`
     - `butcherShiftedLegendre_zero`, `_one`, `_two`, `_three`, `_four`
       (explicit forms, useful for Aristotle to sanity-check small `n`).
   - Target theorem:
     ```lean
     theorem butcherShiftedLegendre_recurrence (n : ℕ) (hn : 2 ≤ n) :
         (n : ℝ) • butcherShiftedLegendre n =
           Polynomial.C ((2 * (n : ℝ) - 1))
             * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
             * butcherShiftedLegendre (n - 1)
           - Polynomial.C ((n : ℝ) - 1) * butcherShiftedLegendre (n - 2) := by
       sorry
     ```
   - Strategy hint in a docstring:
     ```
     Textbook proof outline (Butcher §342, p. 236):
       Step 1. Let Q := n·P_n^* − (2x−1)(2n−1)·P_{n−1}^* − (n−1)·P_{n−2}^*.
               Compare highest-degree coefficients to show Q has degree < n.
       Step 2. By parity (342c), Q has the same parity as n, so degree < n−1.
       Step 3. Q is orthogonal to P_k^* for k < n−2 (by (342a) + Q's degree).
       Step 4. Substitute x = 1 to fix the P_{n−2}^* coefficient
               (LHS = n·1 = n; (2x−1) = 1 at x=1, so RHS = (2n−1) − (n−1) = n). ✓

     Leading-coefficient check:
       lc(P_n^*) = C(2n, n); lc((2x−1)(2n−1)·P_{n−1}^*) = 2(2n−1)·C(2n−2, n−1).
       Identity n·C(2n,n) = 2(2n−1)·C(2n−2, n−1) holds via Nat.choose factorial
       expansion. This is the load-bearing identity for Step 1.
     ```
2. Submit via `mcp__aristotle__submit_file` with a ~200-character
   prompt summarizing the goal and citing the available lemmas.
3. Record the project ID in `task_results/cycle_282.md`.
4. **DO NOT** poll this cycle. Per CLAUDE.md, single-poll discipline
   only; cycle 283+ will poll. Expected first-poll result is
   IN_PROGRESS at low percentage.

### P2 — manual ship: concrete recurrence sanity-check witnesses (40-60 min)

While Aristotle works on the general theorem, ship **three concrete-`n`
non-vacuity witnesses** that verify the recurrence formula at small
`n ∈ {2, 3, 4}` by direct polynomial computation. Each witness consumes
cycles 273–277's explicit forms (`_zero` through `_four`) and verifies
the recurrence holds at those `n`.

**Why this is the right cycle 282 deliverable**: (a) verifies the
recurrence form is correctly stated, ruling out sign/coefficient
errors before Aristotle's general proof lands; (b) provides
regression witnesses that compose with the general theorem when it
ships; (c) is self-contained (no Aristotle dependency); (d) ~15-20
LOC per witness fits within single-cycle budget.

**Recommended proof shape** — use `Polynomial.funext + ring`
(cycle 180's proven recipe for explicit-polynomial-arithmetic IDs):

```lean
theorem butcherShiftedLegendre_recurrence_two :
    (2 : ℝ) • butcherShiftedLegendre 2 =
      Polynomial.C 3 * (Polynomial.C 2 * Polynomial.X - Polynomial.C 1)
        * butcherShiftedLegendre 1
      - Polynomial.C 1 * butcherShiftedLegendre 0 := by
  apply Polynomial.funext
  intro x
  rw [butcherShiftedLegendre_two, butcherShiftedLegendre_one,
      butcherShiftedLegendre_zero]
  simp [Polynomial.eval_smul, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_one, smul_eq_mul]
  ring
```

The `Polynomial.funext` reduces the polynomial equality to a
real-arithmetic identity `∀ x : ℝ, …` which `ring` always handles —
unlike `Polynomial.ext` (coefficient route), which stalled in cycles
172/173 on `Polynomial.C` constant folding.

**Fallback** (only if `funext + ring` stalls): use `Polynomial.ext`
+ per-coefficient `match k with | 0 | 1 | 2 | k+3 => …` like
cycle 280's `bdf2LMM_aPoly_eq` template. Do NOT introduce a sorry-
first scaffold.

**Numerical sanity-check (verified on paper, in this strategy)**:

n=2: `(2)·P_2^* = 3(2x−1)·P_1^* − 1·P_0^*`
- LHS: `2(6x² − 6x + 1) = 12x² − 12x + 2`.
- RHS: `3(2x−1)² − 1 = 12x² − 12x + 2`. ✓

n=3: `(3)·P_3^* = 5(2x−1)·P_2^* − 2·P_1^*`
- LHS: `3(20x³ − 30x² + 12x − 1) = 60x³ − 90x² + 36x − 3`.
- RHS: `5(2x−1)(6x² − 6x + 1) − 2(2x−1) = 60x³ − 90x² + 36x − 3`. ✓

n=4: `(4)·P_4^* = 7(2x−1)·P_3^* − 3·P_2^*`
- LHS: `4(70x⁴ − 140x³ + 90x² − 20x + 1) = 280x⁴ − 560x³ + 360x² − 80x + 4`.
- RHS: `7(2x−1)(20x³ − 30x² + 12x − 1) − 3(6x² − 6x + 1) =`
       `280x⁴ − 560x³ + 360x² − 80x + 4`. ✓

All three check arithmetically. Each witness should close in ~10–20
LOC via the `Polynomial.funext + ring` recipe.

**P2 deliverable target**: three new public theorems
`butcherShiftedLegendre_recurrence_two`, `_recurrence_three`, and
`_recurrence_four` appended to `OpenMath/Chapter3/Section342.lean`
after `butcherShiftedLegendre_norm_sq` (around line 1873). Total
≤ 60 LOC. All axiom-clean (`[propext, Classical.choice, Quot.sound]`).

### P3 — stretch: scoping doc for (342g) distinct real zeros

If P1+P2 leave 20+ minutes, write a small scoping note in
`.prover-state/issues/lem_342A_g_zeros_scoping.md` (~80 lines
markdown, NO Lean code) outlining the cycle 283+ plan for (342g):

- Textbook proof: contradiction with sign-change polynomial Q (where
  Q(x) := (x − x_1)…(x − x_k) is the product of sign-change points;
  ∫ P_n^* · Q ≠ 0 by sign argument but = 0 by orthogonality if
  k < n).
- Mathlib hooks likely needed: `Polynomial.card_roots`,
  `intermediate_value_Ioo` (IVT), `Polynomial.roots_count_le_degree`,
  sign-change combinatorics.
- LOC budget estimate: ~150 LOC.
- Risk assessment: sign-change manipulations are fiddly in Lean; may
  warrant Aristotle submission once (342f) lands.

Skip P3 if cycle budget tight — it is not load-bearing for any
upstream entity.

## §C. What NOT to try

1. **DO NOT attempt manual general (342f).** Cycle 273 documented the
   dead end: both `Polynomial.ext` (coefficient route) and
   `Polynomial.funext` (eval route) at general `n` require Pascal-style
   binomial identities on `Nat.choose` that `ring` cannot close. The
   textbook proof requires substantive parity + degree reasoning
   across multiple polynomials (Q's degree < n−1 follows from parity;
   Q ⊥ lower P_k^* follows from degree + orthogonality). This is
   multi-cycle work — let Aristotle handle it.
2. **DO NOT attempt manual general (342g).** Sign-change combinatorics
   in Lean is multi-cycle. Target via Aristotle after (342f) lands.
3. **DO NOT poll Aristotle projects `727396d5` or `d4ce527b`.** Both
   are COMPLETE and their results are already integrated. Polling
   wastes the slot quota.
4. **DO NOT touch `OpenMath/Chapter4/Section441.lean`.** 43+
   consecutive GPFS-blocked compile timeouts since cycle 182; see
   `cycle_182_gpfs_slowness.md`. Skip per the documented pathology.
5. **DO NOT introduce sorries.** Cycle 200/201, 149/150, 138/139
   rollback precedents stand. If P2's recurrence witnesses don't
   close cleanly with `Polynomial.funext + ring`:
   - First fallback: try `Polynomial.ext + simp [Polynomial.coeff_*]
     + match k with` per cycle 280's BDF2 template.
   - Final fallback: drop n=4 and ship only n=2 + n=3 as P2
     deliverable. Do not leave behind a sorry-first scaffold.
6. **DO NOT split `Section342.lean` into multiple files this cycle.**
   File is ~1870 LOC; splitting can wait. Cycle 281's extraction of
   `Section342NormSqHelpers.lean` already managed growth this run.
7. **DO NOT bump `maxHeartbeats`**. CLAUDE.md hard rule.
8. **DO NOT introduce `axiom` / `constant` declarations.** CLAUDE.md
   hard rule.

## §D. Faithfulness checklist (P2 witnesses)

For each new `butcherShiftedLegendre_recurrence_{two,three,four}`:

- [ ] Textbook statement quoted in docstring:
      *"n P_n^*(x) = (2x − 1)(2n − 1) P_{n−1}^*(x) − (n − 1) P_{n−2}^*(x),
      n = 2, 3, 4, …"* — Butcher §342 (342f).
- [ ] Lean statement captures the exact specialization at n ∈ {2,3,4}
      with no weakening or strengthening of the formula.
- [ ] **Definition smuggling check**: the witness is a sanity check
      of the textbook recurrence formula at concrete `n`, not a
      definition or characterization theorem in disguise.
- [ ] **Tautology check**: the proof body must perform genuine
      polynomial arithmetic (`Polynomial.funext + ring` substantively
      reduces both sides), not rename a hypothesis or close by `rfl`.
      Verify scanner is clean post-write.
- [ ] **Identity check**: not a single `exact h` — each witness must
      genuinely compute.

## §E. Cycle 282 ship target summary

| Priority   | Deliverable                                            | LOC    | Risk |
|------------|--------------------------------------------------------|--------|------|
| P1         | Aristotle submission for general (342f) recurrence     | n/a    | low  |
| P2         | 3 concrete recurrence witnesses (n=2,3,4)              | ~50    | low  |
| P3 stretch | Scoping doc for (342g)                                 | ~80 md | nil  |

Net cycle effect: `lem:342A` row remains `[~]` (partial); ladder of
concrete recurrence witnesses joins the existing `_norm_sq_{0..7}`
ladder; Aristotle slot productively used. Repo sorry count: **0 → 0**.

## §F. Cycle 283+ outlook (no work this cycle)

- Single-poll Aristotle (342f) project. If COMPLETE, integrate
  analogously to cycle 281's `d4ce527b` integration. If IN_PROGRESS
  at low %, continue ladder (n=5, 6, 7 recurrence witnesses) as
  Branch B fallback.
- Once (342f) lands, fire (342g) on Aristotle with all of (342a)–(342f)
  + Rodrigues + parity as cited axioms.
- Or pivot to `lem:342B` (Gaussian quadrature exactness) — natural §342
  follow-up unblocked by cycle 281.

## §G. Pre-flight reminders for the worker

1. Run `git log --oneline -3` first to confirm cycle 281 commit is at
   HEAD. (Defensive — phantom-verdict pattern documented in
   `phantom_commit_verdict_pattern.md`. Trust git, not `attempts.md`.)
2. Run `grep -c sorry OpenMath/Chapter3/Section342.lean` — expect 0.
3. Compile `lake env lean OpenMath/Chapter3/Section342.lean` once
   before P2 to confirm warm cache state.
4. After P2, `#print axioms` on each new witness; expect
   `[propext, Classical.choice, Quot.sound]`.
5. Write `task_results/cycle_282.md` summarizing P1 (Aristotle
   project ID), P2 (LOC + axioms), and (if shipped) P3 (path to
   issue file).
6. Update `plan.md` `lem:342A` row with the cycle 282 entry.
7. **DO NOT** update `lean_status.json` for `lem:342A` this cycle —
   status remains `partial` until both (342f) and (342g) land.
