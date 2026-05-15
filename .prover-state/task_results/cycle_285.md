# Cycle 285 Results

## Worked on
- **P0 (mandatory)**: Single-poll Aristotle project `c8b8f138-f875-4263-94ec-74533b5120d7`
  for general §342 (342f) three-term recurrence. Result: IN_PROGRESS at 12% —
  third consecutive stall (cycles 283/284 + this poll). Triggers Branch B
  "third stall": cancel + execute P1 + execute P2.
- **P1**: Cancelled `c8b8f138`; built strengthened resubmission
  `.prover-state/aristotle_submissions/cycle_285/342f_recurrence_v2.lean` and
  submitted as new Aristotle project `efe4940e-0931-4fb2-8549-7eafab20d7f7`
  (QUEUED at end of cycle).
- **P2**: Added two theorems to `OpenMath/Chapter3/Section342.lean`:
  - `butcherShiftedLegendre_nine` — explicit form of `P_9^*` (degree-9
    expansion derived from `Polynomial.coeff_shiftedLegendre` at n=9, with
    outer Butcher sign `(-1)^9 = -1`).
  - `butcherShiftedLegendre_recurrence_nine` — instance of (342f) at n=9:
    `9 · P_9^* = 17 · (2X − 1) · P_8^* − 8 · P_7^*`.

## Approach

### P0 poll
Single `mcp__aristotle__get_status` on `c8b8f138`. Last update at 18:00:31 still
at 12% percent_complete. CLAUDE.md prohibits re-polling within a cycle, so the
decision was made on this one observation.

### P1 strengthened submission
Took the cycle 282 submission (`.prover-state/aristotle_submissions/cycle_282/342f_recurrence.lean`)
as base and added all strategy-mandated enrichments:

1. `integral_poly_mul_iterDeriv_vanish` axiom — the cycle 277 iterated-IBP
   machinery used in (342a). Lets Aristotle pull "polynomial of degree < n is
   orthogonal to `D^n(X^n(1−X)^n)`" without re-deriving the IBP argument.
2. `integral_poly_mul_iterDeriv_XnOneSubXn_eq_zero` specialization axiom.
3. `butcherShiftedLegendre_leadingCoeff` axiom — cycle 281's
   `lc(P_n^*) = C(2n, n)`. Lets Aristotle do Step 1 (degree-comparison via the
   Pascal identity `n · C(2n, n) = 2(2n − 1) · C(2n − 2, n − 1)`) without
   reconstructing the leading-coefficient identity from Mathlib primitives.
4. Explicit small-`n` axioms extended from n=0..4 → n=0..8 (cycle 282 only
   supplied through n=4).
5. Witnessed recurrence at n=2..8 added as base-case axioms — gives Aristotle
   the option to do strong induction with seven established base steps rather
   than a direct algebraic chase.
6. Textbook proof sketch (verbatim from `extraction/formalization_data/entities/lem_342A.json`)
   quoted in the file header, with a Lean-oriented per-step re-translation
   that names the exact axioms each step relies on.

Prompt explicitly tells Aristotle to "form Q := LHS − RHS, show natDegree < n
via leadingCoeff identity, parity, orthogonality, substitute x=1" and lists
strong induction with the n=2..8 base cases as an acceptable fallback.

New project recorded as `efe4940e-0931-4fb2-8549-7eafab20d7f7`. Do not poll
until cycle 286.

### P2 n=9 ladder rung

**Pre-Lean arithmetic verification (Python integer arithmetic)**:

Coefficient table at n=9 derived from
`coeff_shiftedLegendre n k = (-1)^k · C(n,k) · C(n+k, n)`, then flipped by the
outer Butcher sign `(-1)^9 = -1`:

| k | C(9,k) | C(9+k, 9) | mathlib coeff | Butcher coeff |
|---|--------|-----------|---------------|---------------|
| 0 | 1      | 1         | +1            | −1            |
| 1 | 9      | 10        | −90           | +90           |
| 2 | 36     | 55        | +1980         | −1980         |
| 3 | 84     | 220       | −18480        | +18480        |
| 4 | 126    | 715       | +90090        | −90090        |
| 5 | 126    | 2002      | −252252       | +252252       |
| 6 | 84     | 5005      | +420420       | −420420       |
| 7 | 36     | 11440     | −411840       | +411840       |
| 8 | 9      | 24310     | +218790       | −218790       |
| 9 | 1      | 48620     | −48620        | +48620        |

`P_9^*(1) = sum of Butcher coeffs = 1` (matches (342b)).
`P_9^*(0) = -1` (matches `(-1)^9`).

Recurrence cross-check (Python): with descending-coefficient vectors
`LHS = 9 · [48620, −218790, …, 90, −1]` and
`RHS = 17·(2X−1) ⋆ P_8^* − 8 · P_7^*` (zero-padded), the two coefficient
vectors are identical:
`[−9, 810, −17820, 166320, −810810, 2270268, −3783780, 3706560, −1969110, 437580]`
(ascending order). Confirms `(2n − 1, n − 1) = (17, 8)` at n = 9.

**Lean proofs**:
- `butcherShiftedLegendre_nine`: cycle 280 odd-n template
  (`unfold; ext k; simp only [coeff_C_mul, coeff_map, coeff_shiftedLegendre];
  match k`). Ten explicit cases `k=0..9` discharged by `decide` on
  `Nat.choose` values + `norm_num`. Tail case `(k+10)` uses
  `Nat.choose_eq_zero_of_lt`.
- `butcherShiftedLegendre_recurrence_nine`: cycle 282+ template
  (`Polynomial.funext; intro x; rw [_nine, _eight, _seven]; simp [eval_*]; ring`).

## Result

**SUCCESS**

- `lake env lean OpenMath/Chapter3/Section342.lean` — exit 0
  (`real 0m11.226s`; only pre-existing linter warnings about unused simp
  args in the cycle 277 IBP helper; no errors).
- `lake build OpenMath.Chapter3.Section342` — `Build completed successfully
  (2795 jobs)`.
- `#print axioms butcherShiftedLegendre_nine` →
  `[propext, Classical.choice, Quot.sound]` ✓ (axiom-clean).
- `#print axioms butcherShiftedLegendre_recurrence_nine` →
  `[propext, Classical.choice, Quot.sound]` ✓ (axiom-clean).
- `lake env lean OpenMath/Chapter3.lean` (aggregator) — exit 0.
- Repo sorry count remains 0 (only `sorry` mentions are in cycle-history
  comments, not proof terms).

P1 Aristotle project `efe4940e-0931-4fb2-8549-7eafab20d7f7` QUEUED; first
poll deferred to cycle 286.

## Faithfulness check

### `butcherShiftedLegendre_nine`
- **Entity ID**: `lem:342A` (Butcher §342, p.236).
- **Textbook statement** (from `extraction/formalization_data/entities/lem_342A.json`,
  field `statement_latex`):
  > There exist polynomials P_n^* : [0, 1] → R, of degrees n, for
  > n = 0, 1, 2, … with the properties that … P_n^*(1) = 1, …
- **Lean statement captures**: a specific-`n` instance (n=9) of the polynomial
  `P_n^*` as the explicit expansion derived from Mathlib's
  `Polynomial.coeff_shiftedLegendre`. This is **derivative** of the lem:342A
  family, not a re-statement — the explicit form is a downstream computation,
  not a new mathematical claim. The fact that the explicit form evaluates to
  `1` at `x = 1` (sanity-checked in the docstring) cross-checks against (342b).
- **No definition smuggling**: `butcherShiftedLegendre 9` is defined globally
  by the same `C ((-1)^n) * (shiftedLegendre n).map (Int.castRingHom ℝ)` formula
  used throughout §342; this theorem proves the resulting polynomial equals
  the explicit `Polynomial.C ⟨coeff⟩ * X^k` expansion, which is a pure
  computation in `ℝ[X]`.
- **No hypothesis strengthening**: unconditional at n=9.

### `butcherShiftedLegendre_recurrence_nine`
- **Entity ID**: `lem:342A`, property (342f) at `n = 9`.
- **Textbook statement** (from same file, (342f)):
  > n P_n^*(x) = (2x − 1)(2n − 1) P_{n−1}^*(x) − (n − 1) P_{n−2}^*(x),
  >   n = 2, 3, 4, …
- **Lean statement captures**: the **same** identity, specialized to n = 9
  (i.e. `(2n − 1, n − 1) = (17, 8)`).  Same content. Polynomial-ring equality
  over `ℝ[X]`.
- **No definition smuggling**: the proof goes `funext → rw [explicit forms] →
  simp + ring`, i.e. unfolds to a pure polynomial identity in `ℝ` and lets
  `ring` close. No reformulation, no auxiliary class structure.
- **No hypothesis strengthening**: unconditional at n=9; matches the
  textbook's "n = 2, 3, 4, …" range.

## Dead ends
- None this cycle. Strategy gave a clear branching decision and both P1 and
  P2 templates were already proven viable in prior cycles (282/284/281).

## Discovery
- The Aristotle project `c8b8f138` was created at 17:14:45 on 2026-05-15, the
  same date as today. The "stalled at 12% across cycles 283/284" reflects
  multiple sub-day polls; the project never advanced past 12%. Worth noting
  for the planner: a project stuck at the initial planning percentage (12%)
  rather than mid-proof percentage is more consistent with Aristotle hitting
  an early reasoning impasse than with slow progress; the strengthening in
  P1 (adding leadingCoeff / iterated-IBP / explicit small-n forms / textbook
  proof sketch) is well-targeted for this failure mode.
- The new file `342f_recurrence_v2.lean` is ~280 LOC (vs. cycle 282's 172 LOC).
  Most of the additional length is the textbook proof sketch translation and
  the seven additional explicit small-n axioms — pure context, not new
  derivations to verify.

## Suggested next approach

For **cycle 286** the planner should:

1. **First action**: single-poll `efe4940e-0931-4fb2-8549-7eafab20d7f7`. Three
   outcomes:
   - **COMPLETE**: integrate the proof analogously to cycle 281's `d4ce527b`
     integration. Helper file `OpenMath/Chapter3/Section342RecurrenceHelpers.lean`
     under namespace `OpenMath.Chapter3.Section342Helpers`. Then ship general
     `butcherShiftedLegendre_recurrence` in `Section342.lean` and start work
     on (342g).
   - **IN_PROGRESS at low %**: ship n=10 manual ladder rung. The n=10
     coefficients can be derived from the same `coeff_shiftedLegendre` formula
     (even-n outer sign, `lc(P_10^*) = +C(20, 10) = 184756`); the cycle 280
     odd-n template handles even n with the same `decide` pattern (the
     `coeff_C ((-1)^n)` peel-off works for both signs).
   - **COMPLETE_WITH_ERRORS**: apply suggested fixes per cycle 277's pattern.

2. **If poll shows COMPLETE**: fire Aristotle on (342g) per the existing
   `.prover-state/issues/lem_342A_g_zeros_scoping.md` issue file.

3. **If poll shows another stall (third+ for this resubmission, i.e. cycles
   287/288 show no movement)**: escalate by writing an issue to
   `.prover-state/issues/` documenting that Aristotle cannot close (342f)
   under the current axiomatized setup, and consider pivoting to a manual
   multi-cycle proof using the cycle 281 leadingCoeff infrastructure as a
   starting point. The textbook proof is multi-step (degree, parity,
   orthogonality, substitution) but each step is well-known; a 3–4 cycle
   manual closure is feasible if Aristotle keeps failing.

4. **Cycle 285 leaves the ladder at n=2..9 covered.** Cycle 286 will go to
   n=10 only if P1 returns another stall.
