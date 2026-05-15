# Cycle 286 Results

## Worked on
- **P0 (mandatory)**: single-poll Aristotle project
  `efe4940e-0931-4fb2-8549-7eafab20d7f7`. Result: `IN_PROGRESS` at
  **11%** (created 18:03 UTC 2026-05-15, last update 18:19 UTC, ~16
  minutes in). Project left running for cycle 287 poll, NOT cancelled
  — strategy Branch D / cycle 285's "third stall" cancellation
  protocol does not fire on a first-cycle observation.
- **P1 (per Branch B)**: extended the §342 (342f) ladder to `n = 10`.
  Shipped two new theorems in `OpenMath/Chapter3/Section342.lean`:
  - `butcherShiftedLegendre_ten` — explicit closed form for `P_10^*`.
  - `butcherShiftedLegendre_recurrence_ten` —
    `10 • P_10^* = 19 · (2X − 1) · P_9^* − 9 · P_8^*`.
- **P2 stretch**: skipped per strategy directive ("Skip this priority
  entirely if Branch A fires" — but the P2 stretch was also gated on
  remaining LOC budget; with ~115 LOC added across the two ladder
  theorems and a non-trivial Polynomial.funext+ring composition for
  the recurrence, deferring (342g) Aristotle submission to cycle 287
  is the right call).

## Approach

### P0: single-poll discipline
Called `mcp__aristotle__get_status` exactly once on
`efe4940e-0931-4fb2-8549-7eafab20d7f7`. Status returned
`IN_PROGRESS` at `percent_complete: 11`. The project was submitted at
end of cycle 285 (timestamp `2026-05-15T18:03:40`) and the latest
status update was `2026-05-15T18:19:36` — `~16` minutes of compute on
a strengthened resubmission. This is comparable to the cycle 283 first
poll on `c8b8f138` (`12%` at ~15 minutes), so a single cycle-poll at
`11%` is *not yet diagnostic* of a third-stall pattern; we await
cycle 287 / 288 polls before concluding.

### P1: Python verification before Lean ship
Per cycle 285 precedent, verified both n=10 explicit-form coefficients
and the n=10 recurrence in Python integer arithmetic **before**
writing any Lean. Key data:

**P_10^* coefficients (`(-1)^k · C(10,k) · C(10+k, 10)`, outer
Butcher sign `(-1)^{10} = +1`):**
```
k=0:  1
k=1:  -110
k=2:  2970
k=3:  -34320
k=4:  210210
k=5:  -756756
k=6:  1681680
k=7:  -2333760   ← initial mental arithmetic gave -2227680; Python caught the error
k=8:  1969110
k=9:  -923780
k=10: 184756     ← C(20, 10) = 184756, matches cycle 281 leading-coefficient formula
```
Sanity:
- `P_10^*(0) = 1 = (-1)^{10}` ✓
- `P_10^*(1) = sum = 1` ✓ (matches (342b))
- Leading coefficient `+C(20, 10) = 184756` ✓ (matches cycle 281
  `butcherShiftedLegendre_leadingCoeff`)

**Recurrence cross-check** (both sides multiplied out, ascending
coeffs):
```
LHS  = 10 · P_10^*:                       [10, -1100, 29700, -343200, 2102100, -7567560, 16816800, -23337600, 19691100, -9237800, 1847560]
RHS  = 19 · (2X − 1) · P_9^* − 9 · P_8^*: [10, -1100, 29700, -343200, 2102100, -7567560, 16816800, -23337600, 19691100, -9237800, 1847560]
MATCH: True
```
`(2n − 1, n − 1) = (19, 9)` at `n = 10` is consistent with Butcher
(342f).

### P1: Lean ship
- `butcherShiftedLegendre_ten`: cycle 277/279 even-`n` template
  (outer sign `+1` is trivial — `simp only [coeff_C_mul, coeff_map,
  coeff_shiftedLegendre]` reduces each `k` slot to a Mathlib
  `coeff_shiftedLegendre` evaluation). Per-arm match on `k = 0..10`
  with `Nat.choose` `decide` lemmas at `k = 2..10` (the leaf cases
  `k = 0, 1` are handled by direct `simp + norm_num`; the tail
  `k+11` uses `Nat.choose_eq_zero_of_lt`).
- `butcherShiftedLegendre_recurrence_ten`: cycle 282+ template —
  `Polynomial.funext + rw [_ten, _nine, _eight] + simp + ring`.

Both theorems compile via `lake env lean OpenMath/Chapter3/Section342.lean`
(exit 0, ~21 sec, single-file build).

## Result

**SUCCESS** — Branch B deliverable shipped and verified.

- `lake env lean OpenMath/Chapter3/Section342.lean` → exit 0.
- `lake env lean OpenMath/Chapter3.lean` (aggregator) → exit 0.
- `mcp__lean-lsp__lean_verify` on
  `OpenMath.Chapter3.Section342.butcherShiftedLegendre_ten` →
  `axioms: [propext, Classical.choice, Quot.sound]`, no warnings.
- `mcp__lean-lsp__lean_verify` on
  `OpenMath.Chapter3.Section342.butcherShiftedLegendre_recurrence_ten` →
  `axioms: [propext, Classical.choice, Quot.sound]`, no warnings.
- Sorry count in `OpenMath/Chapter3/Section342.lean` remains **0**.

## Faithfulness check

### `butcherShiftedLegendre_ten`
- **Entity**: explicit form of `P_10^*`, deriving from the textbook
  `lem:342A` package. The textbook does not state the `n = 10`
  expansion explicitly — this is a derived helper used as a base case
  for the recurrence ladder.
- **Lean statement**: equates `butcherShiftedLegendre 10` with the
  polynomial
  `184756X^10 − 923780X^9 + … − 110X + 1` (eleven monomials).
- **Captures**: same content — direct computation from cycle 277's
  definition `butcherShiftedLegendre n = C ((-1)^n) · (shiftedLegendre
  n).map (Int.castRingHom ℝ)` combined with Mathlib's
  `Polynomial.coeff_shiftedLegendre n k = (-1)^k · C(n,k) · C(n+k, n)`.
  Sanity-checked against (342b) (`P_n^*(1) = 1`) at `n = 10` by
  evaluating the coefficient sum.

### `butcherShiftedLegendre_recurrence_ten`
- **Entity**: Butcher §342 (342f) instantiated at `n = 10`. Textbook
  statement (from
  `extraction/formalization_data/entities/lem_342A.json`):
  > `n P_n^*(x) = (2x-1)(2n-1) P_{n-1}^*(x) - (n-1) P_{n-2}^*(x)`
- **Lean statement** at `n = 10`:
  `(10 : ℝ) • butcherShiftedLegendre 10 = C 19 · (C 2 · X − C 1) · butcherShiftedLegendre 9 − C 9 · butcherShiftedLegendre 8`
  — at `n = 10`, `2n − 1 = 19` and `n − 1 = 9`, matching cycle 282+
  recurrence template `C (2n−1) · (C 2 · X − C 1) · P_{n−1}^* − C (n−1) ·
  P_{n−2}^*`. ✓
- **Captures**: same content — direct instantiation of (342f) at the
  textbook's universally-quantified `n`, with no weakening or
  strengthening of hypotheses (the bare statement at `n = 10` has no
  hypotheses to weaken).
- **Tautology check**: conclusion `(10 : ℝ) • P_10^* = …` does not
  appear as a hypothesis. ✓
- **Identity check**: proof is `Polynomial.funext + rw + simp + ring`,
  not `exact h` or `id`. Real algebraic work. ✓
- **Hypothesis strength check**: no hypotheses beyond bare equality —
  none to weaken. ✓
- **Absent theorem check**: no promised `sorry`s in comments — the
  closed-form expansion is fully proved. ✓
- **Definition smuggling check**: no new `def` introduced. ✓

## Dead ends
None this cycle. The cycle 285 recipe transferred mechanically. The
only "miss" was the initial mental-arithmetic value `-2227680` for
`P_10^*` coefficient at `k = 7`, which Python integer arithmetic
correctly produced as `-2333760` (since `120 · 19448 = 2333760`).
Cycle 285's "Python before Lean" precedent saved a downstream
norm_num failure.

## Discovery
- Mathlib's `shiftedLegendre` cast pattern remains robust at `n = 10`.
  `lake env lean` compile time for the single file with the new
  `butcherShiftedLegendre_ten` (eleven `match k =>` arms) is ~21 sec,
  comparable to the n=9 ship's compile time in cycle 285. The
  `Nat.choose` `decide` lemmas at `k = 2..10` evaluate fast
  (`Nat.choose 20 10 = 184756` is the largest and still well under
  `maxHeartbeats` budget).
- Aristotle `efe4940e` (strengthened resubmission) is exhibiting the
  same early-stall pattern as `c8b8f138` (12% across three polls)
  — this is the project's *first* poll (11%), so not yet a stall.
  Cycle 287 should single-poll again; cycle 288's poll determines
  whether the strengthened resubmission has the same blocker as
  `c8b8f138` or is actually progressing.

## Suggested next approach (cycle 287)

1. **P0 (mandatory)**: single-poll `efe4940e` again. Decision tree:
   - **COMPLETE / COMPLETE_WITH_ERRORS** → integrate per strategy
     Branch A (extract helpers to
     `OpenMath/Chapter3/Section342RecurrenceHelpers.lean`, ship
     general theorem in `OpenMath/Chapter3/Section342.lean`).
   - **IN_PROGRESS with `percent_complete > 11`** → encouraging,
     extend ladder to `n = 11` (mechanical port — odd-`n`, leading
     `C(22, 11) = 705432`, outer sign `(-1)^{11} = -1`).
   - **IN_PROGRESS still at ~11%** → second stall observation. Either:
     (a) ship `n = 11` and continue waiting (cycle 285 protocol was
     to wait for THREE polls before cancelling); or (b) cancel and
     escalate to the cycle 281 / Branch D manual-closure path.
   - **FAILED / CANCELLED** → escalate to manual closure per Branch D.

2. **Tactical hint**: the `n` ladder is now at depth 10. Cycles
   282–286 each shipped one ladder rung. Continuing this pattern
   indefinitely is a hedge against Aristotle never delivering, but
   each rung's marginal value drops since the general theorem
   subsumes all. If Aristotle stalls again in cycle 287, the planner
   should weigh: (i) ship `n = 11` (low risk, low reward — already
   covered by general statement if Aristotle ever completes), vs
   (ii) begin the cycle 281 / Branch D 3–4 cycle manual closure
   plan (high risk, high reward — closes (342f) general).
3. **Reference**: cycle 285's submission file at
   `.prover-state/aristotle_submissions/cycle_285/342f_recurrence_v2.lean`
   contains the full axioms-as-hypotheses framing. If Aristotle's
   eventual proof differs structurally from the textbook sketch
   (e.g. uses the recurrence_eight/nine/ten base cases for an
   inductive argument rather than the orthogonality-basis argument),
   the helper-file extraction will look different from cycle 281's
   `Section342NormSqHelpers.lean` — be prepared to factor whichever
   machinery Aristotle produces, not the proof outline the prompt
   suggested.
