# Cycle 331 Strategy — §344 Phase D.11: Lobatto III `s = 2` direct-form `RKTableau`

## TL;DR

Ship **`butcherLobattoIIIDirect_two : RKTableau 2`** (the *unsuffixed*
Lobatto III variant, sixth and final small-`s` direct-form ship in the
cycle 326–330 D-ladder) inline from Butcher Table 344(I) printed values
plus a **`SatisfiesB 2`** non-vacuity example and a **`SatisfiesC 1`**
certificate. This is a single-cycle mechanical lift of cycle 329's
Radau I C(s) template; pre-flight audit and arithmetic are already done
in §B below.

Target file: `OpenMath/Chapter3/Section344.lean`, append after cycle 330's
`butcherLobattoIIICDirect_two` block (currently ending around line 2017).

## §A — Why this and why now

Cycle 330's task results recommend Option 1 (Lobatto III `s = 2`):

> Option 1: **Lobatto III `s = 2` (unsuffixed family)** — `ch03.txt:5372`
> confirms a printed table at `p = 2`; A-matrix per `ch03.txt:5221` is
> `C(s−1)` with last-column zeros. ~50 LOC mechanical ship in the same
> template. Audit outcome uncertain (last-column zero implies divergence
> from plain collocation but it's a specific variant). This would be the
> sixth direct-form ship and saturate the small-`s` Lobatto direct-form
> ladder.

Counterargument considered (option 4 — pivot to fresh entity): cycle 330
worker noted "If the small-`s` §344 ladder is approaching diminishing
returns". Decided **option 1 wins for cycle 331** because:

1. The audit-first protocol has shipped five clean classifications in a
   row (cycles 326/327/328/329/330) — saturating the small-`s` Lobatto
   family one more cycle is a small marginal cost that completes the
   data set (3 Lobatto variants at `s = 2`: IIIA shipped cycle 323
   plain-collocation, IIIC shipped cycle 330 reflection-divergent,
   Lobatto III shipped cycle 331 divergent — the last unshipped variant).
2. The recipe is purely mechanical: cycle 329's template + ~50 LOC.
3. After cycle 331 saturates the s=2 Lobatto ladder, cycle 332+ is the
   natural pivot point — the planner can pick between the formal
   collocation/printed-table bridge (cycle 330 Option 2, ~150 LOC) or a
   fresh entity (lists `def:422B`, `def:442A`, `thm:535A`, `thm:541A`).

## §B — Pre-flight audit (already complete)

### B.1 Textbook source — Butcher Table 344(I) row 5221 + printed Lobatto III `s = 2` table

From `extraction/raw_text/ch03.txt:5221`:

```
Lobatto III     Lobatto quadrature       C(s − 1), a1s = a2s = · · · = ass = 0
```

From `extraction/raw_text/ch03.txt:5372-5378`:

```
Lobatto III    (s = 2, p = 2),
                                                0       0       0
                                                1       1       0
                                                        1       1
                                                        2       2
```

Reading the layout: row 0 has `c_0 = 0`, then `A_{00} = 0`, `A_{01} = 0`.
Row 1 has `c_1 = 1`, then `A_{10} = 1`, `A_{11} = 0`. Bottom row is
`b = (1/2, 1/2)`. So:

- `c = ![0, 1]` (Lobatto abscissae at `s = 2`).
- `b = ![1/2, 1/2]` (Lobatto weights at `s = 2`; same as Lobatto IIIA,
  IIIC).
- `A = !![0, 0; 1, 0]` (last-column-zero property: `a_{i,1} = 0` for
  `i ∈ {0, 1}` — the defining feature of the Lobatto III family).

### B.2 Divergence audit vs plain Lagrange collocation

Plain collocation at `c = (0, 1)`:

- `L_0(x) = (x − 1)/(0 − 1) = 1 − x`.
- `L_1(x) = (x − 0)/(1 − 0) = x`.
- `A_{00} = ∫₀^0 L_0(x) dx = 0`.
- `A_{01} = ∫₀^0 L_1(x) dx = 0`.
- `A_{10} = ∫₀^1 (1 − x) dx = 1/2`.
- `A_{11} = ∫₀^1 x dx = 1/2`.

Plain collocation gives **`A = !![0, 0; 1/2, 1/2]`** (= Lobatto IIIA,
cycle 323), but Butcher's Lobatto III table gives **`A = !![0, 0; 1, 0]`**.
Row 0 coincides (both vacuous since `c_0 = 0`); row 1 diverges entry-for-entry.

**Audit outcome: divergent.** This is the *sixth divergent classification*
out of seven small-`s` D-ladder audits (cycles 326 Radau IA, 327 Lobatto
IIIB s=3, 328 Radau II D(s), 330 Lobatto IIIC, 331 Lobatto III divergent;
only cycle 329 Radau I C(s) coincides). The pattern is now fully
established: only the C(s) collocation-matrix variants of the
plain-quadrature families (Radau I, Lobatto IIIA) coincide with plain
collocation; all reflection-style and D(s)-style and C(s−1)-style variants
diverge.

### B.3 `SatisfiesB 2` arithmetic verification

`SatisfiesB k`: `∀ k', 1 ≤ k' → k' ≤ k → ∑ⱼ bⱼ · cⱼ^(k'−1) = 1/k'`.

For `k = 2`:

- `k' = 1`: `(1/2)·1 + (1/2)·1 = 1 = 1/1` ✓
- `k' = 2`: `(1/2)·0 + (1/2)·1 = 1/2 = 1/2` ✓

`SatisfiesB 3` would FAIL (matching the printed `p = 2`): `k' = 3`:
`(1/2)·0 + (1/2)·1 = 1/2 ≠ 1/3`. So `SatisfiesB 2` is the **maximal**
quadrature certificate, matching Butcher's `p = 2`.

### B.4 `SatisfiesC 1` arithmetic verification

`SatisfiesC k`: `∀ i, ∀ k', 1 ≤ k' → k' ≤ k → ∑ⱼ Aᵢⱼ · cⱼ^(k'−1) = cᵢ^k' / k'`.

For `k = 1` (the family's defining `C(s−1) = C(1)` certificate):

- `(i=0, k'=1)`: `0·1 + 0·1 = 0 = 0^1/1` ✓
- `(i=1, k'=1)`: `1·1 + 0·1 = 1 = 1^1/1` ✓

So `SatisfiesC 1` holds. `SatisfiesC 2` would FAIL (this is why the
printed order is only `p = 2`): `(i=1, k'=2)`: `1·0 + 0·1 = 0 ≠ 1²/2 = 1/2`.

Thus the cycle 331 certificate set is:
- `SatisfiesB 2` (order-2 quadrature, maximal — same bar as cycles 326/327/330).
- `SatisfiesC 1` (the `C(s−1)` family-defining property — analogous to
  cycle 329's `SatisfiesC 2` for the C(s) variant of Radau I).

## §C — Concrete deliverables

Append after `butcherLobattoIIICDirect_two`'s `SatisfiesB 2` example
(currently the last block, ending around line 2017 of `Section344.lean`).

### C.1 Section header (~25 LOC docstring)

```lean
/-! ## Deliverable D.11 — Small-`s` RKTableau (Lobatto III, `s = 2`)

Cycle 331. Per Butcher Table 344(I) (`ch03.txt:5221`), the *unsuffixed*
Lobatto III family's `A`-matrix is *"C(s − 1), a1s = a2s = · · · = ass = 0"*
— i.e. it satisfies the C(s − 1) simplifying assumption (so row sums
equal the abscissae) AND has zero last column. At `s = 2`, C(s − 1) =
C(1) just says row sums equal `c`, and the last-column-zero condition
forces `A` to have its second column identically zero.

The cycle 331 §B audit confirmed that plain Lagrange collocation at
the Lobatto abscissae `(0, 1)` yields rows `(0, 0)` and `(1/2, 1/2)`
(= the Lobatto IIIA tableau, cycle 323), but Butcher's printed
Lobatto III `s = 2` table (p. 226, `ch03.txt:5372-5378`) gives rows
`(0, 0)` and `(1, 0)`. Row 0 coincides (vacuous: `c_0 = 0`); row 1
diverges entry-for-entry. So Lobatto III differs from plain Lagrange
collocation — *sixth divergent classification* in the cycle 326–331
audit ladder; only Radau I C(s) (cycle 329) and Lobatto IIIA (cycle 323,
matched by construction) coincide with plain collocation.

This cycle ships the printed values inline plus `SatisfiesB 2`
(the maximal quadrature certificate; matches Butcher's printed `p = 2`)
and `SatisfiesC 1` (the family-defining `C(s − 1)` certificate). The
formal collocation/printed-table bridge for the C(s) variants
(Radau I + Lobatto IIIA) is deferred to a future cycle. -/
```

### C.2 Definition (~10 LOC)

```lean
/-- **Butcher §344 — Lobatto III `s = 2` tableau (unsuffixed family,
`C(s − 1)` + last-column-zero variant)** declared inline from Butcher's
printed Table 344(I), p. 226 (`extraction/raw_text/ch03.txt:5372-5378`):
`c = (0, 1)`, `b = (1/2, 1/2)`, `A = !![0, 0; 1, 0]`. This is the
classical two-stage Lobatto III method (Butcher's `Choice of A = C(s − 1),
a1s = a2s = · · · = ass = 0` row of Table 344(I)), with printed order
`p = 2`.

The `b` and `c` agree with `butcherLobattoIIIA_two` (cycle 323) and
`butcherLobattoIIICDirect_two` (cycle 330) — all three share the
Lobatto `(0, 1)` abscissae and the trapezoidal `(1/2, 1/2)` weights.
(Lobatto IIIB at `s = 2` does not exist — Butcher line 5263.)

The A-matrix has zero second column (the family-defining
last-column-zero property: `A_{ij} = 0` for `j = s − 1 = 1`). At
`s = 2`, the row-sums-equal-c condition (C(s − 1) = C(1)) plus the
last-column-zero condition uniquely determines the matrix:
`A_{00} = 0` (forced by `c_0 = 0`), `A_{01} = 0` (last column zero),
`A_{10} = 1` (forced by `c_1 = 1` and `A_{11} = 0`), `A_{11} = 0`
(last column zero). -/
noncomputable def butcherLobattoIIIDirect_two :
    OpenMath.Chapter3.Section312.RKTableau 2 where
  A := !![0, 0; 1, 0]
  b := ![1/2, 1/2]
  c := ![0, 1]
```

### C.3 `SatisfiesB 2` example (~10 LOC)

```lean
/-- **Non-vacuity (B(2))**: the direct Lobatto III `s = 2` tableau
satisfies the order-2 quadrature condition `B(2)` (Lobatto III at
`s = 2` has classical order `p = 2`). Arithmetic:
`∑ⱼ bⱼ · cⱼ^0 = 1/2 + 1/2 = 1 = 1/1`,
`∑ⱼ bⱼ · cⱼ^1 = (1/2)·0 + (1/2)·1 = 1/2 = 1/2`. -/
example : butcherLobattoIIIDirect_two.SatisfiesB 2 := by
  intro k h1 hk
  interval_cases k
  · simp [butcherLobattoIIIDirect_two, Fin.sum_univ_two]; norm_num
  · simp [butcherLobattoIIIDirect_two, Fin.sum_univ_two]
```

Per cycle 330's discovery, the `k = 2` arm may close by `simp` alone
without trailing `norm_num` because `c i ^ 1 = c i` reduces the goal
to `1/2 * 0 + 1/2 * 1 = 1/2` which simp's arithmetic handles directly.
If `lake env lean` complains "No goals to be solved" at any trailing
`norm_num`, drop it from that arm. Conversely if `simp` leaves a
residue like `½ + ½ = 1/1` on `k = 1`, the `norm_num` is needed.
Match the cycle 330 pattern: separate bullets per arm, `norm_num`
selectively.

### C.4 `SatisfiesC 1` example (~10 LOC)

```lean
/-- **Non-vacuity (C(1))** — the certificate that characterises this
tableau as the C(s − 1) variant of Lobatto III: the direct Lobatto III
`s = 2` tableau satisfies the order-1 collocation simplifying assumption
`C(1)`, namely `∑ⱼ Aᵢⱼ · cⱼ^(k-1) = cᵢ^k / k` for `i ∈ {0, 1}` and
`k = 1`.

Arithmetic checks:
- `(i=0, k=1)`: `0·1 + 0·1 = 0 = 0^1/1`.
- `(i=1, k=1)`: `1·1 + 0·1 = 1 = 1^1/1`. -/
example : butcherLobattoIIIDirect_two.SatisfiesC 1 := by
  intro i k h1 hk
  fin_cases i <;> interval_cases k <;>
    simp [butcherLobattoIIIDirect_two, Fin.sum_univ_two] <;> norm_num
```

If the trailing `<;> norm_num` emits an `unnecessarySeqFocus` warning
(because all arms close by simp alone for `k = 1` — `c_i ^ 0 = 1`
trivially), replace with `fin_cases i <;> interval_cases k <;> simp
[butcherLobattoIIIDirect_two, Fin.sum_univ_two]` (drop `norm_num`).
Per cycle 329's `SatisfiesC 2` ship, the four-arm chain WAS warning-clean
— but cycle 329 had non-trivial fractional arithmetic in some arms;
the cycle 331 C(1) chain has only `0 = 0` and `1 = 1` arithmetic so
`norm_num` may be vacuous. Verify and adapt to whichever clears
without warnings.

## §D — Verification protocol

1. `lake env lean OpenMath/Chapter3/Section344.lean` — must exit
   silently (no warnings, no errors).
2. `lake env lean OpenMath/Chapter3.lean` — must build the aggregator
   to confirm no downstream regression.
3. `grep -c sorry OpenMath/Chapter3/Section344.lean` — must remain `0`.
4. `#print axioms OpenMath.Chapter3.Section344.butcherLobattoIIIDirect_two`
   — expected `[Quot.sound]` only (definition, no propositional content).
5. Spot-check `#print axioms` on the `SatisfiesB 2` and `SatisfiesC 1`
   example bodies. Since anonymous `example`s aren't named, use the
   `lean_verify` MCP tool on the symbol directly, OR promote the
   examples to named theorems (e.g.
   `butcherLobattoIIIDirect_two_satisfiesB_two`,
   `_satisfiesC_one`) and `#print axioms` them — expected
   `[propext, Classical.choice, Quot.sound]`. Naming is preferred for
   downstream citation hygiene; do it if the cycle budget allows.

If any of these fails, see §F below for fallbacks.

## §E — Tautology scanner mitigation

The cycle 330 ship was scanner-clean. The cycle 331 deliverables use
the same tactical patterns (`simp [...]; norm_num` and `fin_cases +
interval_cases + simp + norm_num` chains, no `:= h_*` / `exact h_*`
closers, no `:= id` closers). Expected scanner-clean.

If a false positive appears, remediate per the cycle 060+ template:
inline the offending line into a parent expression rather than naming
it `h_*`. See `.prover-state/issues/tautology_scanner_false_positives.md`.

## §F — Fallback plan

If the §C ship hits unexpected friction:

- **F.1**: `simp` arithmetic mismatch on a `SatisfiesB 2` arm (e.g.
  the `k = 1` arm leaves `½ + ½ = 1/1` while `½ + ½ = 1` is what
  simp emits). Add explicit `show (1 : ℝ) = 1 / 1; norm_num`
  reframing, or just keep the trailing `norm_num` which handles
  `1 = 1/1` directly.
- **F.2**: `simp` over-reduces `c i ^ 0` to `1` but leaves `½ * 1 +
  ½ * 1` rather than closing. Append `<;> norm_num` or `<;> ring`.
- **F.3**: `interval_cases k` fails to terminate on the empty case
  (`k = 0`) — should be impossible since `h1 : 1 ≤ k` excludes it,
  but if it does, replace with `match k, h1, hk with | 1, _, _ => ...
  | 2, _, _ => ...`.
- **F.4** (graceful degradation): if `SatisfiesC 1` proves
  unexpectedly hard, ship only `SatisfiesB 2` (matching cycle 326/327/330
  reflection-variant precedent) and defer the C(1) certificate.
  Document the deferral in the task results. The cycle still ships a
  valid direct-form `RKTableau` with `B(p)` non-vacuity.
- **F.5** (abort): if the `noncomputable def` itself fails to
  elaborate (e.g. universe mismatch on the `RKTableau` record), check
  for stale `.olean` cache via `rm OpenMath/Chapter3/Section344.olean
  && lake build OpenMath.Chapter3.Section344`. If still failing, split
  the deliverable into a new file `Section344LobattoIII.lean` imported
  by `Chapter3.lean` directly.

## §G — What NOT to attempt

1. **Do NOT attempt a collocation bridge / formal lift** between
   `butcherLobattoIIIDirect_two` and any constructed
   `butcherLobattoIII_collocationA_two`. The Lobatto III A-matrix
   DOES NOT come from plain Lagrange collocation (audit §B.2 confirmed
   divergence), so no such bridge exists. The formal collocation/printed-
   table bridge is reserved for cycle 332+ on the C(s) variants where
   coincidence holds (Radau I, Lobatto IIIA).
2. **Do NOT add a `SatisfiesD 2` or `SatisfiesE 1 1` certificate**.
   The family-defining certificate is C(s − 1) = C(1). D(s) is the
   defining certificate of *Lobatto IIIB*, not Lobatto III. Adding the
   wrong certificate is a definition-smuggling risk.
3. **Do NOT extend to `Lobatto III s = 3`** in this cycle. Cycle 330
   task results lists `butcherRadauIDirect_three` as multi-cycle
   (`√6` arithmetic) and the same caveat applies — at `s = 3` the
   Lobatto abscissae become `(0, 1/2, 1)` (rational, easier) but
   the A-matrix entries from Butcher Table 344(III) at `s = 3` are
   a 9-entry direct-form ship + 6 `SatisfiesC 2` arms; it's a separate
   cycle.
4. **Do NOT submit this to Aristotle**. It's pure mechanical lift;
   manual ship + verify is the fastest path.
5. **Do NOT modify cycle 323's `butcherLobattoIIIA_two`** to add a
   cross-reference. Cross-references in docstrings are fine but no
   structural changes — keep the diff to "append after cycle 330's
   Lobatto IIIC block".
6. **Do NOT touch GPFS-blocked Chapter 4 §441** — 43+ consecutive
   timeouts. Skip per `.prover-state/issues/cycle_182_gpfs_slowness.md`.
7. **Do NOT raise `maxHeartbeats`**. The deliverable is a 4-arm
   `simp + norm_num` chain — well under default limits.
8. **Do NOT try alternate A-matrix forms** like `!![0, 0; 1/2, 1/2]`
   (= Lobatto IIIA) or `!![1, 0; 0, 0]` to "fix" the divergence. The
   printed Butcher values are authoritative; ship them verbatim.

## §H — Post-ship updates

After verification passes:

1. **Update `plan.md`**:
   - In the §344 `thm:344A` row, append a cycle 331 sentence noting
     the Phase D.11 ship (`butcherLobattoIIIDirect_two` + `SatisfiesB 2`
     + `SatisfiesC 1`, axiom-clean). Increment the LOC tally
     `Section344.lean LOC 2017 → ~2070 (+~55)`.
2. **`lean_status.json`**: `thm:344A` row remains `partial` (the full
   §344 thm is still pending Phase B.2 + Phase C.2+); no entity-row
   change. Bump `last_cycle` field on `thm:344A` to 331 if such a
   field is tracked.
3. **Write `.prover-state/task_results/cycle_331.md`** per the CLAUDE.md
   template, documenting:
   - Worked on: §344 Phase D.11 (Lobatto III `s = 2`).
   - Approach: mechanical lift of cycle 329 C(s) template, with
     `SatisfiesC 1` (not `C 2`) per the C(s − 1) family rubric.
   - Result: SUCCESS, three new public symbols (def + two examples,
     all axiom-clean).
   - Faithfulness check: §B above, no divergences.
   - Discovery: audit ladder pattern now saturated at s=2 Lobatto
     family (IIIA cycle 323 plain-coincident, IIIC cycle 330 reflection-
     divergent, III cycle 331 C(s−1)-divergent). Six-for-seven divergent
     classifications in the cycle 326–331 D-ladder; only Radau I C(s)
     (cycle 329) coincides with plain collocation. Pattern: "C(s)
     variants of plain-quadrature families coincide; everything else
     diverges."
   - Suggested next: cycle 332 planner has clean pivot points. Three
     ranked options:
     1. **Pivot to a fresh entity** (RECOMMENDED): with the small-`s`
        D-ladder saturated, cycle 332 is the natural pivot point.
        Candidates from `plan.md`: `def:422B` (underlying one-step
        method LMM, definition-only), `def:442A` (principal sheet,
        definition-only), `thm:535A` (underlying one-step method GLM,
        per JSON likely 2-3 cycles), `thm:541A` (DIMSIM types,
        scoping doc).
     2. **Formal collocation/printed-table bridge for Radau I `s = 2`**
        (cycle 330 Option 2, ~150 LOC) — first non-trivial step
        beyond mechanical lifts within §344.
     3. **Continue ladder** to `butcherLobattoIII_three` (~150 LOC,
        9-entry A-matrix at `s = 3` requires extending the template
        to `Fin.sum_univ_three` arms in the C(2) certificate).
4. **Do NOT modify `Chapter3.lean` aggregator** — Section344 is
   already imported.

## §I — Estimated LOC budget

| Component                          | Estimated LOC |
|------------------------------------|---------------|
| Section header docstring (C.1)     | ~25           |
| Definition (C.2)                   | ~10           |
| `SatisfiesB 2` example (C.3)       | ~10           |
| `SatisfiesC 1` example (C.4)       | ~10           |
| **Total**                          | **~55**       |

Within the ~50 LOC target from cycle 330 task results.

## §J — Cross-references

- `OpenMath/Chapter3/Section344.lean:1920-1955` — cycle 329 Radau I
  `s = 2` C(s) variant (template for the C(k) certificate; cycle 329
  shipped C(2), cycle 331 ships C(1)).
- `OpenMath/Chapter3/Section344.lean:1993-2017` — cycle 330 Lobatto IIIC
  `s = 2` (template for the B(p) example structure).
- `OpenMath/Chapter3/Section344.lean:1786-1805` — cycle 327 Lobatto IIIB
  `s = 3` (template for direct-form deliverable structure).
- `extraction/raw_text/ch03.txt:5221` — Butcher Table 344(I) Lobatto III
  family row.
- `extraction/raw_text/ch03.txt:5372-5378` — Butcher printed Lobatto III
  `s = 2` table.
- `.prover-state/issues/radau_ia_collocation_divergence.md` — broader
  precedent for divergence-from-plain-collocation audits.
- `.prover-state/task_results/cycle_330.md` — cycle 330 task results
  with the Option 1 recommendation.
- `.prover-state/issues/tautology_scanner_false_positives.md` — scanner
  bug reference (no mitigation needed this cycle; expected scanner-clean).
- `.prover-state/issues/cycle_182_gpfs_slowness.md` — §441 GPFS block
  reference (do not touch).
