# Cycle 331 Results

## Worked on
§344 Phase D.11: ship `butcherLobattoIIIDirect_two : RKTableau 2`
(the *unsuffixed* Lobatto III variant, sixth and final small-`s`
direct-form ship in the cycle 326–331 D-ladder) inline from Butcher
Table 344(I) printed values, plus a `SatisfiesB 2` non-vacuity
example and a `SatisfiesC 1` certificate.

## Approach

Mechanical lift of cycle 329's Radau I C(s) template into the
`C(s − 1) = C(1)` regime appropriate for Lobatto III. Appended to
`OpenMath/Chapter3/Section344.lean` after cycle 330's
`butcherLobattoIIICDirect_two` block:

1. Section-header docstring (D.11) summarising the C(s − 1)
   + last-column-zero recipe per Butcher Table 344(I) and the §B
   audit outcome.
2. `noncomputable def butcherLobattoIIIDirect_two` with
   `A := !![0, 0; 1, 0]`, `b := ![1/2, 1/2]`, `c := ![0, 1]`.
3. `SatisfiesB 2` example: two-arm `interval_cases k; simp; norm_num` /
   `simp` close, matching the cycle 330 Lobatto IIIC pattern where
   `k = 1` needs `norm_num` for `½ + ½ = 1/1` and `k = 2` closes by
   `simp` alone since `c i ^ 1 = c i` reduces to a direct
   half-arithmetic equality.
4. `SatisfiesC 1` example: four-arm `fin_cases i <;> interval_cases k
   <;> simp [_, Fin.sum_univ_two]` close — no trailing `norm_num`
   needed since all four arms collapse to `0 = 0` or `1 = 1`
   identities (as predicted in the strategy §C.4).

## Result

SUCCESS — all three new public symbols compile and are axiom-clean.

- `lake env lean OpenMath/Chapter3/Section344.lean`: exits silently (no
  warnings, no errors).
- `lake env lean OpenMath/Chapter3.lean` (aggregator): clean rebuild.
- `lake build OpenMath.Chapter3.Section344`: succeeds (only pre-existing
  Section342 lint warnings).
- `grep -c sorry OpenMath/Chapter3/Section344.lean`: `0` (unchanged).
- `#print axioms OpenMath.Chapter3.Section344.butcherLobattoIIIDirect_two`:
  `[propext, Classical.choice, Quot.sound]` — axiom-clean.
- Section344.lean LOC: 2017 → 2093 (+76, within the ~55 LOC strategy
  estimate after counting docstring narrative).

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `def butcherLobattoIIIDirect_two : RKTableau 2`

Entity ID: `thm:344A` (Phase D.11 deliverable; small-`s` `RKTableau`
construction for the Lobatto III family, supporting the §344 anchor).
Source: Butcher Table 344(I) recipe row at
`extraction/raw_text/ch03.txt:5221`:

> Lobatto III     Lobatto quadrature       C(s − 1), a1s = a2s = · · · = ass = 0

Printed values at `extraction/raw_text/ch03.txt:5372-5378`:

> Lobatto III    (s = 2, p = 2),
>                                                 0       0       0
>                                                 1       1       0
>                                                         1       1
>                                                         2       2

(Row 0: `c_0 = 0`, then `A_{00} = 0`, `A_{01} = 0`. Row 1: `c_1 = 1`,
then `A_{10} = 1`, `A_{11} = 0`. Bottom row: `b = (1/2, 1/2)`.)

Lean statement: `A = !![0, 0; 1, 0]`, `b = ![1/2, 1/2]`, `c = ![0, 1]`.
**Captures: same content** — direct entry-for-entry transcription of
Butcher's printed table.

### `example : butcherLobattoIIIDirect_two.SatisfiesB 2`

Cycle 331 §B.3 arithmetic verification:
- `k = 1`: `(1/2)·1 + (1/2)·1 = 1 = 1/1` ✓
- `k = 2`: `(1/2)·0 + (1/2)·1 = 1/2 = 1/2` ✓

`SatisfiesB 3` would fail (`(1/2)·0 + (1/2)·1 = 1/2 ≠ 1/3`),
matching Butcher's printed `p = 2`. **Captures: same content** — the
maximal `B(p)` non-vacuity bar for this tableau, mirroring cycle
326/327/330 reflection-variant precedent.

### `example : butcherLobattoIIIDirect_two.SatisfiesC 1`

Cycle 331 §B.4 arithmetic verification:
- `(i=0, k=1)`: `0·1 + 0·1 = 0 = 0^1/1` ✓
- `(i=1, k=1)`: `1·1 + 0·1 = 1 = 1^1/1` ✓

`SatisfiesC 2` would fail at `(i=1, k=2)`: `1·0 + 0·1 = 0 ≠ 1^2/2 =
1/2`, matching the Lobatto III table-row classification (only
`C(s − 1) = C(1)` is claimed, not `C(s)`). **Captures: same content** —
the family-defining `C(s − 1)` certificate for the unsuffixed Lobatto
III variant, analogous to cycle 329's `SatisfiesC 2` certificate for
the Radau I C(s) variant.

No divergences from textbook; no hypothesis strengthening or weakening.

### Pre-commit checklist

- TAUTOLOGY CHECK: ✓ no theorem conclusion appears verbatim as a
  hypothesis (the two `SatisfiesB`/`SatisfiesC` examples have
  no premises beyond the `RKTableau` record).
- IDENTITY CHECK: ✓ no proof is `exact h` / `:= h_*` / `:= id`. All
  proofs use `interval_cases`/`fin_cases` + `simp` + (selective)
  `norm_num`.
- DEFINITION SMUGGLING CHECK: ✓ `butcherLobattoIIIDirect_two` is a
  data-only `noncomputable def` of an `RKTableau` record (`A, b, c`);
  no `Prop` fields. The `SatisfiesB 2` and `SatisfiesC 1` properties
  are stated as separate `example` theorems, not encoded into the
  structure.
- HYPOTHESIS STRENGTH CHECK: ✓ the `B(2)` and `C(1)` certificates
  are maximal for this tableau (B(3) and C(2) both fail by §B
  arithmetic). No room to weaken.

## Dead ends

None. The strategy's pre-flight audit (§B) eliminated all guesswork
and the mechanical lift compiled on the first attempt without
adjustment. The fallbacks listed in §F (`norm_num` needed/not needed
per arm, `simp` over-reduction, etc.) all aligned with cycle 330's
template pattern; no fallbacks required.

## Discovery

- **Audit-first ladder is saturated at the small-`s` Lobatto family.**
  Three Lobatto variants now exist at `s = 2`:
  * Lobatto IIIA (cycle 323, plain-collocation coincident, by
    construction);
  * Lobatto IIIC (cycle 330, "reflections of Lobatto III" divergent);
  * Lobatto III (cycle 331, `C(s − 1) + last-column-zero` divergent).
  Lobatto IIIB at `s = 2` does not exist (Butcher line 5263).

- **Six-for-seven divergent audit outcomes** in the cycle 326–331
  D-ladder. The pattern is now fully empirically established:
  * Only the C(s) variants of plain-quadrature families (Radau I,
    Lobatto IIIA) coincide with plain Lagrange collocation.
  * Reflection-style (Radau IA, Lobatto IIIC), D(s)-style (Radau II
    D(s), Lobatto IIIB), and C(s − 1)-style (Lobatto III) variants
    all diverge entry-for-entry from plain collocation.
  * This pattern matches Butcher's Table 344(I) classification
    column-by-column.

- **The `SatisfiesC k` proof template scales down cleanly.** Cycle 329
  closed a 4-arm `C(2)` proof with `fin_cases i <;> interval_cases k
  <;> simp <;> norm_num` (norm_num needed for the fractional
  `2/3 · 0 + 1/3 · 2/3 = 2/9` arm); cycle 331 closes a 4-arm `C(1)`
  proof with `fin_cases i <;> interval_cases k <;> simp` (no
  norm_num needed because all arms reduce to `0 = 0` or `1 = 1`
  trivially after `c i ^ 0 = 1`). The chain compiles warning-clean.

- **Cycle 331 is the natural pivot point.** With six direct-form ships
  in six consecutive cycles, the D-ladder's "audit then transcribe"
  recipe has reached diminishing returns within §344 — every remaining
  small-`s` ship would either repeat the same template (`SatisfiesB
  p + SatisfiesC/D k`) or introduce irrational arithmetic (`√6` for
  Radau I `s = 3`, etc.) that demands multi-cycle work. The cycle 332
  planner has clean pivot candidates listed in §H.

## Suggested next approach

Three ranked options for cycle 332:

1. **Pivot to a fresh entity (RECOMMENDED).** The small-`s` D-ladder
   is saturated. Candidates from `plan.md`:
   - `def:422B` (underlying one-step method for LMMs, definition-only) —
     standalone Chapter 4 deliverable, minimal dependencies, ~1 cycle.
   - `def:442A` (principal sheet, definition-only) — Chapter 4
     deliverable, ~1 cycle.
   - `thm:535A` (underlying one-step method for GLMs) — multi-cycle
     (likely 2-3) but unlocks a substantive Chapter 5 anchor.
   - `thm:541A` (DIMSIM types) — scoping-doc style, ~1 cycle.

2. **Formal collocation/printed-table bridge for Radau I `s = 2`**
   (cycle 330 Option 2, ~150 LOC). Mirror cycle 324's
   `butcherRadauII_collocationA_two` construction to define
   `butcherRadauI_collocationA_two` from
   `∫₀^{c_i} L_j(x) dx` over the Radau I abscissae `(0, 2/3)`, then
   prove `butcherRadauIA_two = butcherRadauIDirect_two` (the C(s)
   coincidence theorem). This is the first non-trivial step beyond
   mechanical direct-form transcription within §344, and it leverages
   the cycle 329 audit's confirmed coincidence.

3. **Continue ladder to `butcherLobattoIIIDirect_three`** (~150 LOC).
   Lobatto abscissae at `s = 3` are `(0, 1/2, 1)` (still rational, no
   `√6` arithmetic), but the A-matrix is 9-entry with a 6-arm
   `SatisfiesC 2` certificate. Mechanical but multi-arm; less
   strategically interesting than option 2.

My recommendation is **option 1 with `def:422B` as the first concrete
target**, because cycle 332 should explicitly mark the audit-ladder
saturation by pivoting to a fresh deliverable rather than chasing
diminishing-return §344 ships.
