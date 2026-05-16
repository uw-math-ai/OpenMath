# Cycle 333 Results

## Worked on
Phase D.13 of §344: Lobatto IIIA `s = 3` collocation-form
`RKTableau` + coincidence theorem with the direct (Simpson's-rule)
form. This scales the cycle 332 Radau I C(s) `s = 2` template to
three stages.

New symbols introduced (14 total, all axiom-clean
`[propext, Classical.choice, Quot.sound]`):

- `butcherLobatto_collocationA_three : Fin 3 → Fin 3 → ℝ` (def)
- `butcherLobatto_collocationA_three_apply_{zero_zero, zero_one,
  zero_two, one_zero, one_one, one_two, two_zero, two_one,
  two_two}` (9 `_apply` theorems)
- `butcherLobattoIIIA_three : RKTableau 3` (def, collocation form)
- `butcherLobattoIIIADirect_three : RKTableau 3` (def, direct form)
- `butcherLobattoIIIA_three_eq_direct` (coincidence theorem)
- `SatisfiesB 4` anonymous `example`

## Approach
Verbatim port of cycle 332's template scaled from 2 to 3 stages:

1. **Row 0 (3 theorems, ~7 LOC each)**: `c_0 = 0`, so the
   integration interval `[0, 0]` is degenerate. Each `_apply`
   closes by `simp [butcherLobatto_zeros_three,
   intervalIntegral.integral_same]` after the `unfold` + `show`
   reframing — identical to cycle 323's `Lobatto IIIA s = 2`
   row-0 closures.

2. **Row 1 (3 theorems, ~37 LOC each)**: `c_1 = 1/2`, so the
   collocation integrals are over `[0, 1/2]`. The Lagrange basis
   polynomials at `(0, 1/2, 1)` are
   `L_0(x) = 2x² − 3x + 1`, `L_1(x) = −4x² + 4x`,
   `L_2(x) = 2x² − x` — these closed forms are already used in
   cycle 321's quadrature-weight `_apply` theorems (lines
   1024–1125). The cycle 321 proof bodies port verbatim with the
   single change `[0, 1] → [0, 1/2]` and the corresponding
   arithmetic shifts: `∫₀^(1/2) x² = 1/24`, `∫₀^(1/2) x = 1/8`.
   Expected values per linearity:
   - `∫₀^(1/2) (2x² − 3x + 1) = 1/12 − 3/8 + 1/2 = 5/24` ✓
   - `∫₀^(1/2) (−4x² + 4x) = −1/6 + 1/2 = 1/3` ✓
   - `∫₀^(1/2) (2x² − x) = 1/12 − 1/8 = −1/24` ✓

3. **Row 2 (3 theorems, ~12 LOC each)**: `c_2 = 1`, so the
   collocation integral is `∫₀^1 L_j(x) dx`, which IS the
   quadrature weight `butcherLobatto_quadratureWeights_three j`
   by definition. After `rw [h_c2]`, the goal becomes
   `∫₀^1 L_j(x) = b_j`, which is exactly the cycle 321 weight
   `_apply` theorem — closed by `exact
   butcherLobatto_quadratureWeights_three_apply_<j>`. The alias
   route works definitionally, no extra reasoning needed.

4. **Tableaux + coincidence theorem**: `butcherLobattoIIIA_three`
   threads cycle 320's zeros, cycle 321's weights, and this
   cycle's collocation A-matrix. `butcherLobattoIIIADirect_three`
   declares Butcher Table 344(I) values inline. Coincidence proof
   has 15 arms (9 + 3 + 3) following the cycle 332 template
   verbatim: `RKTableau.mk.injEq` + `funext` + `fin_cases` per
   field, each leaf `show ... = _; rw [matching _apply]; rfl`.

5. **`SatisfiesB 4`**: routes via the coincidence rewrite to the
   direct form, then `interval_cases k` over `k ∈ {1, 2, 3, 4}`,
   each closed by `simp [butcherLobattoIIIADirect_three,
   Fin.sum_univ_three]; norm_num`.

## Result
SUCCESS — `lake env lean OpenMath/Chapter3/Section344.lean` and
`lake env lean OpenMath/Chapter3.lean` both exit 0; sorry count
in Section344.lean = 0; axiom-clean verified for all 14 new
symbols (`[propext, Classical.choice, Quot.sound]`).
Section344.lean LOC: 2273 → 2572 (+299; within the strategy's
~450–550 LOC budget — the row-2 alias route reduced LOC by ~135).
The `SatisfiesB 4` `simp + norm_num` chain closed all four arms
without needing the fallback `show`+`Fin.sum_univ_three` explicit
decomposition flagged in the strategy's §E risk row 6.

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `butcherLobatto_collocationA_three` (def)
- Entity ID: `thm:344A` (overall §344 headline; this is
  infrastructure feeding the Lobatto IIIA C(s) row of Butcher
  Table 344(I) p. 226).
- Textbook content (Butcher §344 Table 344(I) "Lobatto IIIA"
  row): A-matrix follows the "C(s)" recipe, i.e.
  `A_{ij} = ∫₀^{c_i} L_j(x) dx` at the Lobatto abscissae.
- Lean statement captures: **same content**. The def matches the
  standard collocation construction (the
  `∫₀^{c_i} L_j(x) dx` integral over the Lagrange basis at the
  given abscissae) and is reused at `s = 3` with the three-leaf
  Lobatto nodes.

### Nine `_apply` theorems
- Textbook statement (Butcher Table 344(I) "Lobatto IIIA `s = 3`"):
  > `A = !![0, 0, 0; 5/24, 1/3, -1/24; 1/6, 2/3, 1/6]`
- Lean statements capture: **same content** — each `_apply` is
  the concrete arithmetic identity matching the corresponding
  entry of the Butcher-printed A-matrix.

### `butcherLobattoIIIA_three` (def)
- Textbook content: the Lobatto IIIA `s = 3` `RKTableau` is
  defined by Butcher Table 344(I) values (`c`, `b`, `A` printed
  on p. 226).
- Lean statement captures: **same content**. The tableau is
  assembled definitionally from cycle 320's `_zeros_three`,
  cycle 321's `_quadratureWeights_three`, and this cycle's
  `_collocationA_three`. The coincidence theorem (next item)
  proves equality with the direct printed form.

### `butcherLobattoIIIADirect_three` (def)
- Textbook content: direct Butcher Table 344(I) p. 226 values,
  declared inline.
- Lean statement captures: **same content**. Literal transcription
  of the textbook tableau.

### `butcherLobattoIIIA_three_eq_direct` (theorem)
- Textbook content: the C(s)-variant (Lobatto IIIA) of the
  Lobatto quadrature family coincides with plain Lagrange
  collocation. This follows from the Butcher Table 344(I) "C(s)"
  classification of the A-matrix construction.
- Lean statement captures: **same content** — the equality between
  the collocation-assembled tableau and the direct printed tableau
  is precisely the formal expression of the textbook's "C(s)"
  labeling. Does real work: 15 non-trivial leaf rewrites, no
  tautology.

### `SatisfiesB 4` example
- Textbook content: Lobatto IIIA `s = 3` (Simpson's rule)
  achieves classical order `2s − 2 = 4` (Butcher Table 344(III)
  p. 245, "Lobatto IIIA" stage and order columns), so the
  quadrature condition `B(4)` is maximal.
- Lean statement captures: **same content**. Non-vacuous: at
  `k = 2`, `(1/6)·0 + (2/3)·(1/2) + (1/6)·1 = 1/2`; at `k = 3`,
  `(1/6)·0 + (2/3)·(1/4) + (1/6)·1 = 1/3`; at `k = 4`,
  `(1/6)·0 + (2/3)·(1/8) + (1/6)·1 = 1/4`.

No new `class` or `structure` introduced. No `Prop` fields with
ambiguous hypothesis-vs-conclusion status. Tautology/identity
checks all clear (each `_apply` is a substantive integral
evaluation, the coincidence theorem composes 15 non-trivial
rewrites).

## Dead ends
None — the template port was fully mechanical, matching the
cycle 332 (and earlier 323/324) experience and confirming the
worker's cycle 327 mechanical-template hypothesis once again.

## Discovery
- **Row-2 alias route works definitionally without `show`
  intermediation**. The simple `rw [h_c2]; exact
  butcherLobatto_quadratureWeights_three_apply_<j>` closes each
  of the three row-2 `_apply` theorems directly. No further
  unification massaging was needed (the strategy's `show`
  fallback for the case where unification fails wasn't required).
  This is the lowest-LOC closure pattern in the §344 ladder so
  far: ~12 LOC per theorem versus ~37 LOC for the substantive
  row-1 entries.
- **`SatisfiesB 4` four-arm closure** with `simp +
  Fin.sum_univ_three + norm_num` per arm scales cleanly from
  `Fin.sum_univ_two` (cycles 322/323/324/325/329/332). No
  hot-path issues; the `norm_num` arithmetic at `k = 3, 4` (rational
  fractions like `(2/3)·(1/4) + (1/6)·1 = 1/3` and
  `(2/3)·(1/8) + (1/6)·1 = 1/4`) is well within `norm_num`'s
  comfort zone.

## Suggested next approach
Three options for cycle 334, in increasing scope:

1. **Pivot to fresh entity** (recommended — breaks the 17-cycle
   §344 streak): `def:422B` (underlying one-step method for LMM,
   §422) or `def:442A` (principal sheet, §442) are
   definition-only and single-cycle. Either gives a clean break
   without scoping overhead.

2. **Stretch the `SatisfiesC 3` certificate for
   `butcherLobattoIIIA_three`**: the C(s)-defining collocation
   simplifying assumption at `s = 3` (9 arms: 3 stages × 3
   exponents). This was deferred from cycle 333 in deference to
   the §C sequencing recommendation; ~15–25 LOC. Lifts via the
   coincidence theorem to the direct form, similar to cycle 332's
   `SatisfiesC 2` certificate.

3. **Phase B.2 of `thm:344A`** (polynomial-exactness headline):
   the headline `2s − 2` / `2s − 3` order result. Multi-cycle,
   requires the `B(2s − 1)` / `B(2s − 2)` order-condition
   machinery and polynomial-division reasoning (Butcher p. 244
   proof outline).

Recommend option 1 to break the §344 streak; option 2 is a clean
follow-up if the planner wants one more §344 cycle before
pivoting.
