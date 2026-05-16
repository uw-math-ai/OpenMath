# Cycle 332 Results

## Worked on

§344 Phase D.12 — the first non-trivial coincidence theorem in the §344
small-`s` D-ladder. Specifically, formalising the C(s)-coincidence of
the Radau I `s = 2` quadrature with plain Lagrange collocation, by

1. defining the collocation A-matrix
   `butcherRadauI_collocationA_two (i j) = ∫₀^{c_i} L_j(x) dx`
   at the Radau I abscissae `c = (0, 2/3)`,
2. evaluating its four entries to the closed-form Butcher Table 344(I)
   values `(0, 0, 1/3, 1/3)`,
3. assembling a `RKTableau 2` `butcherRadauI_collocation_two`,
4. proving the coincidence
   `butcherRadauI_collocation_two = butcherRadauIDirect_two` (cycle 329's
   inline Radau I C(s) tableau), and
5. lifting the order-3 `B(3)` and order-2 `C(2)` non-vacuity examples
   through the coincidence theorem.

All six new public symbols (plus two `example` blocks) live in
`OpenMath/Chapter3/Section344.lean` after cycle 331's
`butcherLobattoIIIDirect_two` block (now ending around line 2275).

## Approach

Verbatim mechanical port of cycle 324's `butcherRadauII_collocationA_two`
recipe (lines 1417–1614 of `Section344.lean`) per the cycle 332 planner
recipe:

- The `_apply_zero_*` entries are short (degenerate-interval) closures
  via `intervalIntegral.integral_same` since `c_0 = 0` at the Radau I
  abscissae.
- The `_apply_one_*` entries follow cycle 324's
  `_apply_one_{zero, one}` proof skeleton verbatim with substitutions
  `RadauII → RadauI`, `c_1 = 1 → c_1 = 2/3`, basis evaluation values
  swapped (`L_0(x) = 1 − (3/2)x`, `L_1(x) = (3/2)x` — note `L_0` has
  no `-1/2` constant offset and `L_1` has no `+(slope·shift)` term, so
  `_apply_one_one` only needs `integral_const_mul` whereas
  `_apply_one_zero` still uses the `integral_sub + integral_const +
  integral_const_mul` chain).
- The pivotal arithmetic identity `∫₀^{2/3} x = 2/9` comes from
  `integral_pow` at `b = 2/3`, `pow_one`, then `norm_num`.
- The coincidence theorem follows the cycle 324 `mk.injEq` recipe
  verbatim with the four `_apply` rewrites + cycle 321's two weight
  rewrites + three `rfl`'s for the `c` component.
- Both non-vacuity examples (`B(3)` and `C(2)`) lift through the
  coincidence rewrite to the direct-form arithmetic already discharged
  in cycle 329.

No Aristotle submissions this cycle — per the planner DO-NOT-#8, the
recipe is a verbatim port with a working template at hand, so manual
closure was strictly faster than an Aristotle round-trip.

## Result

SUCCESS.

- `lake env lean OpenMath/Chapter3/Section344.lean` exits 0.
- `lake env lean OpenMath/Chapter3.lean` exits 0.
- `grep -c sorry OpenMath/Chapter3/Section344.lean` returns 0.
- All Deliverables 1–5 plus the stretch `SatisfiesC 2` example landed
  on the first compile.

Six new public symbols shipped (one `def`, four `theorem`'s, one
additional `def`, one coincidence `theorem` = 7 with the def):

1. `butcherRadauI_collocationA_two` (def)
2. `butcherRadauI_collocationA_two_apply_zero_zero` (thm)
3. `butcherRadauI_collocationA_two_apply_zero_one` (thm)
4. `butcherRadauI_collocationA_two_apply_one_zero` (thm)
5. `butcherRadauI_collocationA_two_apply_one_one` (thm)
6. `butcherRadauI_collocation_two` (def)
7. `butcherRadauI_collocation_two_eq_direct` (thm)

Plus two `example` certificates (`SatisfiesB 3`, `SatisfiesC 2`).

## Faithfulness check

All new content is supporting infrastructure for Butcher §344
(`thm:344A`'s Table 344(I) C(s)-variant Radau I row). No new named
mathematical concept is being introduced — these are *concrete tableaux
and quadrature evaluations* derived from Butcher's printed numbers.

- Entity ID: `thm:344A` (Butcher §344, p. 244, Table 344(I), row "Radau
  I — Radau I quadrature — C(s)").
  Textbook statement (quoted from `formalization_data/entities/thm_344A.json`):
  > Let c_1 < c_2 < ··· < c_s be chosen as abscissae of the Radau I,
  > the Radau II or the Lobatto quadrature formula, respectively. ...
  > For the Radau I formula, c_1 = 0. This formula is exact for
  > polynomials of degree up to 2s − 2.

  Cycle 332 captures: the Radau I `s = 2` C(s)-variant tableau
  `c = (0, 2/3)`, `b = (1/4, 3/4)`, `A = !![0, 0; 1/3, 1/3]`
  in *collocation-defined* form (not direct inline), and proves it
  coincides with the cycle 329 inline form. The textbook Table 344(I)
  row says "Radau I quadrature + C(s)" — i.e., the A-matrix is to be
  computed from the C(s) simplifying assumption at the Radau I
  abscissae, which (per the cycle 329 audit and Butcher's remark on
  C(s) ↔ plain collocation when the quadrature is interpolational
  using all `s` abscissae) is exactly the plain Lagrange-collocation
  matrix `A_{ij} = ∫₀^{c_i} L_j(x) dx` that this cycle defines.

  Lean statement captures: **same content** as the printed Table 344(I)
  Radau I row, now derived from the collocation integral rather than
  asserted inline.

- All four `_apply` theorems are *concrete arithmetic identities*
  (Butcher Table 344(I)'s four printed values). No definition smuggling
  — `butcherRadauI_collocationA_two` is defined as the integral, and the
  four `_apply` theorems prove the printed values are equal to it.

- The coincidence theorem `butcherRadauI_collocation_two_eq_direct` is
  genuine work: it bridges the collocation-defined tableau with cycle
  329's inline tableau via component-wise equality, and the proof goes
  through the four non-trivial `_apply` rewrites — not a tautology.

- No new `class` or `structure` introduced. No `Prop` field whose
  status is ambiguous between hypothesis and conclusion.

- Hypothesis strength: each `_apply` theorem has no hypotheses (concrete
  arithmetic). The coincidence theorem has no hypotheses (concrete
  equality of two definitionally-distinct closed-form tableaux). Both
  non-vacuity examples have no extra hypotheses beyond the textbook
  `B(p)`/`C(η)` definitions from §312.

- Tautology / identity checks: the coincidence theorem's proof routes
  through six non-trivial `_apply` rewrites (four collocation entries +
  two quadrature weights) — not `exact h` or `:= id`. The `_apply`
  theorems each reduce a Lagrange-basis integral via the standard
  `integral_pow` / `integral_const_mul` / `integral_sub` chain — real
  work.

- Absent-theorem check: every theorem promised in the cycle 332
  strategy (Deliverables 1–5 plus the stretch `SatisfiesC 2`) is
  present and proved.

## Dead ends

None — the port closed on first compile. The cycle 324 template
proved load-bearing exactly as the planner predicted: every
substitution (`RadauII → RadauI`, `c_1 = 1 → c_1 = 2/3`, basis
evaluation formulas, integration limits) compiled without further
manual intervention.

Minor risks the planner flagged (cycle 324 precedent caveats) that
*did not* materialise:

- The `Lagrange.basisDivisor` `simp + ring` step needed no extra
  lemmas — `Polynomial.eval_mul/_C/_sub/_X` plus `ring` discharged
  both basis evaluations.
- The `intervalIntegral.integral_const_mul` step did not require
  swapping argument order from the `_apply_one_zero` pattern when
  proving `_apply_one_one` — both compiled directly.

## Discovery

1. **The cycle 324 template is *fully* mechanical for Radau-style
   collocation tableaux at `s = 2`.** Cycle 332 took ~150 LOC and a
   single compile to ship Deliverables 1–5 plus the stretch. Future
   C(s)-coincidence ladder cycles (e.g. Lobatto IIIA `s = 3` with
   Simpson's-rule abscissae `(0, 1/2, 1)` and 9 collocation entries)
   should follow the same template with three-node Lagrange-basis
   evaluations — roughly `3 × 150 ≈ 450` LOC, well within a 2-cycle
   budget.

2. **The `c_i = 0` degenerate case is a 6-LOC closure** via
   `intervalIntegral.integral_same`. Radau I and Lobatto-family ladder
   extensions will benefit: any abscissa equal to `0` makes its row's
   entries vanish at the integral level, costing 6 LOC each rather
   than the ~30 LOC of a non-degenerate `_apply` proof.

3. **The C(s)-coincidence pattern is the structural counterpoint to
   cycles 326/327/328/330/331's divergence audits.** Five consecutive
   reflection-style / D(s) / C(s−1) families *disagree* with plain
   collocation; cycle 332's Radau I C(s) variant *agrees*. This
   matches Butcher's Table 344(I) classification: the families whose
   third column reads "C(s)" coincide with plain collocation; the
   rest don't. Future audits should treat "C(s) row" as the marker
   for a likely coincidence theorem.

4. **Cycle 329's `SatisfiesC 2` proof body is verbatim-portable** to
   `butcherRadauI_collocation_two` once the coincidence rewrite is in
   place. This is a reusable "lift via coincidence" pattern for
   non-vacuity certificates on collocation-defined tableaux.

## Suggested next approach

Per the cycle 332 planner's "Cycle 333 outlook" section, three options:

1. **Mechanical extension to Lobatto IIIA `s = 3`** (Simpson's-rule
   abscissae `(0, 1/2, 1)`; 9 collocation entries; ~3× cycle 332 LOC,
   probably 1–2 cycles). Same template, larger `Finset.erase`
   reductions for the 3-leaf basis polynomials. Per the discovery
   above, this is mechanical and the only friction will be the 9
   `_apply` proofs at the larger denominators.

2. **Pivot to a fresh entity scoping doc** (`def:422B`, `def:442A`,
   `thm:535A`, or `thm:541A`). Each is genuinely multi-cycle; a
   scoping-doc-only cycle 333 would scope one of these before any code
   ships.

3. **Phase B.2 of `thm:344A`** — the polynomial-exactness `2s − 2` /
   `2s − 3` headline. Multi-cycle.

My recommendation: option 1 (Lobatto IIIA `s = 3`) — it extends the
now-validated C(s)-coincidence template by one rung, keeps the §344
infrastructure complete to `s = 3` for at least one family, and is a
1–2 cycle commitment that wastes no compute on speculative upstream
work. If the planner wants to break out of §344, option 2 with a
scoping doc on `thm:541A` (B-series convergence, the next major
post-§3 milestone) is the highest-leverage non-§344 option.

The cycle 332 stretch `SatisfiesC 2` example landed for free, so the
"audit-validated mechanical port" cell of the cycle plan is fully
exhausted at `s = 2` for Radau I C(s). No further work at this rung.
