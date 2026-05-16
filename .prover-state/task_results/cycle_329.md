# Cycle 329 Results

## Worked on

§344 Phase D.9 — shipped `butcherRadauIDirect_two : RKTableau 2`
(the C(s) variant of Radau I at `s = 2`) plus `SatisfiesB 3` and
`SatisfiesC 2` non-vacuity witnesses, all inline in
`OpenMath/Chapter3/Section344.lean` after the cycle 328 D.8 block.

## Approach

Followed the strategy's audit-first protocol verbatim:

1. **Audit (Path α)**: Re-read `extraction/raw_text/ch03.txt:5260–5275`
   and confirmed Butcher's printed Radau I `s = 2` table parses to
   `c = (0, 2/3)`, `b = (1/4, 3/4)`, `A = !![0, 0; 1/3, 1/3]`.
2. **Cross-check vs plain Lagrange collocation** (per strategy §C.2):
   computed `A_{0,0} = A_{0,1} = 0` (vacuous, `c_0 = 0`),
   `A_{1,0} = ∫₀^{2/3} (1 − (3/2)x) dx = 1/3`,
   `A_{1,1} = ∫₀^{2/3} ((3/2)x) dx = 1/3`. The collocation values
   agree with the printed table entry-for-entry — first D-ladder
   cycle where the audit outcome is **coincidence** rather than
   divergence (cycles 326/327/328 were all divergent).
3. **Template lift**: Used cycle 328's `D.8` block as the literal
   template (`def` shape, `B(3)` three-arm close, `D(2)` four-arm
   close). Swapped `SatisfiesD 2` → `SatisfiesC 2` since Radau I
   is the C(s) variant, and adjusted the `intro` binder name
   `j` → `i` to match `SatisfiesC`'s outer binder
   (`OpenMath/Chapter3/Section321.lean:99`).
4. **Pre-write arithmetic spot-check** of all four `C(2)` cases
   `(i, k) ∈ {0,1} × {1,2}`:
   - `(0, 1)`: `0·1 + 0·1 = 0 = 0^1/1` ✓
   - `(0, 2)`: `0·0 + 0·(2/3) = 0 = 0^2/2` ✓
   - `(1, 1)`: `(1/3)·1 + (1/3)·1 = 2/3 = (2/3)^1/1` ✓
   - `(1, 2)`: `(1/3)·0 + (1/3)·(2/3) = 2/9 = (4/9)/2` ✓
5. **Wrote** the D.9 block (header docstring + def + two examples,
   74 LOC).
6. **Verified** per strategy §F:
   - `lake env lean OpenMath/Chapter3/Section344.lean` → exit 0
     (silent — no warnings, no errors).
   - `lake build OpenMath.Chapter3.Section344` → ✔ 2803 / 2803
     jobs, 5.6s.
   - `grep -c sorry` → 0.
   - `#print axioms OpenMath.Chapter3.Section344.butcherRadauIDirect_two`
     → `[propext, Classical.choice, Quot.sound]`.

Did not invoke Aristotle this cycle — the `B(3)` and `C(2)`
mechanical closes are textbook three- and four-arm
`simp + norm_num` patterns lifted verbatim from cycles 324 and 328;
they fired on the first compile. Aristotle would have been pure
overhead for a ~50 LOC mechanical ship.

Did not pursue the strategy §D.3 stretch goal (collocation-coincidence
cross-check lemma) — the required deliverables were complete and
verified well within budget, but lifting the collocation A-matrix
formally is the natural cycle 330+ pickup point per strategy §I,
and shipping a partial cross-check this cycle would split the work
awkwardly across cycles.

## Result

SUCCESS — all five §F verification checks passed. Three new public
symbols (`butcherRadauIDirect_two` + two anonymous `example`s)
delivered, all axiom-clean. Section344.lean LOC: 1883 → 1957
(+74, within the strategy's `~50 LOC` budget envelope counting the
substantive docstrings). Sorry count: 0.

## Faithfulness check

### `def butcherRadauIDirect_two : RKTableau 2`

- Entity ID: no per-entity JSON exists for `def:RadauI_s2` (the
  extractor only emits `thm:344A` for the surrounding section, per
  strategy §E). Source is Butcher Table 344(I) p. 225,
  `extraction/raw_text/ch03.txt:5260–5275`. Quoted in the
  declaration docstring with the line range citation.
- Textbook statement (from `ch03.txt:5265–5270`):
  > Radau I        (s = 2, p = 3),
  >                                                       0        0       0
  >                                                       2        1       1
  >                                                       3        3       3
  >                                                                1       3
  >                                                                4       4
- Parsed values: `c₁ = 0, c₂ = 2/3`; `A_{1,1} = 0, A_{1,2} = 0`,
  `A_{2,1} = 1/3, A_{2,2} = 1/3`; `b₁ = 1/4, b₂ = 3/4`.
- Lean values: `c := ![0, 2/3]`, `A := !![0, 0; 1/3, 1/3]`,
  `b := ![1/4, 3/4]`.
- Lean statement captures: **same content** — entry-for-entry
  match against Butcher's printed table.
- No equivalence required: printed values copied verbatim. The
  audit cross-check against plain Lagrange collocation (strategy
  §C.2) is informational; it documents that the C(s) variant of
  Radau I happens to coincide with plain collocation at the Radau
  I abscissae, but the docstring explicitly cites Butcher's
  printed table as the source, not collocation.

### `example : butcherRadauIDirect_two.SatisfiesB 3`

- No new definitions introduced (`SatisfiesB` is the existing
  `OpenMath.Chapter3.Section321.RKTableau.SatisfiesB` predicate).
- Tautology check: the example takes only the universally-bound
  hypotheses `k : ℕ, h1 : 1 ≤ k, hk : k ≤ 3`; the goal is not
  a hypothesis.
- Identity check: proof is a real three-arm arithmetic close, not
  `exact h`.
- Hypothesis strength check: the goal hypotheses are the standard
  `SatisfiesB`/`SatisfiesC` quantification arity; nothing extra.

### `example : butcherRadauIDirect_two.SatisfiesC 2`

- No new definitions introduced (`SatisfiesC` is the existing
  `OpenMath.Chapter3.Section321.RKTableau.SatisfiesC` predicate).
- Tautology check: takes only the universally-bound
  `i : Fin 2, k : ℕ, h1 : 1 ≤ k, hk : k ≤ 2`; goal is not a
  hypothesis.
- Identity check: proof is a real four-arm `fin_cases <;>
  interval_cases <;> simp <;> norm_num` arithmetic close.
- Hypothesis strength check: standard `SatisfiesC` arity.

## Dead ends

None. The mechanical template fired on the first compile. The
only minor adjustment from the cycle 328 template was the `intro`
binder name swap `j` → `i` (since `SatisfiesC`'s outer binder is
`i : Fin s`, vs `SatisfiesD`'s `j : Fin s`) — caught pre-write by
reading `OpenMath/Chapter3/Section321.lean:99`, as suggested by
strategy §H step 3.

## Discovery

**Audit-first protocol now generalises across both divergent
(IA / IIIB / II D(s)) and coincident (I C(s)) cases.** This is the
key structural data point for cycle 330+: the protocol's value is
not just catching divergences (cycles 326/327/328) but documenting
the *outcome* of each audit, so future cycles know which printed
tables are safely liftable from plain collocation and which require
the formal recipe (D(s) construction, "reflections of X", etc.).

A pattern is now visible across the four direct-form ships
(cycles 326–329):

| Cycle | Family             | s | Variant      | Coincides w/ plain collocation? |
|-------|--------------------|---|--------------|---------------------------------|
| 326   | Radau IA           | 2 | reflections  | NO                              |
| 327   | Lobatto IIIB       | 3 | D(s)         | NO (D(s) recipe, not collocation) |
| 328   | Radau II (Direct)  | 2 | D(s)         | NO (last column zero)           |
| 329   | Radau I            | 2 | C(s)         | YES                             |

The C(s) row of Butcher Table 344(I) is the unique liftable row.
Per the strategy's recommendation, future cycles that want a formal
collocation lift should target Radau I `s = 2` (this cycle's ship)
or Radau IIA `s = 2` (cycle 324's `butcherRadauIIA_two_eq_direct`
coincidence theorem already exists) first; the D(s) and reflection
variants need their own infrastructure.

**Mechanical template is now four-cycle stable.** Cycles 326/327/
328/329 all close with the same `interval_cases k; simp [_, Fin.sum_univ_*];
norm_num` for the `B(*)` order arm and (for cycles 328/329) the
`fin_cases <;> interval_cases <;> simp <;> norm_num` for the
characteristic-condition arm. The cycle 327 worker's
"mechanical-template" hypothesis is now load-bearing — future
small-`s` direct-form ships should follow this template by default.

**The `intro` binder name matters for legibility, not correctness.**
`SatisfiesB` has outer binder `k : ℕ`, `SatisfiesC` has `i : Fin s,
k : ℕ`, `SatisfiesD` has `j : Fin s, k : ℕ`. The strategy correctly
flagged this in §D.2 — the binder names must match, but the proof
script is otherwise identical. A future cycle could probably factor
this into a `Tableau.satisfies_BCDE_at_small_s` tactic, but with only
four data points it's premature.

**Audit time is dominated by parsing Butcher's tables, not Lean
work.** The C(s) audit took ~5 minutes (re-read raw text, parse
column layout, compute four collocation integrals by hand). The
Lean writeup took ~10 minutes (lift cycle 328 template, swap
binder names, swap `SatisfiesD` → `SatisfiesC`). Build + axiom
check took ~2 minutes total. The strategy's `~5 min audit + ~20
min Lean + ~10 min verify` estimate was accurate to within ±5 min
per phase.

## Suggested next approach

Per strategy §I, cycle 330+ candidates ranked:

1. **Lobatto IIIC `s = 2` direct form** (best continuation of the
   small-`s` ladder). Per `ch03.txt:5224`, Lobatto IIIC =
   "reflections of Lobatto III"; the audit-first protocol should
   classify this as either divergent (likely) or coincident.
   Either outcome is informative; ~50 LOC ship; matches cycle
   326's pattern. The `SatisfiesC`/`SatisfiesD` certificate
   selection depends on which variant Butcher's IIIC row picks.
2. **Collocation-coincidence formalisation for Radau I `s = 2`**
   (the strategy §D.3 stretch goal, deferred this cycle). Build
   `butcherRadauI_collocationA_two : Fin 2 → Fin 2 → ℝ` (mirror
   of cycle 324's `butcherRadauII_collocationA_two`), four `_apply`
   theorems, then prove `butcherRadauIDirect_two.A = _collocationA_two`
   as a coincidence lemma. ~150 LOC; medium-cycle. Would be the
   first formal collocation/printed-table bridge in the §344 D
   ladder, validating that Butcher's C(s) row is the unique
   directly-liftable row.
3. **Lobatto III `s = 2` (unsuffixed family)** — needs a grep of
   `ch03.txt` first to confirm a printed table exists. If yes,
   ~50 LOC ship.
4. **`butcherRadauIDirect_three`** (Radau I `s = 3`) — defer.
   Per `ch03.txt:5307` this involves `√6` arithmetic and is
   multi-cycle work. The small-`s` ladder should be saturated
   before pushing to `s = 3`.
5. **Investigation of Butcher's "reflections of X" precise meaning**
   — multi-cycle blocker work that would unlock canonical Radau IA
   and Lobatto IIIB / IIIC collocation/reflection bridges. Deferred
   per cycle 326's `radau_ia_collocation_divergence.md` issue file.
6. **Pivot to a fresh Chapter 5 entity** (per cycle 327 outlook):
   `def:451A` G-stable companion, `def:422B`, `def:442A`,
   `thm:535A`, `thm:541A`. Use if the §344 small-`s` ladder is
   approaching saturation and a fresh substrate would be more
   productive than another ~50 LOC ship.

Planner recommendation: **option 1 (Lobatto IIIC `s = 2`)** is
the natural cycle 330 target — same ~50 LOC mechanical template,
exercises the audit protocol on a fresh row of Butcher Table
344(IV), and continues the small-`s` ladder.
