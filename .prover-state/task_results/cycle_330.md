# Cycle 330 Results

## Worked on

§344 Phase D.10: shipped `butcherLobattoIIICDirect_two : RKTableau 2`
("reflections of Lobatto III" variant per Butcher Table 344(IV)
p. 226, `extraction/raw_text/ch03.txt:5389-5396`) inline in
`OpenMath/Chapter3/Section344.lean`, plus a `SatisfiesB 2` non-vacuity
example. This is the fifth cycle in the small-`s` direct-form RK
ladder following 326 / 327 / 328 / 329.

## Approach

Mechanical lift of the cycle 329 template with the C(2) arm dropped.
Per the cycle 330 strategy §B.2 audit, both `SatisfiesC 2` and
`SatisfiesD 2` provably fail for Lobatto IIIC at `s = 2` (printed
order `p = 2`), so `SatisfiesB 2` is the appropriate non-vacuity bar
— matching cycles 326 / 327's reflection-variant precedent (ship
just `B(p)`).

Concrete steps:

1. Pre-write audit (already done by the planner in strategy §B): for
   `c = (0, 1)` plain Lagrange basis gives `L_0(x) = 1 − x`,
   `L_1(x) = x`. Plain collocation rows: `(0, 0)` and `(1/2, 1/2)`.
   Butcher's printed Lobatto IIIC `s = 2` table: rows
   `(1/2, -1/2)` and `(1/2, 1/2)`. Row 0 disagrees entry-for-entry,
   row 1 happens to coincide. **Divergent** — fourth divergent
   audit outcome out of five D-ladder cycles (cycles 326 Radau IA,
   327 Lobatto IIIB, 328 Radau II D(s), 330 Lobatto IIIC) with only
   cycle 329's Radau I C(s) variant coinciding.
2. Wrote the def inline:
   `c = ![0, 1]`, `b = ![1/2, 1/2]`, `A = !![1/2, -(1/2); 1/2, 1/2]`.
3. Wrote the `SatisfiesB 2` example with two `interval_cases k`
   arms. First arm `k = 1` reduces to `1/2 + 1/2 = 1/1` and needs
   trailing `norm_num`. Second arm `k = 2` closes by `simp` alone
   because `c i ^ 1 = c i` is reduced to `c 0 = 0` and `c 1 = 1`
   in the unfold, leaving `(1/2) * 0 + (1/2) * 1 = 1/2` which simp
   normalises directly.
4. Verified: `lake env lean OpenMath/Chapter3/Section344.lean` exits
   silently (no warnings, no errors). `lake build
   OpenMath.Chapter3.Section344` builds in 5.7s on a warm rebuild.
   `grep -c sorry` = 0. `#print axioms` returns the standard
   `[propext, Classical.choice, Quot.sound]`.

## Result

**SUCCESS**. `butcherLobattoIIICDirect_two : RKTableau 2` shipped
axiom-clean with one `SatisfiesB 2` non-vacuity example. Section344.lean
LOC grew 1957 → 2017 (+60). Five-for-five clean audit-first outcomes
across the D-ladder.

## Faithfulness check

For `def butcherLobattoIIICDirect_two : RKTableau 2`:

- Entity ID: no per-entity JSON exists for `def:Lobatto_IIIC_s2`
  (extractor only emits the umbrella `thm:344A` for §344). Source
  is Butcher Table 344(IV) p. 226, `extraction/raw_text/ch03.txt`
  lines 5389-5396, which print:

  > Lobatto IIIC   (s = 2, p = 2),
  >                                            0       1
  >                                                    2       − 12
  >                                                    1           1
  >                                            1       2           2
  >                                                    1           1
  >                                                    2           2

  (PDF text extraction artefact — the table layout encodes rows
  `c | A` and trailing row `| b`, with `1/2`, `−1/2`, `1/2`, `1/2`
  as the A entries and `(1/2, 1/2)` as `b`.)
- Lean values: entry-for-entry copy of the printed table. `c = ![0, 1]`,
  `b = ![1/2, 1/2]`, `A = !![1/2, -(1/2); 1/2, 1/2]`.
- Lean statement captures: **same content**.

For the `SatisfiesB 2` `example`:

- Captures the order-2 quadrature condition `B(2)` exactly as
  `OpenMath.Chapter3.Section321.SatisfiesB`: for `k ∈ {1, 2}`,
  `∑ⱼ bⱼ · cⱼ^(k-1) = 1/k`.
- Pre-write arithmetic verification (strategy §B.2):
  - `k = 1`: `(1/2)·1 + (1/2)·1 = 1 = 1/1` ✓
  - `k = 2`: `(1/2)·0 + (1/2)·1 = 1/2 = 1/2` ✓
- `B(3)` would FAIL: `(1/2)·0 + (1/2)·1 = 1/2 ≠ 1/3`, matching the
  printed `p = 2`.
- C(2) and D(2) provably FAIL (strategy §B.2 audit). Per cycle 326
  precedent for reflection variants, `SatisfiesB p` alone is the
  appropriate non-vacuity bar. NOT a faithfulness divergence —
  this is the correct certificate set for this tableau.

**Audit divergence (NOT a faithfulness gap)**: the printed
A-matrix is NOT the plain Lagrange-collocation matrix at `(0, 1)`.
This divergence is documented in the def's docstring and the
section header docstring; no coincidence theorem is attempted (none
exists for "reflections of Lobatto III" without first formalising
that construction, which is multi-cycle work — see cycle 326's
`.prover-state/issues/radau_ia_collocation_divergence.md` for the
broader precedent).

Tautology check: the `SatisfiesB 2` example's conclusion does not
appear among its hypotheses (no hypotheses — it's an `example` with
no premises beyond the universal `∀ k, ...`).

Identity check: the proof is not `exact h`; it is a genuine
mechanical close via `interval_cases k` + `simp` + `norm_num`.

Definition smuggling check: `RKTableau 2` is an existing structure
from cycle 308 / §312; no new structure with `Prop` fields is
introduced. The def assembles three concrete `Fin`-valued data
fields, no `Prop`-field smuggling possible.

Hypothesis strength check: no extra hypotheses; the def is a bare
inline constructor mirroring Butcher's printed table.

## Dead ends

None this cycle. The first compile attempt hit one tiny issue:
the strategy's `simp + norm_num` template assumed both arms need
`norm_num`, but for `k = 2` `simp` closed the goal alone (`c i ^ 1`
reduces to `c i` and the resulting `1/2 * 0 + 1/2 * 1 = 1/2` falls
to simp's arithmetic normalisation without needing `norm_num`).
Trailing `norm_num` then failed with "No goals to be solved" at
2015:59. Fixed by writing the two arms as separate bullets:

```
· simp [butcherLobattoIIICDirect_two, Fin.sum_univ_two]; norm_num
· simp [butcherLobattoIIICDirect_two, Fin.sum_univ_two]
```

instead of the `interval_cases k <;> simp <;> norm_num` chain (which
also worked but emitted an `unnecessarySeqFocus` warning).

## Discovery

For `SatisfiesB k` examples on tableaux where `c` contains a `1`
entry, `simp` may close the `(k − 1) = 1` arm (the power-1 case
where `c i ^ 1 = c i`) without needing `norm_num`, while still
needing `norm_num` for the `(k − 1) = 0` arm (`c i ^ 0 = 1` triggers
fractional sum). When a one-size-fits-all `<;>` chain is used, this
produces an `unnecessarySeqFocus` warning. The cleanest fix is to
keep separate bullets per `interval_cases` arm and add `norm_num`
selectively. This is a textbook two-arm pattern for `SatisfiesB 2`
on tableaux with `c_s = 1`; future small-`s` ships should expect
the second arm to often close by `simp` alone.

Five-cycle D-ladder pattern now confirmed: only the C(s) variant of
Radau I `s = 2` (cycle 329) coincides with plain Lagrange collocation;
all four reflection-style / D(s) variants (326 Radau IA, 327 Lobatto
IIIB, 328 Radau II D(s), 330 Lobatto IIIC) diverge entry-for-entry.
This matches Butcher Table 344(I) row 5224's prose: only `Choice of
A = C(s)` rows arise from plain collocation; "reflections of X" and
"D(s)" rows are different constructions.

## Suggested next approach

Cycle 331+ planner options (ranked):

1. **Lobatto III `s = 2` (unsuffixed family)** — `ch03.txt:5372`
   confirms a printed table at `p = 2`; A-matrix per `ch03.txt:5221`
   is `C(s−1)` with last-column zeros. ~50 LOC mechanical ship in
   the same template. Audit outcome uncertain (last-column zero
   implies divergence from plain collocation but it's a specific
   variant). This would be the sixth direct-form ship and saturate
   the small-`s` Lobatto direct-form ladder.
2. **Collocation-coincidence cross-check lemma for Radau I `s = 2`**
   (the cycle 329 §I option 2): formalise `butcherRadauI_collocationA_two`
   mirroring cycle 324's IIA construction and prove
   `butcherRadauIDirect_two.A = _collocationA_two`. ~150 LOC, the
   first formal collocation/printed-table bridge in the §344 ladder.
3. **`butcherRadauIDirect_three`** — defer per the strategy's
   §H ranking (`√6` arithmetic; multi-cycle).
4. **Pivot to a fresh Chapter 5 entity** if the small-`s` §344
   ladder is approaching diminishing returns. Candidates:
   `def:451A` G-stable companion, `def:422B`, `def:442A`,
   `thm:535A`, `thm:541A`.

My recommendation: option 1 (Lobatto III `s = 2`) for another
audit-first divergent / coincident classification ship that
finishes saturating the small-`s` Lobatto family. After that,
strongly consider option 2 (formal collocation/printed-table
bridge for Radau I `s = 2`) as the first non-trivial step beyond
mechanical lifts.
