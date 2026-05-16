# Cycle 327 Results

## Worked on

§344 Phase D.7 — Lobatto IIIB `s = 3` direct-form `RKTableau`. Adds
two new public symbols to `OpenMath/Chapter3/Section344.lean`:

* `butcherLobattoIIIBDirect_three : RKTableau 3` — the Butcher
  Table 344(III) p. 245 tableau declared inline (`A`, `b`, `c`
  copied verbatim from `extraction/raw_text/ch03.txt:5426-5434`).
* an anonymous `example` proving
  `butcherLobattoIIIBDirect_three.SatisfiesB 4` (the maximal
  quadrature order at `s = 3`, `p = 2s − 2 = 4`).

## Approach

Mechanical port of cycle 326's `butcherRadauIADirect_two` direct-
form pattern. No new infrastructure; no Aristotle submission
needed — the `SatisfiesB 4` proof is four arms each closed by
`simp [butcherLobattoIIIBDirect_three, Fin.sum_univ_three]; norm_num`,
the same `Fin.sum_univ_*` + `simp` + `norm_num` triad cycles
322/323/324/325/326 have been using throughout the §344 small-`s`
ladder.

### Audit (per cycle 326 protocol)

Values read directly from `extraction/raw_text/ch03.txt:5426-5434`:

```
Lobatto IIIB   (s = 3, p = 4),
                              0         1/6      -1/6           0
                              1/2       1/6       1/3           0
                              1         1/6       5/6           0
                                        1/6       2/3           1/6
```

Translation to `RKTableau 3`:

* `c = ![0, 1/2, 1]`
* `b = ![1/6, 2/3, 1/6]`
* `A = !![1/6, -(1/6), 0; 1/6, 1/3, 0; 1/6, 5/6, 0]`

`b` and `c` coincide with Lobatto IIIA `s = 3` (both families share
the Lobatto quadrature choice at `(0, 1/2, 1)`); the `A`-matrices
differ (IIIA uses C(s), IIIB uses D(s) per Butcher Table 344(I)).

### Files touched

* `OpenMath/Chapter3/Section344.lean` (1760 → 1807 LOC, +47 LOC).
* `plan.md` — appended Cycle 327 paragraph to the `thm:344A` row.

### Build verification

```
lake env lean OpenMath/Chapter3/Section344.lean    # exit 0
lake build OpenMath.Chapter3.Section344            # exit 0
lake env lean OpenMath/Chapter3.lean               # exit 0 (aggregator)
```

### Axiom-clean spot-check

```
#print axioms OpenMath.Chapter3.Section344.butcherLobattoIIIBDirect_three
-- depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Result

SUCCESS. Two new public symbols shipped, both axiom-clean. No
sorries introduced anywhere; LOC count for the cycle 327 ship is
within budget (+47 LOC ≪ 80 LOC soft ceiling). The `SatisfiesB 4`
proof closed cleanly on the first compile attempt — the same
`interval_cases k <;> simp [_, Fin.sum_univ_three] <;> norm_num`
pattern that cycle 326 used for `Fin.sum_univ_two` ported
mechanically.

The R1 pre-flagged risk (negative literal `-(1/6)` inside `!![...]`
syntax) did not fire — Lean 4's matrix-row literal accepts `-(1/6)`
as a parenthesised `Neg.neg` of a positive `ℝ`-literal without
issue. Same goes for `Fin.sum_univ_three` (R2): it fired as
expected.

## Faithfulness check

For the new `def butcherLobattoIIIBDirect_three : RKTableau 3`:

* **Source**: `extraction/raw_text/ch03.txt:5426-5434` (Butcher
  Table 344(III), p. 245).
* **Textbook statement** (quoted verbatim above): the Butcher-tableau
  triple `(c, A, b)` with `c = (0, 1/2, 1)`, `A` the 3×3 matrix
  with rows `(1/6, -1/6, 0), (1/6, 1/3, 0), (1/6, 5/6, 0)`, and
  `b = (1/6, 2/3, 1/6)`.
* **Lean statement captures**: same content. The `noncomputable
  def` carries the three fields with values matching the Butcher
  printed table entry-for-entry.

For the `SatisfiesB 4` example:

* **Source**: Butcher §344 — Lobatto IIIB at `s = 3` has classical
  order `p = 2s − 2 = 4`, so the maximal `B(η)` quadrature
  condition is `η = 4`.
* **Lean statement captures**: same content — the four arms
  `k = 1, 2, 3, 4` verify `∑ⱼ bⱼ · cⱼ^{k-1} = 1/k` and close by
  `norm_num` (hand-computed in the strategy §E.2 and confirmed
  by Lean).

No definition smuggling: `RKTableau` is a `structure` with three
data fields (no `Prop` fields), so the cycle 326 smuggling-pattern
sweep is inapplicable. No tautology: the `SatisfiesB 4` example
has empty hypothesis context other than the `k` range, and its
conclusion is a four-armed equality chain that is not present in
any hypothesis. No identity proofs: `simp <;> norm_num` is a
substantive arithmetic computation.

## Dead ends

None. The cycle followed the strategy exactly; no path required
backtracking. The R1/R2 pre-flagged risks did not fire — the
literal pattern worked on first compile.

## Discovery

The cycle 326 / 327 direct-form pattern at `s ≤ 3` is **extremely
mechanical**: each ship is ~50 LOC, four arms of `simp +
Fin.sum_univ_<n> + norm_num`, no Aristotle needed, no LSP search
needed, no infrastructure to add. The mechanical-template
hypothesis is now confirmed across two cycles (326 Radau IA s=2,
327 Lobatto IIIB s=3). Future direct-form ships in cycles 328+
(Radau II s=2 D(s), Radau I s=2, Lobatto IIIC s=2 if it exists)
should follow the same template.

Specific observation: the negative-literal worry inside `!![...]`
matrix-row syntax was **unfounded**. `-(1/6)` parses cleanly as a
ℝ-valued matrix entry. The cycle 324 precedent (negative literals
in theorem statements) carries forward to matrix-literal entries
without modification. Future direct-form ships with mixed-sign A-
matrix entries can use `-(p/q)` verbatim without case-splitting or
`Matrix.of` fallback.

## Suggested next approach

The cycle 326 task results' Option 1 (this cycle) is now closed.
Cycle 328 should pick **one** of the following (all ~50 LOC
direct-form ships, mechanical template confirmed):

1. **Radau II `s = 2` direct form** (Butcher Table 344(II) p. 245,
   D(s) choice). Distinct from cycle 324's Radau **IIA** which
   uses the C(s) plain-collocation construction. The two should
   coincide on `b` and `c` but differ on `A`. Verify `c =
   (1/3, 1)`, `b = (3/4, 1/4)` (matches Radau IIA) and audit `A`
   against Butcher's printed table.
2. **Radau I `s = 2` direct form** (further small-`s` ladder
   fill, ~50 LOC). Plain Lagrange collocation matches Butcher
   per the cycle 326 audit math; cycle 326's collocation
   template *could* lift here, or the direct form ships as a
   ~50 LOC drop-in.
3. **Lobatto IIIC `s = 2` direct form** (Butcher Table 344(IV)
   p. 246). Per `ch03.txt:5224`, Lobatto IIIC = "reflections of
   Lobatto III". **Audit-first**: read the printed table from
   `ch03.txt` and confirm the value layout before writing Lean.

Recommendation: **Option 1 (Radau II s=2 direct form)** — closes
a meaningful gap in the §344 D(s)-vs-C(s) coverage matrix and is
the cycle 326 task results' first cycle-328 candidate. Cycle 328
should also explicitly document whether the D(s) and C(s) forms
coincide at `s = 2` (the cycle 324 ship already gives us the C(s)
form's `A`-matrix entries — if they agree with Butcher Table
344(II) p. 245's printed values, the D(s)-vs-C(s) distinction may
collapse at small `s`; if not, the divergence pattern matches
cycle 326's Radau IA story).

The "reflections of X" multi-cycle investigation
(`.prover-state/issues/radau_ia_collocation_divergence.md`)
remains deferred — no need to touch it in cycle 328.
