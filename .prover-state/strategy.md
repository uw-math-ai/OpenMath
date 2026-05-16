# Cycle 330 Strategy — §344 Phase D.10: Lobatto IIIC `s = 2` direct-form `RKTableau`

## A. Headline target

Ship `butcherLobattoIIICDirect_two : RKTableau 2` (the "reflections of
Lobatto III" variant per Butcher Table 344(IV)) plus a `SatisfiesB 2`
non-vacuity witness, all inline in
`OpenMath/Chapter3/Section344.lean` immediately after cycle 329's
`butcherRadauIDirect_two` block.

This is the 5th cycle in the small-`s` direct-form ladder and the
**4th divergent audit outcome** (after cycles 326 / 327 / 328 each
diverged from plain Lagrange collocation; cycle 329 was the unique
coincident outcome). The mechanical template is now five-cycle stable.

## B. Pre-write audit (DONE — values verified by the planner)

Butcher Table 344(IV) line 5389–5396 of `extraction/raw_text/ch03.txt`
prints the Lobatto IIIC `s = 2, p = 2` table as:

```
                    0       1/2     -1/2
                    1       1/2      1/2
                            1/2      1/2
```

Parsed:

```
c = ![0, 1]
b = ![1/2, 1/2]
A = !![1/2, -1/2; 1/2, 1/2]
```

### B.1 — Audit step (Path α): plain Lagrange collocation at `c = (0, 1)`

`L_0(x) = (x - 1) / (0 - 1) = 1 - x`,  `L_1(x) = x / 1 = x`. Then

| `(i, j)` | `∫₀^{c_i} L_j(x) dx` | Value |
|----------|-----------------------|-------|
| `(0, 0)` | `∫₀^0 (1-x) dx`       | `0`   |
| `(0, 1)` | `∫₀^0 x dx`           | `0`   |
| `(1, 0)` | `∫₀^1 (1-x) dx`       | `1/2` |
| `(1, 1)` | `∫₀^1 x dx`           | `1/2` |

Plain collocation gives `!![0, 0; 1/2, 1/2]`. Butcher's printed
Lobatto IIIC gives `!![1/2, -1/2; 1/2, 1/2]`. **DIVERGENT.** Row 0
differs entry-for-entry; row 1 happens to coincide. This matches
the cycle 326 / 327 / 328 divergence pattern (reflection variants
do NOT come from plain collocation), confirming cycle 329's
classification of the C(s) row as the unique liftable row.

### B.2 — Certificate selection: B(2) only

Numerical verification of which `SatisfiesX` certificates hold
(using the SatisfiesB / SatisfiesC / SatisfiesD definitions at
`OpenMath/Chapter3/Section321.lean:89–115`):

* **B(2)**: `∑ b_i c_i^0 = 1/2 + 1/2 = 1 = 1/1` ✓;
  `∑ b_i c_i^1 = 0 + 1/2 = 1/2 = 1/2` ✓. **B(2) HOLDS.** B(3) fails
  (`∑ b_i c_i^2 = 0 + 1/2 = 1/2 ≠ 1/3`), matching the printed `p = 2`.
* **C(2)**: at `(i=0, k=2)`, `∑ A_{0,j} c_j^1 = 0 + (-1/2)·1 = -1/2`
  but RHS `c_0^2/2 = 0`. **C(2) FAILS.**
* **D(2)**: at `(j=1, k=2)`,
  `∑ b_i c_i^1 A_{i,1} = b_0·0·A_{0,1} + b_1·1·A_{1,1} = 0 + 1/2·1/2 = 1/4`
  but RHS `(b_1/2)(1 - c_1^2) = 1/4·0 = 0`. **D(2) FAILS.**

So **B(2) is the only non-trivial certificate available**. C(1) and
D(1) both hold trivially but they're weak — at order ≤ 1, every
reasonable Lobatto tableau satisfies them. Per cycle 326 (Radau IA
direct, which was also a reflection variant), shipping just
`B(p)` is the appropriate non-vacuity bar for reflection variants.

## C. Concrete deliverables

### C.1 — `def butcherLobattoIIICDirect_two : RKTableau 2`

Located immediately after cycle 329's `butcherRadauIDirect_two`
block (line ~1957 in current HEAD), inside the existing
`namespace OpenMath.Chapter3.Section344`. Use the cycle 329 template
verbatim with substitutions `Radau I` → `Lobatto IIIC`,
`c = ![0, 2/3]` → `c = ![0, 1]`, `b = ![1/4, 3/4]` → `b = ![1/2, 1/2]`,
`A = !![0, 0; 1/3, 1/3]` → `A = !![1/2, -1/2; 1/2, 1/2]`.

The docstring should:
1. Cite Butcher Table 344(IV) p. 246, raw text `ch03.txt:5389–5396`.
2. State `(s = 2, p = 2)`, the "reflections of Lobatto III" variant
   per `ch03.txt:5224`.
3. Note the audit outcome: **DIVERGES** from plain Lagrange
   collocation (`A` row 0 disagrees: printed `(1/2, -1/2)` vs
   collocation `(0, 0)`).
4. Cross-reference cycle 326's `radau_ia_collocation_divergence.md`
   for the broader pattern of reflection variants not coming from
   plain collocation.

### C.2 — `example : butcherLobattoIIICDirect_two.SatisfiesB 2`

Mechanical two-arm `interval_cases k; simp [butcherLobattoIIICDirect_two,
Fin.sum_univ_two]; norm_num` close. Exactly mirrors cycle 326's
`butcherRadauIADirect_two.SatisfiesB 3` example (which used three
arms for B(3)); here we have two arms for B(2).

Pre-write arithmetic spot-check (DONE in §B.2):
- `k = 1`: `1/2·1 + 1/2·1 = 1 = 1/1` ✓
- `k = 2`: `1/2·0 + 1/2·1 = 1/2 = 1/2` ✓

(Recall the SatisfiesB sum is `∑ b_i · c_i^(k-1)`; for `k = 2`
that's `b_0·c_0^1 + b_1·c_1^1 = 0 + 1/2 = 1/2`.)

### C.3 — Faithfulness check anchors

For the cycle results' faithfulness section:

* Entity ID: no per-entity JSON exists for `def:Lobatto_IIIC_s2`
  (extractor only emits `thm:344A` for §344). Source is Butcher
  Table 344(IV) p. 246, `ch03.txt:5389–5396`. Quote these line
  numbers in the docstring.
* Lean values: entry-for-entry copy of the printed table.
* Lean statement captures: **same content**.
* Audit divergence (DOC NOTE only, not a faithfulness issue):
  the printed A-matrix is NOT the plain Lagrange-collocation
  matrix at `(0, 1)`. Document in the docstring; do NOT attempt
  to prove a coincidence theorem (none exists).

## D. What NOT to try

1. **Do NOT attempt collocation-coincidence formalisation.** The
   audit shows divergence; trying to prove
   `butcherLobattoIIICDirect_two.A = butcherLobattoIIIC_collocationA_two`
   would fail at row 0 entry-for-entry. The collocation/reflection
   bridge for Lobatto IIIC is multi-cycle work (requires Butcher's
   "reflections of Lobatto III" precise meaning — see cycle 326's
   `radau_ia_collocation_divergence.md` for the precedent that bare
   `RKTableau.reflection` does not reproduce these values).
2. **Do NOT ship `SatisfiesC 2` or `SatisfiesD 2` examples.** Both
   provably FAIL per §B.2 above. Pre-write arithmetic counter-
   examples are already noted; do not waste cycle time discovering
   this inside Lean.
3. **Do NOT ship `SatisfiesC 1` or `SatisfiesD 1` as bonus
   non-vacuity.** They hold but are weak. Cycle 326 precedent: for
   reflection variants, `SatisfiesB p` alone is the appropriate
   non-vacuity bar.
4. **Do NOT submit to Aristotle.** Same reasoning as cycle 329:
   the `B(2)` mechanical close is a textbook two-arm `simp +
   norm_num` pattern lifted verbatim from cycles 326 / 327 / 328 /
   329; it will fire on the first compile. Aristotle would be pure
   overhead for a ~50 LOC mechanical ship.
5. **Do NOT raise `maxHeartbeats`.** The single `simp` on a 2×2
   matrix with `Fin.sum_univ_two` is trivial.
6. **Do NOT introduce a new `Mathlib.Tactic.*` import.** All
   needed tactics (`simp`, `norm_num`, `interval_cases`,
   `Fin.sum_univ_two`) are already in scope via Section344's
   existing imports.
7. **Do NOT pursue the cycle 329 §I option 2** (collocation lift
   for Radau I `s = 2`). That's a ~150 LOC medium-cycle deliverable;
   defer to cycle 331+.
8. **Do NOT attempt Lobatto IIIB `s = 2`.** Per `ch03.txt:5263`,
   Lobatto IIIB at `s = 2` does NOT exist (cycle 327's `s = 3`
   ship is the canonical entry point for that family).

## E. Verification checklist (do these in order)

After writing the D.10 block:

1. `lake env lean OpenMath/Chapter3/Section344.lean` — expect exit 0,
   silent (no warnings / errors).
2. `lake build OpenMath.Chapter3.Section344` — expect ✔ all jobs in
   <30s warm rebuild.
3. `grep -c sorry OpenMath/Chapter3/Section344.lean` — expect 0.
4. `#print axioms OpenMath.Chapter3.Section344.butcherLobattoIIICDirect_two`
   — expect `[propext, Classical.choice, Quot.sound]`.
5. Verify the aggregator `OpenMath/Chapter3.lean` still builds (warm
   rebuild ≤10s).

If any check fails, diagnose minimally (most likely culprits:
typo'd matrix value, missing parenthesis on `1/2`, mistaken
exponent in `B(2)` example). Do not rewrite the strategy.

## F. LOC and time budget

Cycle 329's D.9 block was 74 LOC (def + two examples + docstrings).
This cycle's D.10 block should be ~50 LOC because only one example
is needed (B(2) instead of B(3) + C(2)/D(2)). Breakdown:

- Docstring: ~25 LOC.
- Def body: ~5 LOC.
- B(2) example: ~15 LOC (two arms instead of three).

Time budget per cycle 329's experience: ~5 min docstring + parsing,
~10 min Lean writeup, ~5 min build + axiom check + faithfulness
section. Total ≤30 min focused work.

## G. Faithfulness divergence to record

Update the cycle 330 task results §"Faithfulness check" section to
note:

* The five direct-form ships through cycle 330 form a clean pattern:
  four reflection-style / D(s) variants diverge from plain
  collocation (cycles 326 Radau IA, 327 Lobatto IIIB, 328 Radau II
  D(s), 330 Lobatto IIIC) and only the C(s) variant of Radau I at
  `s = 2` coincides (cycle 329).
* `plan.md` row change: just bump the §344 update paragraph for
  `thm:344A` to add a "**Cycle 330 ships Phase D.10**: Lobatto IIIC
  `s = 2` direct-form ..." sentence after the existing cycle 329
  block. Status stays `[~]`.
* `lean_status.json` `thm:344A` row: bump `cycle` to 330 with a
  brief note about the D.10 Lobatto IIIC ship; status stays
  `partial`.

## H. Cycle 331+ outlook (informational, NOT this cycle's work)

After cycle 330 lands Lobatto IIIC `s = 2`, the small-`s` direct-form
ladder is approximately saturated for `s ≤ 2` (cycles 322, 323, 324,
325, 326, 328, 329, 330 each shipped one direct-form RKTableau at
`s ∈ {1, 2}`). Cycle 331+ planner choices, ranked:

1. **Lobatto III `s = 2` (unsuffixed family)** — `ch03.txt:5372`
   confirms a printed table at `p = 2`; A-matrix per `ch03.txt:5221`
   is `C(s−1)` with last-column zeros. This would be a 6th
   direct-form ship; ~50 LOC. Audit outcome uncertain (last-column
   zero implies divergence from plain collocation but a specific
   variant of it).
2. **Collocation-coincidence cross-check for Radau I `s = 2`**
   (the cycle 329 §I option 2): build `butcherRadauI_collocationA_two`
   and prove `butcherRadauIDirect_two.A = _collocationA_two` as
   the first formal collocation/printed-table bridge. ~150 LOC.
3. **`butcherRadauIDirect_three` (Radau I `s = 3`)** — defer.
   `ch03.txt:5307` involves `√6` arithmetic; multi-cycle.
4. **Lobatto IIIA `s = 3` (Simpson's rule)** — defer per cycle
   323 outlook.
5. **Pivot to fresh Chapter 5 entity** if the §344 D ladder is
   approaching diminishing returns. Candidates: `def:451A` G-stable
   companion, `def:422B`, `def:442A`, `thm:535A`, `thm:541A`.

Cycle 331 planner should choose based on whether to saturate the
small-`s` ladder (option 1) or pivot (option 5).

## I. Summary

**Single deliverable**: ship `butcherLobattoIIICDirect_two : RKTableau 2`
with one `SatisfiesB 2` non-vacuity example. ~50 LOC, axiom-clean,
sorry count stays 0. Mechanical lift of cycle 329's template with
the C(2) arm dropped (Lobatto IIIC at `s = 2` provably fails C(2)
and D(2) per §B.2). All audit work is pre-done in §B; the worker
just writes and verifies.
