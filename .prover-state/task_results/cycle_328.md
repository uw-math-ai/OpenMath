# Cycle 328 Results

## Worked on
§344 Phase D.8: ship `butcherRadauIIDirect_two : RKTableau 2`, the D(s)
variant of Butcher's Radau II tableau at `s = 2`, plus `B(3)` and
`D(2)` non-vacuity witnesses.

## Approach

### §A. Audit (mandatory pre-write step, per cycle 326/327 protocol)

Grepped `extraction/raw_text/ch03.txt` for `Radau II` and located
Butcher's printed Table 344(II) at lines 5284-5289:

```
Radau II       (s = 2, p = 3),
                                                      1        1
                                                      3        3       0
                                                      1        1       0
                                                               3       1
                                                               4       4
```

Parsing the column layout (`c | A` on top, `b` row at bottom):

- **c**: `c₁ = 1/3, c₂ = 1`
- **A** row 1: `A₁₁ = 1/3, A₁₂ = 0`
- **A** row 2: `A₂₁ = 1, A₂₂ = 0`
- **b**: `b₁ = 3/4, b₂ = 1/4`

Cross-checked the pattern against Radau II at `s = 3`
(`ch03.txt:5339-5352`) where the last column of `A` is also all
zeros, confirming the D(s)-recipe signature: `c_s = 1 ⇒ A_{j,s} = 0`
for every row `j`.

### §B. Divergence verification

Cycle 324's `butcherRadauIIA_two` has `A = !![5/12, -(1/12); 3/4, 1/4]`.
The audited Radau II A-matrix `!![1/3, 0; 1, 0]` differs in every
entry. `b` and `c` agree (both come from the Radau II quadrature).
So **Radau II ≠ Radau IIA at `s = 2`** — the §G R1 risk (coincidence)
did not materialise.

Hand-checked D(2) on paper for the audited values:

* `(k=1, j=0)`: LHS `(3/4)(1/3) + (1/4)(1) = 1/2`, RHS `(3/4)(2/3) = 1/2` ✓
* `(k=1, j=1)`: LHS `0 + 0 = 0`, RHS `(1/4)(0) = 0` ✓
* `(k=2, j=0)`: LHS `(3/4)(1/3)(1/3) + (1/4)(1)(1) = 1/3`, RHS `(3/8)(8/9) = 1/3` ✓
* `(k=2, j=1)`: LHS `0 + 0 = 0`, RHS `(1/8)(0) = 0` ✓

This confirms the printed table really does satisfy D(2), and that
the D(s)-vs-IIA divergence at `s = 2` is non-trivial.

### §C. Lean implementation

Shipped three items at the end of `OpenMath/Chapter3/Section344.lean`
(lines 1807-1888), following the cycle 326/327 small-cycle template
literally:

1. **`butcherRadauIIDirect_two : RKTableau 2`** — direct-form
   declaration with the audited values inline.
2. **`example : butcherRadauIIDirect_two.SatisfiesB 3`** — three-arm
   `interval_cases k` + `simp [_, Fin.sum_univ_two]; norm_num` close,
   reusing cycle 324's exact recipe.
3. **`example : butcherRadauIIDirect_two.SatisfiesD 2`** — D(2)
   certificate (the planner's §C.4 optional stretch goal). Four-arm
   `fin_cases j <;> interval_cases k <;> simp [_, Fin.sum_univ_two]
   <;> norm_num` close.

Plus a `D.8` section header docstring documenting the audit,
divergence, and deferral of the abstract D(s) construction.

## Result

**SUCCESS.** All three deliverables compile cleanly.

* `lake env lean OpenMath/Chapter3/Section344.lean` → exit 0
* `lake build OpenMath.Chapter3.Section344` → exit 0 (5.3s rebuild,
  no errors, only pre-existing simp-arg-linter warnings on §342)
* `lake env lean OpenMath/Chapter3.lean` → exit 0
* `#print axioms OpenMath.Chapter3.Section344.butcherRadauIIDirect_two`
  → `[propext, Classical.choice, Quot.sound]` (axiom-clean)
* Sorry count: 0 (stays clean).
* Section344.lean LOC: 1807 → 1883 (+76, within the planner's
  ~50 LOC budget allowing for the optional D(2) stretch).

The `D(2)` certificate distinguishes this tableau from the cycle-324
IIA variant: `butcherRadauIIA_two` satisfies `C(s)` (by construction
from the Lagrange collocation A-matrix at the Radau II abscissae)
but not D(s) in general at `s ≥ 2`.

## Faithfulness check

### `def butcherRadauIIDirect_two : RKTableau 2`

* **Entity ID**: no per-entity JSON exists for this concept (the
  extractor only emitted `thm:344A`). The defining content is
  Butcher Table 344(II) p. 245, `ch03.txt:5284-5289`, quoted in the
  task results §A above.
* **Textbook statement (quoted from raw text)**:
  ```
  Radau II       (s = 2, p = 3),
                  c=1/3   A row=(1/3, 0)
                  c=1     A row=(1, 0)
                          b=(3/4, 1/4)
  ```
* **Lean statement captures**: same content. `A := !![1/3, 0; 1, 0]`,
  `b := ![3/4, 1/4]`, `c := ![1/3, 1]` agree entry-for-entry with
  Butcher's printed values. No equivalent reformulation; printed
  values copied verbatim.

### `example : butcherRadauIIDirect_two.SatisfiesB 3`

* **Source**: Butcher Table 344(I) p. 244 column 3 lists Radau II's
  classical attainable order as `p = 2s − 1`; at `s = 2` this gives
  `p = 3`. The B(η) quadrature condition is at `η = p = 3`.
* **Lean statement captures**: same content. `M.SatisfiesB 3` unfolds
  to `∀ k ∈ {1,2,3}, ∑ⱼ bⱼ · cⱼ^(k-1) = 1/k`, which is the standard
  order-3 quadrature exactness condition for `b, c`. Since Radau II
  and Radau IIA share `b` and `c`, the B(3) arithmetic is identical
  to cycle 324's `butcherRadauIIA_two.SatisfiesB 3` example.

### `example : butcherRadauIIDirect_two.SatisfiesD 2`

* **Source**: Butcher Table 344(I) p. 244 row "Radau II" specifies
  `Choice of A = D(s)`, the matrix satisfying the D(s) simplifying
  assumption (defined in `OpenMath/Chapter3/Section321.lean:112` as
  `∀ j k, ∑ᵢ bᵢ · cᵢ^(k-1) · Aᵢⱼ = (bⱼ/k)(1 - cⱼ^k)`). At `s = 2`
  this is D(2).
* **Lean statement captures**: same content. This certificate is the
  *defining* property of the D(s) variant — it's what makes Radau II
  not equal to Radau IIA at `s ≥ 2`. The proof discharges the
  4-element grid of `(j, k) ∈ {0,1} × {1,2}` cases by mechanical
  `norm_num`.

### Faithfulness checklist (per CLAUDE.md):

* **Tautology check**: ✓ Neither example's conclusion appears as a
  hypothesis (no hypotheses at all besides `k` / `j` indices and
  bounds).
* **Identity check**: ✓ Both proofs decompose by `interval_cases` /
  `fin_cases` and discharge via `simp + norm_num` — no `exact h`
  vacuous re-exports.
* **Definition smuggling**: ✓ `RKTableau` is the existing
  `Section312.RKTableau` structure (A, b, c only — no Prop fields).
  No structures were introduced this cycle.
* **Hypothesis strength**: ✓ No hypotheses besides the standard
  `1 ≤ k`, `k ≤ η` bounds inside the SatisfiesB / SatisfiesD
  `∀`-binders.
* **Absent theorem**: ✓ The §D.8 docstring references
  `butcherRadauIIA_two` (cycle 324, exists at line 1577) and Butcher
  table line numbers; no promised-but-missing content.

## Dead ends

None. The audit-from-printed-table path was mechanical; the
divergence from Radau IIA was anticipated by the planner (§B
"more interesting outcome") and confirmed in ~5 min of grepping.

The single non-trivial choice was the tactic recipe for D(2): the
four-case `fin_cases j <;> interval_cases k <;> simp <;> norm_num`
chain closes all four arms uniformly because the A-matrix has zero
columns (column 2 = 0) and the `c, c^2` powers reduce cleanly. No
need to split by `j` first; the unified chain works.

## Discovery

1. **D(s)-recipe signature pattern.** When `c_s = 1` (as in Radau II
   and Lobatto-family methods), the D(s) construction forces the
   last column of `A` to zero. This was visible in both Butcher's
   `s = 2` and `s = 3` Radau II tables and is now explicit in the
   §D.8 docstring. Future cycles touching Lobatto IIIB / IIIC
   `s = 2` should expect the same "zero last column" pattern.

2. **`fin_cases j <;> interval_cases k <;> ...` works uniformly for
   D(2) at `s = 2`.** This composite four-arm close (cycle 328 §C.3)
   is now a confirmed mechanical template for D(η) certificates at
   small stage count, complementing cycle 324's `interval_cases k`
   template for B(η).

3. **Cycle 326's audit-first protocol caught a real divergence
   *again*.** First Radau IA at s=2 (cycle 326), now Radau II vs
   IIA at s=2 (this cycle). Two-for-two — the audit step is
   load-bearing for the direct-form ship workflow and should remain
   mandatory.

## Suggested next approach

The planner's §I outlook (Radau I `s = 2`, Lobatto IIIC `s = 2`,
Lobatto IIIA `s = 3`) is well-positioned. Concrete suggestions:

* **Cycle 329 — Radau I `s = 2` direct form.** Per Table 344(I) p. 244,
  Radau I uses `Choice of A = C(s)`. The audit-first protocol should
  run on Butcher's printed Radau I `s = 2` table (`ch03.txt` around
  the cycles 325/326 region) and verify whether it agrees with plain
  Lagrange collocation at the Radau I abscissae `(0, 2/3)`. Note
  this is the C(s)-vs-collocation question, NOT the
  reflections-of-Radau-II question (which is cycle 326's already-
  shipped Radau IA territory). Likely outcome: C(s) at `s = 2`
  coincides with plain collocation when the abscissae include 0,
  but the audit is the authoritative answer.

* **Cycle 330 — Lobatto IIIC `s = 2` direct form.** Per
  `ch03.txt:5224`, Lobatto IIIC uses `Choice of A = "the reflections
  of Lobatto III"`. Audit-from-printed-table is mechanical; expect
  a likely-divergent A-matrix from Lobatto IIIA's trapezoidal form
  (cycle 323) since the C(s)-vs-reflection question is the same
  flavour as cycles 326 and 328.

* **Cycle 331+ — pivot or push s = 3.** If the cycle 329/330 direct
  ships continue smoothly, consider either (a) `butcherRadauIDirect_three`
  / `butcherRadauIIDirect_three` (printed at `ch03.txt:5307` and
  `ch03.txt:5339` — non-trivial `√6` arithmetic but mechanically
  feasible per the planner's note), or (b) pivot to a fresh
  Chapter 5 entity per the cycle 327 outlook.

The mechanical-template hypothesis is now confirmed across cycles
326, 327, and 328 — three consecutive small-`s` direct-form ships
with audit-first protocol. The pattern is robust.
