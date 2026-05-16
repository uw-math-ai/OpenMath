# Issue: Radau IA `s = 2` is not the plain collocation tableau

## Blocker

Cycle 326's strategy proposed shipping `butcherRadauIA_two : RKTableau 2`
as a mechanical port of cycle 324's Radau IIA `s = 2` template, where
the A-matrix is the plain Lagrange-collocation integral

```
A_{ij} = ∫₀^{c_i} L_j(x) dx
```

evaluated at the Radau I abscissae `(0, 2/3)`. The cycle 326 strategy
§D faithfulness audit flagged this as a potential definition-smuggling
risk and recommended verifying against Butcher's printed table before
committing.

The audit fired. **Radau IA at `s = 2` is NOT the plain collocation
tableau.**

## Context

### Butcher Table 344(I), p. 224 (verbatim from `extraction/raw_text/ch03.txt:5214`)

```
Table 344(I)    Methods in the Radau and Lobatto families

Name            Choice of b and c        Choice of A
Radau I         Radau I quadrature       C(s)
Radau IA        Radau I quadrature       The reflections of Radau II
Radau II        Radau II quadrature      D(s)
Radau IIA       Radau II quadrature      The reflections of Radau I
Lobatto III     Lobatto quadrature       C(s − 1), a1s = a2s = · · · = ass = 0
Lobatto IIIA    Lobatto quadrature       C(s)
Lobatto IIIB    Lobatto quadrature       D(s)
Lobatto IIIC    Lobatto quadrature       The reflections of Lobatto III
```

The entry for **Radau IA** explicitly specifies `Choice of A`: *"The
reflections of Radau II"*. This is **not** the plain collocation
formula `A_{ij} = ∫₀^{c_i} L_j(x) dx`.

### Butcher's printed Radau IA `s = 2` tableau (p. 225, ch03.txt:5274)

```
Radau IA       (s = 2, p = 3),
                                            0        1/4       -1/4
                                            2/3      1/4        5/12
                                                     1/4        3/4
```

So `c = (0, 2/3)`, `b = (1/4, 3/4)`,
`A = !![1/4, -1/4; 1/4, 5/12]`.

### Plain-collocation values at the same abscissae

Lagrange basis at `(0, 2/3)`:

* `L_0(x) = (x − 2/3) / (0 − 2/3) = 1 − (3/2)x`
* `L_1(x) = x / (2/3) = (3/2)x`

Plain collocation `A_{ij} = ∫₀^{c_i} L_j(x) dx`:

| `(i, j)` | Integral                                             | Value  |
|----------|------------------------------------------------------|--------|
| `(0, 0)` | `∫₀^0 (1 − 3x/2) dx`                                  | `0`    |
| `(0, 1)` | `∫₀^0 (3x/2) dx`                                      | `0`    |
| `(1, 0)` | `∫₀^{2/3} (1 − 3x/2) dx = 2/3 − (3/4)·(4/9) = 1/3`    | `1/3`  |
| `(1, 1)` | `∫₀^{2/3} (3x/2) dx = (3/4)·(4/9) = 1/3`              | `1/3`  |

So plain collocation gives row 0 `(0, 0)` and row 1 `(1/3, 1/3)`,
**not** Butcher's row 0 `(1/4, -1/4)` and row 1 `(1/4, 5/12)`.

### Both tableaux satisfy `C(1)` but differ on remaining degrees of freedom

`C(1)` (row sum equals `c`): both tableaux satisfy row 1 `1/4 +
5/12 = 8/12 + 5/12 - 3/12 = ... wait, 1/4 + 5/12 = 3/12 + 5/12 =
8/12 = 2/3 = c_1` ✓ for Butcher; `1/3 + 1/3 = 2/3 = c_1` ✓ for
collocation. Row 0 trivially satisfies `C(1)` for both (sum `0 =
c_0`). So both are valid RK tableaux at the prescribed abscissae;
they differ on what determines the remaining four entries.

## What was tried

1. Read `extraction/raw_text/ch03.txt:5214` (Table 344(I)) and
   `:5274` (printed Radau IA `s = 2` table).
2. Computed the Lagrange basis at `(0, 2/3)` and integrated.
3. Compared with Butcher's printed values; row 0 and row 1 both
   diverge.
4. Verified each of Butcher's row sums equals the corresponding
   abscissa, so the textbook values satisfy `C(1)` (sanity).
5. Examined the cycle 343 `RKTableau.reflection` definition
   (`OpenMath/Chapter3/Section343.lean:69`) which implements
   `â_{ij} = b_j − a_{ij}`, `b̂_j = b_j`, `ĉ_i = (∑_j b_j) − c_i`.
   Computed `(butcherRadauII s = 2).reflection`:
   * `b̂ = (3/4, 1/4)`
   * `ĉ = (2/3, 0)`
   * `Â = !![3/4 − 1/3, 1/4 − 0; 3/4 − 1/3, 1/4 − 0]
        = !![5/12, 1/4; 5/12, 1/4]`
   This does **not** match Butcher's Radau IA `s = 2` A-matrix
   either. Butcher's "reflections of Radau II" is therefore a more
   refined construction than the bare §343 reflection — it
   presumably also reorders the stages so that abscissae are
   increasing.

   Even with a stage swap, the reflected A-matrix
   `!![5/12, 1/4; 5/12, 1/4]` ≠ Butcher's `!![1/4, -1/4; 1/4, 5/12]`.
   So Butcher's "reflections of Radau II" is not exactly the §343
   reflection up to permutation either — there is some additional
   structure (sign convention or symplectic adjoint) that needs
   investigating.

## Possible solutions

### Option A — Pivot cycle 326 to a direct-form ship

Ship `butcherRadauIADirect_two : RKTableau 2` with Butcher's
printed values

```
c = (0, 2/3)
b = (1/4, 3/4)
A = !![1/4, -1/4; 1/4, 5/12]
```

as a *direct* `RKTableau` definition, with no claim that it comes
from collocation. Add a `SatisfiesB 3` non-vacuity example
(Radau IA achieves classical order `p = 2s − 1 = 3`, so `B(3)` is
maximal). Defer the collocation/reflection bridge to a future
cycle.

This is the cycle 326 plan executed. See cycle 326 task results.

### Option B — Build the reflection-with-permutation construction

Define `RKTableau.permute (σ : Equiv.Perm (Fin s)) (M : RKTableau s) :
RKTableau s` (apply a stage permutation), then prove that for
`s = 2` and the swap permutation `σ = swap 0 1`:

```
butcherRadauIA s = 2  ≡  (butcherRadauIIA s = 2).reflection.permute σ
```

This requires understanding Butcher's "reflections" terminology
more carefully — the discrepancy between the §343 `RKTableau.reflection`
output and Butcher's printed Radau IA values (after swap) indicates
either a different sign convention or that "reflections of
Radau II" specifically means "reflections of the underlying
**collocation matrix** of Radau II" rather than "reflections of
the Radau IIA tableau itself".

### Option C — Skip Radau IA, focus on other §344 deliverables

Stay with cycles 322 / 324 (Radau IIA `s = 1, 2`) and 323
(Lobatto IIIA `s = 2`) as the §344 §D anchor. Pursue Lobatto IIIA
`s = 3` (Simpson's rule, multi-cycle) or the Phase B.2 polynomial
exactness headline (`thm:344A` III, multi-cycle) instead. Note:
Lobatto IIIB `s = 2` is **not** available — Butcher line 5263
explicitly: *"we note that Lobatto IIIB with s = 2 does not exist"*.

## Decision (cycle 326)

Cycle 326 ships **Option A**: a direct-form Radau IA `s = 2`
tableau with the textbook values plus a `SatisfiesB 3` non-vacuity
example. This is the cleanest "small cycle" outcome that preserves
faithfulness — the values are exactly Butcher's printed Table 344(I)
entry, and the order-3 quadrature condition `B(3)` is proved
mechanically.

The collocation/reflection bridge (Option B) and the cycle 326
strategy's preferred path are deferred to a future cycle. The
planner should treat Option B as a non-trivial multi-cycle effort
that requires first formalising the "reflections of Radau II"
construction precisely (which the cycle 343 `RKTableau.reflection`
alone does not capture).

## Faithfulness note

The direct-form ship is **NOT** definition smuggling: the values
are exactly Butcher's printed table; no claim is made that the
A-matrix is derived from any specific construction. The
`SatisfiesB 3` example is doing real work — it verifies a
classical order condition at the textbook values.
