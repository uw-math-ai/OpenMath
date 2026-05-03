# Issue: Cycle 692 redefinition of `activeStabilityPolyPoly` breaks the BDF→`stabilityPolyPoly` bridges

## Blocker

The cycle 692 strategy directs Step 2 to re-prove

```
activeStabilityPolyPoly m z = m.stabilityPolyPoly z
```

under BDF after redefining

```lean
activeStabilityPolyPoly m z := (1 - z β_last) • (toGLM_stabilityMatrixPY m 0).charpoly
```

(i.e. `D • PY(0).charpoly`).

That identity is **mathematically false** in general. With this
redefinition, `activeStabilityPolyPoly = stabilityPolyPoly` no longer
holds under BDF — they differ by a non-zero correction proportional to
`z · β_last`.

## Counterexample (s = 1, backward Euler)

Coefficients: `α = (-1, 1)`, `β = (0, 1)`. So `D = 1 - z`.

* `m.stabilityPolyPoly z = -1 + (1-z) X = D · X − 1`.
* `(toGLM_stabilityMatrixPY m 0).charpoly = X − 1` (z = 0 ⇒ no `1/D`
  rescaling, bottom row carries `-α(0) = 1`).
* `D • PY(0).charpoly = (1-z)(X-1) = D · X − D`.
* Difference: `D • PY(0).charpoly − stabilityPolyPoly z = (D · X − D) − (D · X − 1) = 1 − D = z β_last = z`.

At `z = 0.5` for instance, `D • PY(0).charpoly = 0.5 X − 0.5` while
`stabilityPolyPoly z = 0.5 X − 1`. They disagree by `0.5`.

## General algebra

Unconditionally (no BDF needed),
`(toGLM_stabilityMatrixPY m 0).charpoly = X^s + ∑_{l : Fin s} C(α(castSucc l)) X^l`
(specialise the cycle-690 lemma `toGLM_stabilityMatrixPY_charpoly` at
`z = 0`, where the `1/D` denominator is `1`). Multiplying by `D`:

```
D • PY(0).charpoly = D · X^s + ∑_l C(D · α(castSucc l)) X^l
```

Under BDF, `m.stabilityPolyPoly z = D · X^s + ∑_l C(α(castSucc l)) X^l`
(the j = last term contributes `C(1 - z β_last) X^s = C D · X^s`; the
other terms collapse because `β(castSucc l) = 0`).

Difference:

```
D • PY(0).charpoly − stabilityPolyPoly z = ∑_l C((D - 1) α(castSucc l)) X^l
                                          = -C(z β_last) · ∑_l C(α(castSucc l)) X^l
```

This vanishes **only** when `z β_last = 0`, i.e. at `z = 0` or for a
hypothetical "BDF" with `β_last = 0` (which would violate the LMM
non-degeneracy of the implicit step).

Cycle 692 strategy's Step 3 inherits the same gap: it asserts
`D · charpoly = X^s · activeStabilityPolyPoly` under BDF, which would
force `D • PY(0).charpoly = D • PY(z).charpoly` under BDF (they are
equal up to the `1/D` rescaling of the bottom row, so this fails for
the same reason).

## Context

This file documents why cycle 692 deviated from the strategy's Steps 2
and 3. The redefinition (Step 1) and the general headline (Step 4)
were landed correctly. The two BDF lemmas at the original lines
449–475 (`activeStabilityPolyPoly_eq_stabilityPolyPoly_of_bdf` and
`D_mul_toGLM_charpoly_eq_X_pow_mul_active_of_bdf`) became false under
the redefinition and were replaced with a single TRUE BDF lemma using
`stabilityPolyPoly` directly:

```
D_mul_toGLM_charpoly_eq_X_pow_mul_stabilityPolyPoly_of_bdf:
  C D · charpoly = X^s · m.stabilityPolyPoly z   (BDF)
```

This is the natural BDF-flavoured headline (the textbook quantity is
`stabilityPolyPoly`, not the `PY(0)`-flavoured active polynomial), and
it is the form downstream callers (notably the §521 BDF A-stability
transport `toGLM_isAStable_of_bdf`) actually want.

## What was tried

Verified with two independent calculations (s = 1 BE concrete, and
general algebraic expansion using
`toGLM_stabilityMatrixPY_charpoly_of_bdf` at `z = 0`) that
`D • PY(0).charpoly ≠ stabilityPolyPoly z` under BDF.

Tested cycle-692 Step 4 (general headline) compiles via the cycle 690
lemma plus `Polynomial.smul_eq_C_mul`; lands sorry-free.

## Possible solutions

For a future cycle that needs to bridge the new `activeStabilityPolyPoly`
to `stabilityPolyPoly`:

1. **State the corrected BDF identity**:

   ```
   activeStabilityPolyPoly m z = m.stabilityPolyPoly z
     − Polynomial.C (z * β_last)
       * ∑ l : Fin s, Polynomial.C (α(castSucc l)) * X^l   (BDF)
   ```

   Provable by expanding `toGLM_stabilityMatrixPY_charpoly` at `z = 0`,
   computing `D • PY(0).charpoly` and `stabilityPolyPoly z` term-by-term
   under BDF, and matching coefficients.

2. **Compute `rowYQuot` under BDF**: under BDF, the residual in
   `D_mul_toGLM_charpoly_eq_X_pow_mul_active_plus_residual` collapses
   to `rowYQuot · X^s · C(z β_last)` (the `rowFAlphaPoly` and
   `rowFBetaPoly` terms vanish because `β(castSucc l) = 0` ⇒
   `rowFBetaPoly = 0`, then `rowFAlphaPoly = 0` follows from
   `toGLM_stabilityCharpolyRowF_of_bdf`). Combined with the cycle 643
   identity `D · charpoly = X^s · stabilityPolyPoly` (BDF), this
   yields

   ```
   rowYQuot · C(z β_last) = activeStabilityPolyPoly − stabilityPolyPoly  (BDF)
   ```

   which by (1) reduces to
   `rowYQuot = -∑_l C(α(castSucc l)) · X^l (mod C(z β_last))` under
   BDF — interesting but not the cheap path.

3. **Leave the bridge implicit**: the §521 iff bridge target
   (`LMM.toGLM_isAStable_iff`) needs degree counting and unit-disk
   evaluation of `D · charpoly = X^s · activeStabilityPolyPoly − residual`,
   which doesn't require a direct `activeStabilityPolyPoly = stabilityPolyPoly`
   identity.
