# Issue: `stabilityMatrix_quadForm_eq_neg_integral` needs a safe low-degree/top-degree split

## Blocker
The new live helper for mixed monomials is in place, but the current proof plan
for `stabilityMatrix_quadForm_eq_neg_integral` still has a gap before the
top-degree defect computation:

- the theorem statement allows `q.natDegree < s - 1`,
- the planner sketch subtracts `Polynomial.C q.leadingCoeff * Polynomial.X ^ (s - 1)`,
- that subtraction only cancels the degree-`s - 1` term when `q.natDegree = s - 1`.

For genuine low-degree inputs, `q.leadingCoeff` lives in a lower degree, so

```lean
r := q - Polynomial.C q.leadingCoeff * Polynomial.X ^ (s - 1)
```

does **not** satisfy `r.natDegree < s - 1` in general.

## Context
- Live file: `OpenMath/CollocationAlgStability.lean`
- Current target:

```lean
lemma stabilityMatrix_quadForm_eq_neg_integral
    (t : ButcherTableau s) (hcoll : t.IsCollocation) (hAlg : t.IsAlgStable)
    (q : ℝ[X]) (hq : q.natDegree ≤ s - 1)
    (hzero : ∀ r : ℝ[X], r.natDegree < s - 1 →
      ∫ x in (0 : ℝ)..1, ((nodePoly t) * r).eval x = 0) :
    let v : Fin s → ℝ := fun i => q.eval (t.c i)
    ∑ i : Fin s, ∑ j : Fin s, v i * t.algStabMatrix i j * v j =
      -2 * (q.leadingCoeff / (s : ℝ)) *
        ∫ x in (0 : ℝ)..1, ((nodePoly t) * q).eval x
```

- New live infrastructure from this cycle:

```lean
private lemma algStabMatrix_monomial_bilinear_zero
    ...
    (hmn : m + n + 2 ≤ 2 * s - 1) :
    ...
```

## What was tried
- Implemented the mixed-monomial vanishing route directly from the live `C`,
  `D`, and `B(2 * s - 1)` infrastructure.
- While proving that helper, found that the planner’s suggested Nat bound
  `m + n ≤ 2 * s - 3` is not safe in Lean at `s = 1` because subtraction is
  truncated. The private helper was strengthened to the nontruncated form
  actually needed by the proof:

```lean
m + n + 2 ≤ 2 * s - 1
```

- Rechecked that the target file still compiles with only the four intended
  sorrys.
- Started the main theorem reduction and hit the `q.leadingCoeff`/low-degree
  mismatch above.

## Possible solutions
- Split the theorem into two branches:
  - `q.natDegree < s - 1`: prove both sides are zero.
  - `q.natDegree = s - 1`: use the top-term subtraction
    `q - Polynomial.C q.leadingCoeff * Polynomial.X ^ (s - 1)`.
- For the low-degree branch, add a theorem-local polynomial bilinear helper:

```lean
∑ i, ∑ j, p.eval (t.c i) * t.algStabMatrix i j * r.eval (t.c j) = 0
```

when `p.natDegree < s`, `r.natDegree < s`, and
`p.natDegree + r.natDegree + 2 ≤ 2 * s - 1`, proved by expanding `p` and `r`
into monomials and applying `algStabMatrix_monomial_bilinear_zero`.
- In the top-degree branch, compute the remaining defect using
  `p := (nodePoly t) * Polynomial.X ^ (s - 1)`:
  - `quadEvalPoly t p = 0` by node evaluation,
  - `polyMomentN (2 * s) p = ∫ ((nodePoly t) * X^(s - 1)).eval`,
  - the only missing contribution is the coefficient of `X^(2 * s - 1)`,
    which is `1` because `nodePoly t` is monic.
