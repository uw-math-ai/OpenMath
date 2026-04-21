# Issue: generic Padé leading coefficient for `padeR * exp (-z)` is still unproved

## Blocker
The remaining honest seam is the explicit first nonzero term of
`φ_{n,d}(z) = padeR n d z * exp (-z)` near `z = 0`.

The denominator-control step is now available locally:
- `padeQ_continuous`
- `padeQ_nonzero_near_zero`
- `padeQ_inv_norm_le_two_near_zero`

So the blocker is no longer local invertibility of `padeQ`. The missing theorem is
the coefficient/sign statement needed before the generic direction lemmas
`arrow_down_of_pos_errorConst` and `arrow_down_of_neg_errorConst_odd` can fire.

## Context
The exact theorem I tried to force into shape is the cycle-296 scratch target:

```lean
def padePhiErrorConst (n d : ℕ) : ℝ :=
  ((-1 : ℝ) ^ d) * ((n.factorial : ℝ) * (d.factorial : ℝ)) /
    (((n + d).factorial : ℝ) * ((n + d + 1).factorial : ℝ))

theorem padeR_exp_neg_leading_term
    (n d : ℕ) :
    ∃ g : ℂ → ℂ, ∀ z : ℂ,
      padeR n d z * exp (-z) -
        (1 - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1)) =
      z ^ (n + d + 2) * g z
```

This is the coefficient theorem that would make the sign of the first error term
explicit. After that, the next honest target is the local norm bound in the exact
shape expected by `OpenMath/OrderStars.lean`:

```lean
∀ z : ℂ, ‖z‖ < δ₀ →
  ‖padeR n d z * exp (-z) -
      (1 - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1))‖
    ≤ K * ‖z‖ ^ (n + d + 2)
```

## What was tried
- Re-triaged the nine ready Aristotle bundles listed by the planner. All were rejected.
  The failure modes were exactly the expected ones: recreating `OpenMath/PadeOrderStars.lean`,
  changing branch/direction interfaces, or attacking the already-closed support layer.
- Wrote a focused Aristotle batch in `.prover-state/aristotle/cycle_296/`:
  - `01_pade_defect_leading_coeff.lean`
  - `02_pade_expTaylor_to_exp_local_bound.lean`
  - `03_padeQ_nonzero_near_zero.lean`
  - `04_padeR_exists_downArrowDir.lean`
  - `05_padeR_down_branch_from_direction.lean`
- Waited once for 30 minutes, then refreshed once only.
- Cycle-296 Aristotle results:
  - `dc182a12...` (`01`) came back `COMPLETE_WITH_ERRORS` but was invalid. It rebuilt
    `OpenMath/PadeOrderStars.lean` and "proved" the target by defining the remainder as
    the full left-hand side divided by `z^(n+d+2)`, with no genuine coefficient computation.
  - `c14a5101...` (`03`) came back `COMPLETE`. It also rebuilt `OpenMath/PadeOrderStars.lean`,
    so the bundle was rejected as-is, but the proof idea for local denominator control was honest.
    I transplanted that idea manually into live `OpenMath/Pade.lean`.
  - `e9c89bfa...`, `6ebe0669...`, and `00735cff...` were still `IN_PROGRESS` after the single
    mandated refresh, so I did not poll again.
- Ran symbolic series checks outside Lean for `0 ≤ n,d ≤ 5`. They consistently gave
  the first nonzero term

```text
φ_{n,d}(z) = 1 - C_{n,d} z^(n+d+1) + O(z^(n+d+2))
```

  with

```text
C_{n,d} = ((-1)^d) * n! d! / ((n+d)! (n+d+1)!)
```

  so the sign appears to depend only on the parity of `d`.

## First concrete case where the pattern fails or becomes unclear
No counterexample was found for `0 ≤ n,d ≤ 5`; the symbolic checks matched the formula above
throughout that range.

The first place the pattern becomes unclear is not a numerical counterexample but the first
generic case beyond the live explicit formulas. `OpenMath/Pade.lean` only hard-codes small
Padé defects up to `(3,3)`, so the proof becomes genuinely unclear as soon as we leave that
finite table. The first such pair is `(n,d) = (4,0)`, although the external symbolic check
still supports the same coefficient formula there.

## Possible solutions
- Prove the coefficient formula directly from the explicit coefficient sums for `padeP` and
  `padeQ` by extracting the `z^(n+d+1)` coefficient of `padeR n d z * exp (-z) - 1`.
- Alternatively, first strengthen `pade_approximation_order` to an exact statement for
  `padeP - padeQ * expTaylor (n+d)` with its leading coefficient, then combine that with a
  clean remainder theorem for `exp - expTaylor (n+d)`.
- The honest replacement still looks **unconditional**, not restricted to a subfamily:
  no small-case evidence suggests a parity/sign failure. The missing ingredient is proof
  infrastructure, not a theorem-family restriction.
