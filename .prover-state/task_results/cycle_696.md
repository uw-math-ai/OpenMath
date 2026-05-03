# Cycle 696 Results

## Worked on
§521 Step C.13b — `activeStabilityPolyPoly_eq_stabilityPolyPoly_add_correction`
in `OpenMath/LMMAsGLM/StabilityCharpoly.lean` (general bridge between
the active and textbook stability polynomials, with the explicit
`z`-times-correction term over `Fin s`).

## Approach
Followed the strategy: unfold both sides, apply the cycle-694 helper
`toGLM_stabilityMatrixPY_zero_charpoly_eq` and `Polynomial.smul_eq_C_mul`
on the LHS, expand `stabilityPolyPoly` on the RHS via
`Fin.sum_univ_castSucc`, substitute `α(Fin.last s) = 1` and
`Fin.val_last`, then reduce three `Fin s` sums to a single
per-summand identity.

The load-bearing computation was a per-`l` polynomial identity
```
C(D) * (C(-α(castSucc l)) * X^l)
  = -(C(α(castSucc l) - z β(castSucc l)) * X^l)
    - C(z) * (C(β(castSucc l) - β_last α(castSucc l)) * X^l)
```
proved as `hsum_eq` by collecting `Polynomial.C` factors via
`← Polynomial.C_mul/_add/_sub/_neg`, peeling `X^l`, and discharging
the residual scalar identity `(1 - z β_last) · (-α) = -(α - z β) − z (β − β_last α)`
in `ℂ` with `push_cast; ring`.

After applying `hsum_eq` under `Finset.sum_congr`, the goal collapses
to a polynomial identity that `ring` closes once the inner sums are
combined via `Finset.sum_neg_distrib`, `sub_neg_eq_add`, and
`Finset.sum_add_distrib`.

## Result
SUCCESS. `OpenMath/LMMAsGLM/StabilityCharpoly.lean` and
`OpenMath/LMMAsGLM.lean` both compile under `lake env lean` with no
errors and no warnings. The new theorem
`activeStabilityPolyPoly_eq_stabilityPolyPoly_add_correction` is
sorry-free.

## Dead ends
* `ring_nf` alone could not close the per-summand goal: `ring` does
  not see through `Polynomial.C` (the C-of-mul / C-of-add lemmas need
  to be applied as rewrites first).
* Single-line `lean_multi_attempt` snippets with `have h : ... := by
  push_cast; rfl; rw [h, ...]` got mis-parsed because the second `;`
  is interpreted as part of the `by` block; wrapping the proof in
  parens `(by ...)` resolves it. (Mostly an LSP-tool quirk; the file
  proof uses a normal multi-line `have ... := by ...` block.)
* The earlier preferred-path skeleton from the strategy had a single
  giant `show ... by ring` clause that triggered a parser error
  (unexpected token `by`). Splitting the rewrites into named helpers
  (`hsum_eq`, `hα_last`) made the proof robust.

## Discovery
The `Polynomial ℂ` identity in the per-summand reduction is exactly
the cleanest form of the cycle-692 redefinition: `D · α = (α - z β) +
z (β - β_last α)`. The fact that this matches `hsum_eq` so cleanly
confirms the cycle 692/694 redefinition is the right structural choice
(no spurious correction term beyond the textbook one).

The general bridge specialises to `Step C.13b under BDF`: when every
`β(castSucc l) = 0`, the inner correction becomes
`C(-(β_last α(castSucc l))) X^l`, and the global correction collapses
to `-C(z β_last) · ∑ C(α(castSucc l)) X^l`, matching the strategy's
prediction (and the disproven-identities note in the cycle-692 issue
file). No hypothesis on `β_last` is needed.

## Suggested next approach
Step C.14 — assemble the active-side headline using the new bridge:
combine `D_mul_toGLM_charpoly_eq_X_pow_mul_active_plus_residual`
with `activeStabilityPolyPoly_eq_stabilityPolyPoly_add_correction` to
obtain
```
C(D) * charpoly = X^s * stabilityPolyPoly
                  + X^s * (correction term)
                  - residual
```
i.e. a stand-alone identity that no longer mentions
`activeStabilityPolyPoly`. This is the form the eventual root-counting
argument for A-stability will use.
