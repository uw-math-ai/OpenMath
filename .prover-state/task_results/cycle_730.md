# Cycle 730 Results

## Worked on
§521 Step H — closed form for `(rowFAlphaResidual m l).eval 1` and the
headline general (non-BDF) unit-circle identity. All three sub-targets
landed (H.1, H.2, H.3) plus the strategy-mandated promotion of
`rowFAlphaResidual_eval_one_eq_double_sum` from `private` to public.

## Approach
Followed the planner's recommended path with one key proof simplification:

- **Promotion** (line 2197 of `StabilityCharpoly.lean`): dropped `private`
  on `rowFAlphaResidual_eval_one_eq_double_sum`, mirroring cycle 728's
  promotion of `rowFAlphaResidual_eval_one_of_bdf_eq_zero`. No proof
  change needed; required by H.2.

- **H.1** (`toGLM_stabilityMatrixPY_zero_charmatrix_adjugate_last_col`):
  rather than the strategy's row-swap + Laplace + 2×2 minor block-decomp
  route (which the strategy itself flagged as ~150 lines of bookkeeping
  in the off-diagonal case), used the **adjugate row equation**
  `A · (adj A) = (det A) • I`. At off-diagonal entries `(j, ⟨s-1, _⟩)`
  for `j < s - 1`, the LHS sum collapses to
  `X · adj(j, last) - adj(j+1, last) = 0`, giving the recurrence
  `adj(j+1, last) = X · adj(j, last)`. Iterate over `n` to telescope:
  `X^n · adj(j, last) = adj(j + n, last)`, then instantiate at
  `j = k`, `n = s - 1 - k`, anchor at the F.1 result
  `adj(s-1, last) = X^(s-1)`, and cancel `X^(s-1-k)` (a non-zero-divisor
  in `Polynomial ℂ`) via `mul_left_cancel₀` to recover `adj(k, last) = X^k`.
  Total: ~110 lines, no Laplace expansion needed.

- **H.2** (`rowFAlphaResidual_eval_one_closed_form`): direct
  substitution chain. After `rowFAlphaResidual_eval_one_eq_double_sum`,
  collapse the inner `j`-sum via `Finset.sum_eq_single ⟨s-1, _⟩` (off
  branch: PYHF is gated on `(j:ℕ)+1 = s` and so vanishes; on branch:
  the `z`-correction in PYHF zeros out at `z = 0`, leaving
  `β(castSucc l)`). Rewrite `(adj k ⟨s-1, _⟩).eval 1 = (X^k).eval 1 = 1`
  via H.1, then reshape with `Finset.mul_sum` + `ring`.

- **H.3** (`D_mul_toGLM_charpoly_eval_one_eq_stabilityPolyPoly`,
  general, non-BDF): substitute H.2 into G.1's residual sum:
  `∑ l, (rowFAlphaResidual m l).eval 1 = -(∑β castSucc) · (∑α castSucc)`
  via `Finset.sum_congr` + H.2 + `← Finset.sum_mul` +
  `Finset.sum_neg_distrib`. The substituted residual exactly cancels
  G.1's `∑β · ∑α` cross-product correction, and `ring` closes the rest.

## Result
**SUCCESS** on all three targets — H.3 included as the headline
general theorem.

The H.3 cancellation went through cleanly as the strategy predicted —
no residual term, no false-identity surprise. The BDF hypothesis is
not needed for the unit-circle reduction:

```
(1 − z β_last) · charpoly(stabilityMatrix z).eval 1
  = stabilityPolyPoly(z).eval 1
```

is now a general theorem, with F.4 (`..._of_bdf`) sitting as the
trivial BDF specialisation of H.3.

`lake env lean OpenMath/LMMAsGLM/StabilityCharpoly.lean` clean.
`lake build` clean (only pre-existing unrelated linter warnings in
`OpenMath/ButcherGroup/Section386Aug/DepthThree.lean`).

File size after H landings: 2837 lines (was 2623, +214). Still well
under the 3000 soft cap.

## Dead ends
- Initially wrote `Matrix.diagonal_apply` thinking the index order is
  `(k', ⟨j, hj⟩)`, but it's `(⟨j, hj⟩, k')`. Switched to a
  `by_cases hkj : k' = ⟨j, hj⟩` discrimination plus
  `Matrix.diagonal_apply_eq` / `Matrix.diagonal_apply_ne _ (Ne.symm hkj)`
  to handle the asymmetry, plus a manual `if` push for the `Polynomial.C`
  wrapping the indicator.
- One `congr 1; apply Fin.ext; ...; omega` chain in the calc telescope
  failed with "No goals to be solved" — `congr 1` over-decomposed.
  Replaced with an explicit
  `have hidx : ⟨..., _⟩ = ⟨..., _⟩ := Fin.ext (by ...; omega); rw [hidx]`.
- An `omega` invocation from inside a `Fin.ext (by omega)` lambda failed
  because it couldn't see that `(⟨a, _⟩ : Fin s).val = a`. Hoisted the
  computation out into a stand-alone `by apply Fin.ext; show _; omega`
  block.

## Discovery
- The **row equation** `A · adj A = (det A) • I` is a much cleaner
  vehicle for last-column / first-column adjugate identities than direct
  determinant computation. Each off-diagonal row equation gives a single
  recurrence step on the adjugate column. The strategy's worked-out
  Laplace + block-triangular minor proof (~150 lines) is correct but
  unnecessarily heavy for this particular structure.
- `Polynomial ℂ` is an integral domain, so `X^n` is a non-zero-divisor
  and `mul_left_cancel₀ (pow_ne_zero _ Polynomial.X_ne_zero)` cleanly
  closes the telescoped equation. No unique-permutation-in-det_apply
  arguments needed.

## Suggested next approach
The H-ladder closes the §521 unit-circle reduction. The natural next
targets:

1. **H.3 mirror at ξ = 0** — analogous closed form for
   `(rowFAlphaResidual m l).eval 0` and a clean
   `D_mul_toGLM_charpoly_eval_zero_eq_...` headline. The structure
   should mirror H.1/H.2/H.3 but with a *first-column* adjugate ladder
   instead of last-column. The H.1 proof technique generalises directly:
   use `A · adj A = (det A) • I` at off-diagonal `(j, ⟨0, _⟩)` entries
   to get a `column 0` adjugate recurrence, then telescope from a
   diagonal anchor. The first-column case may need its own anchor
   (analogous to F.1) — that should be a separate Step (call it
   F.1-mirror or H.0).

2. **`LMM.toGLM_isAStable_iff` bridge** — the §521 ladder's headline goal.
   With H.3 in place, the unit-circle (`ξ = 1`) side is now
   `charpoly · (1 − z β_last) = stabilityPolyPoly`. The `ξ = 0` side
   still goes through G.3 and contains the `rowFAlphaResidual ⟨0,_⟩ +
   α₀ · β₀` term. Once that mirror is closed, both endpoints are
   stabilityPolyPoly evaluations and an A-stability iff statement
   becomes within reach.

3. **D-ladder index audit** — cycle 728's deferred suggestion. With the
   H targets landed, a token-light index/glossary block at the top of
   `StabilityCharpoly.lean` listing each lettered step (D.11a–c, D.16a–d,
   E.1–4, F.1–4, G.1–3, H.1–3) and where it lives would make future
   navigation cheaper. Not load-bearing for any active proof, so a
   small surface-improvement cycle, not a score-3 candidate.

Score self-assessment: **3 / excellent** — both mandatory H targets
plus the stretch H.3 landed, with `ring`-close cancellation matching
the strategy's predicted algebra. No issue files needed.
