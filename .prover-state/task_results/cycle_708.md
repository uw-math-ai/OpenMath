# Cycle 708 Results

## Worked on

`OpenMath/LMMAsGLM/StabilityCharpoly.lean` — landed all three planned
targets (Steps C.20, D.1, and D.2):

- **Target 1 / Step C.20**: `toGLM_charpoly_eval_ne_zero_iff_of_bdf`
  (eval-form contrapositive of cycle 706's unified BDF iff).
- **Target 2 / Step D.1**: `D_mul_toGLM_charpoly_eval_zero_eq`
  (general non-BDF closed form for `D · charpoly(0)`).
- **Target 3 / Step D.2**: `D_mul_toGLM_charpoly_eval_zero_eq_zero_of_bdf`
  (alternative proof of cycle 704's `toGLM_charpoly_eval_zero_eq_zero_of_bdf`
  routed through the new general identity).

## Approach

### Target 1 (Step C.20)
Used the strategy's primary shape:
```
rw [Ne, toGLM_charpoly_eval_eq_zero_iff_of_bdf m ξ hbdf hz, not_or]
```
The trailing `rfl` from the strategy template was *not* needed — the
`rw` already closed the goal (`Ne … ∧ Ne …` lined up with `¬ … ∧ ¬ …`
modulo the `Ne`-unfold inside the rewrite chain). The `lean_diagnostic_messages`
LSP caught a stray "no goals to be solved" on the `rfl`, which I removed.

**Worked shape**: 1-line `rw` chain. Strategy's fallback (`tauto` /
`simp only [Ne]`) was unnecessary.

### Target 2 (Step D.1)
Used the strategy's primary shape:
```
have h := D_mul_toGLM_charpoly_eval_eq m (z := z) (ξ := 0) hz hs
have h0 : (0 : ℂ) ^ s = 0 := zero_pow hs.ne'
rw [h0] at h
linear_combination h
```
`linear_combination h` accepted the residual identity directly after
substituting `0 ^ s = 0`. Neither the `simp only`/`linarith` fallback
nor the manual `ring_nf` chain was needed.

**Worked shape**: 4-line proof. Cleanest possible specialization at
`ξ = 0` of the cycle 700 general headline.

### Target 3 (Step D.2)
Built on the cycle 672 BDF row-collapse `toGLM_stabilityCharpolyRowF_of_bdf`
combined with the cycle 682 / cycle 700 row-split
`toGLM_stabilityCharpolyRowF_eq_alphaPoly_plus_PY_betaPoly`:

1. **`rowFBetaPoly m = 0` under BDF**: each summand has coefficient
   `m.β (Fin.castSucc k)`, which is 0 by BDF since `Fin.castSucc k`
   is strictly less than `Fin.last s` (used `Fin.castSucc_lt_last k`
   then `.ne`). Followed by `Finset.sum_eq_zero` and `simp`.
2. **`rowFAlphaPoly m = 0` under BDF**: deduced from the row-split
   `0 = rowFAlphaPoly m + PY.charpoly * rowFBetaPoly m` (after substituting
   `hRowF` and `hBeta`).
3. The Step D.1 RHS then collapses by `simp` after rewriting both
   `rowFAlphaPoly m` and `rowFBetaPoly m` to `0`.

**Worked shape**: ~12-line proof. No new auxiliary lemmas needed.

## Result

**SUCCESS** for all three targets. `lake env lean
OpenMath/LMMAsGLM/StabilityCharpoly.lean` exits 0 with zero
diagnostics. No new sorrys introduced. File grew from 1709 → ~1772
lines (well under the 3000-line cap). Only tracked file changed is
`OpenMath/LMMAsGLM/StabilityCharpoly.lean` (plus this task result).

## Dead ends

None this cycle. The strategy's fallback proofs were not needed for
any target — the primary shape worked first try in each case after
one cosmetic correction (dropping the trailing `rfl` on Target 1).

## Discovery

- For eval-form iff contrapositives where the iff already targets
  equalities, `rw [Ne, <iff>, not_or]` closes the goal *without* a
  trailing `rfl`. The defeq `Ne x 0 ↔ ¬ (x = 0)` is unfolded by the
  initial `rw [Ne]`, and the `not_or` rewrite then aligns the `∧`
  branches. This template is reusable for future eval-form
  contrapositives in `StabilityCharpoly.lean` and avoids spurious
  "no goals to be solved" errors.
- `Fin.castSucc_lt_last : Fin.castSucc k < Fin.last s` is the clean
  way to discharge `Fin.castSucc k ≠ Fin.last s` (just append `.ne`).
  No need for `Fin.ext_iff` / `Fin.val_ne_iff` gymnastics.
- The cycle 672 `toGLM_stabilityCharpolyRowF_of_bdf` plus the cycle
  682 row-split is enough to drive *both* `rowFAlphaPoly = 0` and
  `rowFBetaPoly = 0` under BDF — no new helpers needed. The "alpha"
  side is fully determined once the rowF and beta sides are known to
  vanish.

## Suggested next approach

The unit-disk root-counting argument that turns Step C.19's iff into
the BDF case of `LMM.toGLM_isAStable_iff` remains the next
architectural milestone (per cycle 706's task result). Step C.20's
contrapositive is one of the natural inputs (it gives a clean
"non-zero on the closed unit disk" framing).

For the general (non-BDF) iff, Step D.1 isolates the constant term
of `D · charpoly` purely in terms of `(rowFAlphaPoly m).eval 0`,
`(rowFBetaPoly m).eval 0`, and `(toGLM_stabilityMatrixPY m 0).charpoly.eval 0`.
A future cycle could:

1. Try to evaluate `(rowFBetaPoly m).eval 0` in closed form (it
   should equal `m.β (0 : Fin (s+1))` cast to ℂ, i.e. the `k = 0`
   summand of `rowFBetaPoly`).
2. Try to evaluate `(rowFAlphaPoly m).eval 0` in closed form similarly.
3. Combine to get a simple necessary condition on `m` for `ξ = 0` to
   be a non-spurious root of the GLM charpoly. This may unlock the
   precise statement of the general iff (which per the strategy may
   itself require modification — spurious roots can lie outside the
   unit disk for non-BDFs).

For an immediately tractable next cycle, Step D.3 could specialize
`D_mul_toGLM_charpoly_eval_eq` at `ξ = 1` (the boundary of the unit
disk that determines A-stability) to produce a closed-form for
`D · charpoly(1)` analogous to Step D.1. Both `1^s = 1` and the
non-zero `ξ` regime simplify cleanly.
