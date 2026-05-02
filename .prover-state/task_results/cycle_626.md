# Cycle 626 Results

## Worked on
§512 LMM stability lift — Phase E (assembly) in `OpenMath/LMMAsGLM.lean`.

Added the headline theorems:

1. `LMM.toGLM_isStable (m : LMM s) (hzs : m.IsZeroStable) : m.toGLM.IsStable`
2. `LMM.toGLM_isConvergent (m : LMM s) (hcon : m.IsConsistent)
   (hzs : m.IsZeroStable) : m.toGLM.IsConvergent`

Plus a small private monotonicity helper `M_max_pow_le_M_max_pow_of_le`.

## Approach
Followed the planner's Phase E recipe end-to-end.

1. Picked the Phase D step 4 witness `(My, hMy_nonneg, hMy)` from
   `toGLM_y_half_iter_complex_norm_bound`.
2. Set `Mbase := (M_max m) ^ s` (≥ 0 via `pow_nonneg` and the existing
   `M_max_nonneg`) and `M' := My * Mbase + Mbase`.
3. Reindexed the input slot `k : Fin (2*s)` into `Fin (s + s)` via
   `Fin.cast (Nat.two_mul s)` and split with `addCases` into the
   y-half and `h*f`-half, exactly the pattern used by `toGLM_V_row_l1_le`.
4. **y-half slot**:
   - `n < s`: bounded by `(M_max m)^n * 1 ≤ Mbase ≤ M'` via Phase C
     (`toGLM_V_iter_le`) and the new pow-monotonicity helper.
   - `s ≤ n`: set `j := n − s`; complex norm of the y-half on `V^[s] q`
     bounded by `Mbase` via `pi_norm_le_iff_of_nonneg`,
     `Complex.norm_real`, `Real.norm_eq_abs`, and Phase C; apply `hMy`
     with `n := s, j := j`; extract single coordinate via
     `norm_le_pi_norm`; identify
     `toGLM_y_half (V^[s+j] q) k' = (V^[n] q) (cast.symm (castAdd s k'))`
     by `unfold` + `s + j = n`.
5. **h·f-half slot**:
   - `n < s`: same Phase C bound as the y-half.
   - `s ≤ n`: Phase B (`toGLM_V_iter_natAdd_eq_zero_of_le`) makes the
     slot zero; bound holds by `0 ≤ M'`.
6. `toGLM_isConvergent` is the planned literal `⟨…, …⟩` combining
   `toGLM_isConsistent` and `toGLM_isStable`.

## Result
SUCCESS.

Verification:

- `lake env lean OpenMath/LMMAsGLM.lean` exits 0.
- `grep -c sorry OpenMath/LMMAsGLM.lean` prints `0`.
- Both `toGLM_isStable` and `toGLM_isConvergent` are defined sorry-free
  in `OpenMath/LMMAsGLM.lean`.
- `plan.md`'s §512 entry is now `[x]`; the Active Frontier got a new
  cycle 626 paragraph; backlog item #1 was updated.
- `.prover-state/issues/butcher_section512_lmm_stability_lift.md`
  retired (deleted).

## Dead ends
The strategy's suggested `pow_le_pow_right` (for `1 ≤ a → n ≤ m →
a^n ≤ a^m` on `ℝ`) failed: Mathlib's `pow_le_pow_right'` lives on the
unbundled monoid path and demands a `MulLeftMono ℝ` instance the
synthesizer would not provide. Switched to `pow_le_pow_right₀` (the
`MonoidWithZero` form with `ZeroLEOneClass + PosMulMono`), which
discharges trivially on ℝ. No other dead ends.

## Discovery
The default norm on `Fin s → ℂ` (no `PiLp` wrapper) is the Pi sup-norm,
and the right pair of API lemmas for the §512 lift is
`pi_norm_le_iff_of_nonneg` + `norm_le_pi_norm`, exactly as the
strategy outlined. `Complex.norm_real (r : ℝ) : ‖(r : ℂ)‖ = ‖r‖` plus
`Real.norm_eq_abs` is the right composition to land on `|r|`.

The y-half coordinate `toGLM_y_half q k = q (cast.symm (castAdd s k))`
is definitionally equal to the corresponding `Fin (2*s)` slot, so
`unfold toGLM_y_half` plus a `rw [hns_eq]` (where `hns_eq : s + j = n`)
is enough to reconcile the Phase D output with the §510 stability
goal — no extra reindexing equality lemma needed.

## Suggested next approach
The natural next §51x targets are:

- **§513 (necessity of stability for convergence)** — the converse of
  Phase E on the LMM-as-GLM side. With the §512 LMM lift now closed,
  the §513 side likely reduces to upgrading the existing §513 LMM
  necessity to a GLM statement.
- **§515 (Dahlquist equivalence)** — the GLM analogue of
  `OpenMath/DahlquistEquivalence.lean`. Backlog item #2.

Either of these is a natural follow-up; §515 is the heavier lift.

A separate clean-up worth scheduling: the helper `toGLM_y_step` and
its iterate / complex bridges live next to the Phase E theorems but
are now only consumed via `toGLM_y_half_iter_complex_norm_bound`. If
the §513/§515 work doesn't reuse them directly, they could be made
`private`. Not load-bearing this cycle.
