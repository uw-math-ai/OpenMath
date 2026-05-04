# Cycle 782 Results

## Worked on
§530 LMM-as-GLM order witnesses for `adamsBashforth2`:
- `adamsBashforth2_toGLM_hasOrderGe1` (must-land #1)
- `adamsBashforth2_toGLM_hasOrderGe2` (must-land #2)

Both added to `OpenMath/LMMAsGLM.lean`, adjacent to the existing
GE1 cluster (after `bdf2_toGLM_hasOrderGe1`) and after the BDF2
GE2 witness, per strategy.

## Approach
- GE1: one-line wrapper around `adamsBashforth2.toGLM_hasOrderGe1
  adamsBashforth2_consistent`, mirroring the four cycle-776 witnesses.
- GE2: copied the BDF2 GE2 body verbatim (the natural Nordsieck Taylor
  template `q'_y = j, q'_f = 1`, `q''_y = j², q''_f = 2j`) with method
  name substituted from `bdf2 → adamsBashforth2`. Strategy predicted
  this would suffice for AB2 because AB2 has `β_s = 0` (explicit), which
  makes the implicit-row contributions vanish — strictly easier than
  BDF2 (β_s = 1) which already worked.

## Result
SUCCESS — both witnesses compile under `lake env lean
OpenMath/LMMAsGLM.lean` with no errors.

One small deviation from the verbatim BDF2 template was required:
the BDF2 `(U·𝟙 = q + q')` row obligation has body
`simp [...]; norm_num`, but for AB2 the same `simp [...]` already
closes that branch (no `norm_num` needed). On the first compile,
keeping the trailing `norm_num` produced
`error: No goals to be solved` at line 1752 — fixed by dropping the
trailing `norm_num` from the `intro i; fin_cases i` branch.

The `B 𝟙 + V q' = q + q'` and `2 (B c) + V q'' = q + 2 q' + q''`
obligations both still need `simp [...]; norm_num` per
`fin_cases k`, exactly as in BDF2.

## Dead ends
None — first-attempt landing modulo the trailing-`norm_num` cleanup
above. The strategy's prediction (AB2 GE2 follows the BDF2 GE2
template trivially because AB2 is explicit) was accurate.

## Discovery
For an explicit LMM with `β_s = 0`, the GE2 `(U·𝟙 = q + q')`
obligation is closed by `simp` alone — `norm_num` is redundant
because there is no implicit-row coefficient to multiply through. For
implicit methods (BDF2 with `β_s = 1`, trapezoid with `β_s = 1/2`)
the trailing `norm_num` is load-bearing because the simp normal form
leaves a numeric arithmetic obligation involving `β_s`.

This is a small but useful refinement of the cycle-778 template:
the GE2 boilerplate body for explicit LMMs can drop the
single-stage `norm_num` while keeping the per-`fin_cases k`
`norm_num` calls intact. (Future stretch witnesses for AB3 / AB4
would inherit this same simplification, while BDF3 / AM3 would
not.)

## Suggested next approach
- **Cycle 783**: attempt `adamsBashforth3_toGLM_hasOrderGe1` (one-line
  wrapper, trivial) and `adamsBashforth3_toGLM_hasOrderGe2` (Stretch A
  from cycle 782 strategy, deferred). AB3 is `s = 3` (Fin 6 GLM
  inputs), order 3, explicit. The GE2 obligations are quadratic in
  `c`, not cubic — so the cycle-780 BDF3 GE3 heartbeat blowup does
  not directly apply. Try the natural template `q'' j = j², 2j` first.
  If `simp [..., Fin.sum_univ_succ]` times out on the s = 3 branches,
  fall back to `Fin.sum_univ_four` / per-`fin_cases` blocks. Drop the
  stretch if either approach times out (per cycle 782 strategy).
- **Cycle 784**: `bdf3_toGLM_hasOrderGe1` and a careful-shift attempt
  at `bdf3_toGLM_hasOrderGe2`. BDF3 has `β_s ≠ 0`, so the natural
  template will likely need a shift `C = (Uq'')_0`. Compute `C`
  algebraically before submitting; if non-trivial, defer.
- **Cycle 785+**: `adamsMoulton3_toGLM_hasOrderGe2` and (if the AM2
  GE3 shift pattern generalises) `adamsMoulton3_toGLM_hasOrderGe3`.
  AM3 is `s = 3` (Fin 6) with `β_s = 9/24`; shift would be
  `C = s² - 2·β_s·s = 9 - 27/4 = 9/4`. The Fin 6 simp issue from
  cycle 780 may bite here too — defer until AB3 GE2 shows the Fin 6
  branch budget is workable.

The natural-template Fin 4 budget (s = 2) is fully exercised now:
forward Euler / backward Euler GE1, trapezoid GE1+GE2, BDF2 GE1+GE2,
AB2 GE1+GE2, AM2 GE1+GE2+GE3 (shifted). The next milestone is
proving the Fin 6 (s = 3) budget can carry GE2 for at least one
explicit method (AB3) before attempting any implicit s = 3 witness.
