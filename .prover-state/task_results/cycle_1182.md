# Cycle 1182 Results

## Worked on
§530 LMM-as-GLM `HasOrderGe2` and `HasOrderGe3` witnesses for
`adamsMoulton8`, appended to `OpenMath/LMMAsGLM/Section530Step8.lean`.
Continues the AB7 → AM7 → BDF7 → AB8 rotation through cycles 1166–1180,
landing the AM-side of the s = 8 row.

Also added the supporting lemmas in `OpenMath/AdamsMethods.lean`:

* `adamsMoulton8_consistent : adamsMoulton8.IsConsistent`
* `adamsMoulton8_implicit : adamsMoulton8.IsImplicit`

## Approach
Mirrored AM7GE2 and AM7GE3 from `Section530Step7.lean` with the
substitutions `7 → 8`, `Fin 14 → Fin 16`, helper-row indices `k = 6..13`
→ `k = 7..15`. AM8GE3 used the Pascal shift constant
`C = s² − 2 β_s s = 64 − 16·(1070017/3628800) = 13445183/226800`.

For AM8GE2:
* Inline `q''_obligation` arms for `k = 0..6` (seven inline `simp +
  norm_num` arms; first arm `k = 0` closes with `simp` alone).
* Helpers `q''_obligation_seven` … `q''_obligation_fifteen` (nine
  private theorems for fresh heartbeat budget).
* Boundary `k = 8` (first past-`h·f` row) closes with `simp` alone — no
  `norm_num`. Matches the AM-family pattern from cycles 1158/1170/1172.

For AM8GE3:
* Same `q''` shape as AM8GE2 but with the `C = 13445183/226800` shift in
  `q''N` and `q'''N`. The `k = 0` inline arm now needs `norm_num`
  (because `C ≠ 0` leaves a residue in the past-`h·f` columns).
* `q'''` helpers for `k = 4..15` (twelve private theorems), with inline
  arms for `k = 0..3`. All close with `simp + norm_num`, including the
  `k = 8` boundary (the non-zero shift produces a numeric residue that
  `simp` alone cannot close).

## Result
SUCCESS. `lake env lean OpenMath/LMMAsGLM/Section530Step8.lean` compiles
clean with no errors and no new warnings. Both
`adamsMoulton8_toGLM_hasOrderGe2` and `adamsMoulton8_toGLM_hasOrderGe3`
landed; the `HasOrderGe1` companion is the standard one-line
consequence via `.toHasOrderGe1`.

Wall-clock for full leaf-file compile (after `lake build OpenMath.LMMAsGLM`):

* AM8GE2 alone: 2m02s
* AM8GE2 + AM8GE3: 2m28s

These match the cycle-1178 budget (1m38s for AB8GE2) plus the
expected AM-family `norm_num` overhead from the 3628800-denominator
rationals.

## Boundary nuance confirmation
The AM-family `q''_obligation_eight` row (first past-`h·f` row at
`k = s = 8`) closes with **`simp` alone** in both AM8GE2 and AM8GE3 —
matching the AM6/AM7 pattern. Adding `norm_num` would trigger "no goals
to be solved". The `q'''_obligation_eight` row, by contrast, requires
`simp + norm_num` because the non-zero `C = 13445183/226800` shift
leaves a numeric residue (analogous to AM7GE3 cycle 1172).

## Dead ends
None this cycle — the AM-family recipe carried over verbatim with the
Fin-size bump and helper-name list.

## Discovery
The `C = s² − 2 β_s s` Pascal shift constant for AM8 simplifies to
`13445183/226800` (denominators differ by a factor of 16 from the AM7
case `386561/8640`). Despite the larger denominators, per-row `norm_num`
remained well under the 200000 heartbeat budget — the rationals are
"large but flat" and don't blow up the kernel work.

## Suggested next approach
Continue the §530 LMM-as-GLM rotation with `bdf8`. The next slot in the
table is BDF8GE2 (and possibly BDF8GE3) — the BDF-side of the s = 8
row. After that, the rotation reaches s = 9 (AB9, AM9, BDF9), with each
new step requiring a new `Section530Step<N>.lean` leaf file and the
matching `_consistent` / `_implicit` lemmas in the relevant LMM-method
file.
