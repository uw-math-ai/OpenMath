# Cycle 1160 Results

## Worked on
`adamsMoulton6_toGLM_hasOrderGe3` in `OpenMath/LMMAsGLM/Section530.lean`
— next rung of the §530 LMM-as-GLM ladder
(AB6GE3 → AM6GE2 → **AM6GE3**), promoted from cycle 1158's "Suggested
next approach".

## Approach
Mirrored the AB6GE3 namespace (cycle 1156, lines 1106–1359) verbatim
with two textual substitutions:

- `adamsBashforth6 → adamsMoulton6`
- `36 → (162353/5040)` (only inside the qN/q''N/q'''N defs, where the
  shift constant `C = s² − 2·β_s·s = 36 − 2·(19087/60480)·6 = 162353/5040`
  lives)

`AB6GE3` was renamed to `AM6GE3`. The four private noncomputable
Nordsieck vectors (`qN`, `q'N`, `q''N`, `q'''N`), seven
`q''_obligation_<k>` helpers (k = 5..11), eight `q'''_obligation_<k>`
helpers (k = 4..11), the two master dispatchers, and the public
theorem `adamsMoulton6_toGLM_hasOrderGe3` were all carried over with
the same `simp [...]; norm_num` template — including the `q''_obligation_six`
boundary nuance (simp alone, no norm_num) inherited from AB6GE2 /
AM6GE2 / AB6GE3.

The substitution was applied with `sed`, then the resulting block was
inserted via Python after `adamsMoulton6_toGLM_hasOrderGe1` (line 1498)
together with a doc-comment header explaining the shift constant.

## Result
**SUCCESS** — `lake env lean OpenMath/LMMAsGLM/Section530.lean` exits 0
in ~3m10s wall (vs. ~2m45s for AM5GE3, consistent with one extra row
pair plus a fractional shift). No sorry's. File is 2328 lines (well
under the 3000-line cap; +263 lines from the AM6GE3 block).

The mirror-AB6GE3 template worked first try — every per-row helper
`simp [...]; norm_num` closed without modification, including all
`q'''_obligation_*` rows under the fractional `C = 162353/5040`. The
strategy's worry about `norm_num` timing out on the 5040 denominator
did not materialise.

## Dead ends
None this cycle. The recipe was mechanical and the substitution
applied cleanly.

## Discovery
- The `simp [...]; norm_num` per-row template scales to denominators
  as ugly as `5040` without needing `field_simp; ring`. The AM5GE3
  shift `3125/144` was easier; the AM6GE3 shift `162353/5040` is the
  worst LMM constant so far in the ladder, and `norm_num` still
  closed each row in budget.
- Strategy's note that AB6GE3's `q'''_obligation_six` uses simp alone
  is incorrect — `q'''_obligation_six` in AB6GE3 (line 1320–1321)
  uses `simp [...]; norm_num`. Only `q''_obligation_six` is
  simp-alone. The AM6GE3 mirror correctly preserved this asymmetry.
- The `q'_obligation`, `q''_obligation`, `q'''_obligation` names get
  re-declared in each namespace; namespacing keeps them private and
  isolated, so the public theorem reference uses
  `AM6GE3.q'_obligation` etc. (No re-use across AM6GE2 — re-declared,
  consistent with AB6GE3's choice.)

## Suggested next approach
The s = 6 LMM ladder now has both GE2 and GE3 witnesses for AB6 and
AM6. The natural next rungs:

1. **BDF6GE2** then **BDF6GE3** — completes the s = 6 row across
   AB / AM / BDF, mirroring the s = 5 layout (AB5/AM5/BDF5 each have
   GE2 and GE3 closed). BDF6's β coefficients are
   `60/147` and zero elsewhere on past-h·f; the shift constant for
   BDF6GE3 is `C = 36 − 2·(60/147)·6 = 36 − 720/147 = 4572/147 = 1524/49`.
2. **s = 7 ladder** (AB7GE2, AM7GE2, BDF7GE2 first) — extends the
   ladder one step further. AB7's `β_s = 0` so its GE3 shift is
   `C = 49`; AM7's `β_s = 36799/120960` gives
   `C = 49 − 2·(36799/120960)·7 = ...`. Note `Fin 14` slots will
   stress the simp closure further; per-row helper extraction will
   continue to be mandatory.

The planner should pick BDF6GE2 next to keep the s = 6 row symmetric
before stepping to s = 7.
