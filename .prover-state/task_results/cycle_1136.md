# Cycle 1136 Results

## Worked on

§530 LMM-as-GLM order-≥ 3 witness — `adamsMoulton4_toGLM_hasOrderGe3`
in `OpenMath/LMMAsGLM.lean`. Completes the s = 4 LMM-as-GLM
`HasOrderGe3` triplet (AB4, BDF4 from cycle 1134; AM4 this cycle).

## Approach

Mirrored the AB4GE3 / BDF4GE3 helper-extraction recipe verbatim,
substituting the AM4 shift constant
`C := s² − 2 β_s s = 16 − 2·(251/720)·4 = 1189/90`.

Inserted a new `namespace AM4GE3` block immediately after the
`bdf4_toGLM_hasOrderGe3` block (line 2441) and before `namespace
Matrix`. The block defines four private `noncomputable def`
Nordsieck vectors (`qN`, `q'N`, `q''N`, `q'''N`) on `Fin (2*4)`
using the `Fin.addCases ... (Fin.cast (Nat.two_mul 4) k)` shape.
The q''' obligation is split into `q'''_obligation_seven` (carved
out for `k = 7`) plus a parent `q'''_obligation` that does
`fin_cases k` and discharges k = 0..6 inline with the standard
`simp [LMM.toGLM, adamsMoulton4, Fin.addCases, Fin.sum_univ_succ,
qN, q'N, q''N, q'''N]; norm_num` block.

The public theorem then `refine`s the `HasOrderGe3` constructor and
discharges the four lower-order obligations (V·q = q, q-row, q'-row,
q''-row) by `intro k; fin_cases k; all_goals simp [...]; all_goals
norm_num`.

## Result

**SUCCESS** — `OpenMath/LMMAsGLM.lean` compiles with zero `sorry`s
and zero new heartbeat warnings on the first attempt at the
literal recipe (ladder step 1).

Wall clock: `lake env lean OpenMath/LMMAsGLM.lean` took
**~2m02s** (real). For comparison the strategy noted AB4 ~85s and
BDF4 ~115s baselines; AM4 with 720-denominator rationals comes in
slightly above BDF4 but within budget.

Per-`Fin 8` case usage of the ladder for `q'''_obligation`:

- k = 0..6: closed inline with `simp; norm_num` (ladder step 1).
- k = 7: closed via `q'''_obligation_seven` helper (ladder step 2,
  a single helper sufficed; no extra k = 5/6 helpers needed —
  matching AB4 and BDF4).

## Dead ends

None. The literal AB4GE3 / BDF4GE3 recipe with `C = 1189/90` worked
on the first build. No need to descend the ladder past step 2.

## Discovery

- AM4 (β with `*/720` denominators) does not require more per-case
  helpers than AB4 (β = ratios) or BDF4 (β with `*/25`). The
  bottleneck case is uniformly `k = 7`, which makes sense
  geometrically: the q''' obligation is densest on the s-th input
  slot since the `j³ − 3·C·j` shift evaluates non-trivially across
  all four past-y indices and all four past-(h·f) indices, with
  `B(7,·)` and `V(7,·)` both pulling on the full `β_s` row.
- `norm_num` handles the `1189/90` ↔ `2008/720` equivalence
  without manual rationalisation. This confirms that `*/720`
  fractions are not categorically harder than `*/25`; what
  matters is depth of the Fin.sum_univ_succ unfolding, not the
  denominator size.
- The `(V q) = q` row obligation closed without an explicit
  `norm_num` after `simp` (the inline AB4 recipe shape, not the
  BDF4 one which has a trailing `norm_num`). This suggests
  `adamsMoulton4_consistent` already provides enough to close
  the q-row by `simp` alone.

## Suggested next approach

The s = 4 LMM-as-GLM `HasOrderGe3` slate is now complete (AB4,
BDF4, AM4). Natural follow-ups, in order of risk:

1. **`HasOrderGe4` predicate-shape exploration** for the s = 3
   family (AB3, AM3, BDF3) on a separate planning cycle. Cycle 800
   / 802 / 1132 set the s = 3 `HasOrderGe3` foundation. The
   `HasOrderGe4` predicate likely needs a `j⁴ − 6 C j² + (...)` or
   similar Nordsieck shift; the closed form needs a research pass
   before a worker can attempt it.

2. **`_via_ge3` projection corollaries** for AM4 / AB4 / BDF4 once
   `HasOrderGe3.toHasOrderGe2` (and likewise `.toHasOrderGe1`)
   exist in `OpenMath/GeneralLinearMethod.lean`. This is mostly
   bookkeeping; verify the projection lemma exists before
   scheduling.

3. **s = 5 family blocked** — cycle 786 confirmed AB5
   `HasOrderGe2` already exhausts the budget at the q'
   obligation. Don't open this without new tactic infrastructure.

The optional stretch (`adamsMoulton4_toGLM_hasOrderGe2_via_ge3`)
was not attempted because the projection lemma's existence wasn't
quickly verifiable inside the cycle budget; defer to the next
planner pass.
