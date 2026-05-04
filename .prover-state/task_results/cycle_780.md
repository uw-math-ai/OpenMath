# Cycle 780 Results

## Worked on
§530 LMM-as-GLM order ≥ 3 witness for `adamsMoulton2` (must-land target),
plus `HasOrderGe2` and `HasOrderGe1` projection re-exports. Attempted
the BDF3 stretch witness but dropped it on heartbeat-timeout grounds
(documented below).

## Approach
Followed the cycle-778 scaffold for `bdf2_toGLM_hasOrderGe2` as the
template. Wrote the order-≥ 3 witness with the Nordsieck Taylor-moment
table on `Fin (2 * s)`:

* `q_{past-y j} = 1, q_{past-f j} = 0`
* `q'_{past-y j} = j, q'_{past-f j} = 1`
* `q''_{past-y j} = j² − C, q''_{past-f j} = 2 j`
* `q'''_{past-y j} = j³ − 3·C·j, q'''_{past-f j} = 3·(j² − C)`

with the **shift constant** `C := s² − 2 β_s s` chosen to kill
`(U q'')_0`. For AM2 (`s = 2, β_s = 5/12`) this gives `C = 7/3`.
The first `?_` discharges via `LMM.toGLM_V_nordsieckQ_eq` together with
`adamsMoulton2_consistent`. The remaining four are closed by
`fin_cases k; simp [LMM.toGLM, adamsMoulton2, Fin.addCases, Fin.sum_univ_succ];
norm_num`.

The two projection re-exports use `HasOrderGe3.toHasOrderGe2` and
`HasOrderGe2.toHasOrderGe1`.

## Result
SUCCESS for must-land target. Committed in two stages:
* `f4c44458e9` — scaffold with `sorry`s.
* `247588e973` — closed all five obligations (the must-land witness).
* (this cycle, pending push) — `adamsMoulton2_toGLM_hasOrderGe2/1`
  projection re-exports.

PARTIAL on stretch: BDF3 stretch witness `bdf3_toGLM_hasOrderGe3` was
written and verified by hand but does not compile inside the
`maxHeartbeats 200000` budget.

## Dead ends

### Naive Nordsieck Taylor template fails the predicate

The natural Taylor moment template `q'' j = j², 2j` and `q''' j = j³,
3 j²` does **not** satisfy Lean's `HasOrderGe3`. Substituting into the
order-2 obligation at row `k = s − 1` (the last past-`y` row, where
`B[k, 0] = β_s`) gives an extra `−3 (B(Uq''))_k` term that vanishes
only if `(U q'')_0 = 0`. With the natural template, `(U q'')_0`
evaluates to the LMM-specific constant `s² − 2 β_s s`, which is non-zero
for both AM2 (7/3) and BDF3 (63/11).

The fix is to pre-shift `q''_{past-y j}` by `−C` so `(U q'')_0` becomes
zero exactly. The corresponding `q'''_{past-y j}` shift is `−3 C j`,
and `q'''_{past-f j}` shifts to `3 (j² − C)`. With this shifted moment
table, all five obligations are simple linear/quadratic identities in
the LMM coefficients and `simp; norm_num` closes them.

### BDF3 stretch — heartbeat timeout

The BDF3 witness has `Fin (2 · 3) = Fin 6` GLM input slots. Closing the
order-3 obligation `refine_5` (the `q'''` identity, which has cubic
polynomial entries on past-`y` summed against six `B[k, j]` and `V[k, l]`
entries) timed out in `simp` with the message:
```
Tactic `simp` failed with a nested error:
(deterministic) timeout at `whnf`, maximum number of heartbeats (200000)
has been reached
```

Tried:
1. `simp [LMM.toGLM, bdf3, Fin.addCases, Fin.sum_univ_succ]; norm_num` —
   timed out on `whnf`.
2. `simp only [...]` with a curated lemma list (LMM.toGLM, bdf3,
   Fin.addCases, Fin.sum_univ_succ/zero, Fin.cast_mk, Fin.castSucc_mk,
   Fin.last, Fin.val_zero/succ/mk, Fin.coe_castAdd/natAdd, Matrix
   selectors) followed by `norm_num` — also timed out.

Per `CLAUDE.md`, raising `maxHeartbeats` is forbidden. Decomposing the
proof or providing additional projection lemmas (e.g. for past-`f`
rows of `V`, analogous to `toGLM_V_castAdd_*_apply`) would let the
proof bypass the heavy `whnf` work. Out of scope for this cycle —
removed the `bdf3_*` witnesses to keep the file building.

The BDF3 witness was verified algebraically by hand: with `C = 63/11`,
the four obligations reduce to identities like `q[k] = (V q)_k` etc.
that mirror the AM2 proof exactly. A future cycle that adds the
missing past-`f`-row projection lemmas, or that splits each
`fin_cases k` branch into its own tactic block, should land it.

## Discovery

**Predicate-vs.-Taylor mismatch (CRITICAL for higher-order LMMs).**
Lean's `HasOrderGe3` (and presumably `HasOrderGe4` etc.) defines the
order-2 stage moment as `m₂_j := (A c)_j + (U q'')_j`, which is the
*plain* Nordsieck moment. The natural Taylor identity has the moment
`m₂_j = c_j² / 2!` after the standard symmetric weighting, but in
Lean's `HasOrderGe3` predicate the explicit identity is
```
2 · ∑_j B[k,j] · m₂_j + (V q'')_k = q[k] + 2 q'[k] + q''[k]
```
For LMMs whose past-`y` rows force `(U q'')_0 = c_0² ≠ 0` (i.e.
β_s ≠ s/2), the natural Taylor template fails. The remedy is the
shifted template described above. Future cycles formalizing
`HasOrderGe4`/`HasOrderGe5` for LMMs will need analogous shifts:
`q''''_{past-y j} = j⁴ − 6 C j²`-style corrections at each derivative
order, with `C` determined by `(U q^{(k)})_0 = 0`.

## Suggested next approach

1. **Cycle 782** — Add past-`f` projection lemmas for the `V` block of
   `LMM.toGLM` (`toGLM_V_natAdd_shift_apply`, etc.) so simp can work
   on row entries without unfolding the structure body. With those in
   place, retry `bdf3_toGLM_hasOrderGe3` and `bdf3_toGLM_hasOrderGe2/1`
   projections.
2. **Cycle 784+** — Once the projection-lemma toolkit is broadened,
   harvest several stretch witnesses cheaply: AB3, AM3, BDF3, BDF4
   `HasOrderGe3` (and where applicable `HasOrderGe4`) using the
   shifted-moment template. The shift constant for AM3 is `C = s² −
   2 β_s s = 4 − 18/24 = 39/12 = 13/4` (tentative — recompute from
   AM3 coefficients).
3. **Cycle 786+** — Generalize: prove a single lemma
   `LMM.toGLM_hasOrderGe_of_consistent_of_root` that derives
   `HasOrderGe k` from the order-`k` consistency conditions, removing
   per-method witness chasing.
