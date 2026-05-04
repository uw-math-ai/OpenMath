# Cycle 792 Results

## Worked on
§530 GLM order witnesses for the four embedded-pair main methods
(Heun–Euler 2(1), Bogacki–Shampine 3(2), RKF45, DOPRI5) — i.e. the
`*_mainMethod_toGLM_hasOrderGeN` family in `OpenMath/RKAsGLM.lean`.

## Approach
Followed the strategy verbatim:

1. Added `import OpenMath.EmbeddedRK` next to the other concrete-tableau
   imports at the top of `OpenMath/RKAsGLM.lean`.
2. Appended 12 term-mode witnesses at the end of the file, each
   feeding a pre-existing `_main_orderN` certificate and the
   `_consistent.main_consistent` field through one of the existing
   `ButcherTableau.toGLM_hasOrderGeN` bridges.

No new infrastructure, no new bridge lemmas, no `by` blocks beyond
what the strategy spelled out.

## Result
SUCCESS — all 12 theorems landed sorry-free, exit code 0 from
`lake env lean OpenMath/RKAsGLM.lean`.

Theorems added (in `ButcherTableau` namespace, end of `RKAsGLM.lean`):

Headline (4):
- `rkHeunEuler21_mainMethod_toGLM_hasOrderGe2`
- `rkBS32_mainMethod_toGLM_hasOrderGe3`
- `rkRKF45_mainMethod_toGLM_hasOrderGe5`
- `rkDOPRI5_mainMethod_toGLM_hasOrderGe5`

Lower-order projections (8):
- `rkBS32_mainMethod_toGLM_hasOrderGe2`
- `rkBS32_mainMethod_toGLM_hasOrderGe1`
- `rkRKF45_mainMethod_toGLM_hasOrderGe4`
- `rkRKF45_mainMethod_toGLM_hasOrderGe3`
- `rkRKF45_mainMethod_toGLM_hasOrderGe2`
- `rkDOPRI5_mainMethod_toGLM_hasOrderGe4`
- `rkDOPRI5_mainMethod_toGLM_hasOrderGe3`
- `rkDOPRI5_mainMethod_toGLM_hasOrderGe2`

Total = 1 + 3 + 4 + 4 = 12, matching the strategy.

The pre-existing simp arg-lint warnings on the file remain (these
predate this cycle); the benign `PANIC at Lean.Expr.appArg!` simproc
trace also still appears but `lake env lean` exits 0 with no
diagnostics flagged as errors. Treated as success per the strategy's
acceptance criterion.

## Dead ends
None. The destructuring shapes from the strategy
(`h.1.1`, `h.1.2.1`, `h.1.2.2.1`, `h.1.2.2.2.1` for HasOrderGe3 from
HasOrderGe5; `h.1` for HasOrderGe4 from HasOrderGe5) matched the
actual definitions in `OpenMath/RungeKutta.lean` exactly:

- `HasOrderGe5 = HasOrderGe4 ∧ order5a ∧ ... ∧ order5i` (right-assoc)
- `HasOrderGe4 = order1 ∧ order2 ∧ order3a ∧ order3b ∧ order4a ∧ ... ∧ order4d`

So projection `h.1.1` is `order1`, `h.1.2.1` is `order2`, etc., as the
strategy described.

## Discovery
Stretch goals (the three `_hasOrderGe1` witnesses for Heun–Euler,
RKF45, DOPRI5) were not added in this cycle to keep the diff at the
exact 12 the strategy enumerated. They are trivial one-line
consistency-only bridges and can be folded into a future cycle if the
planner wants the full ladder.

## Suggested next approach
- **Most natural continuation**: the embed-method side of the same
  four pairs (`rkHeunEuler21.embedMethod`, `rkBS32.embedMethod`,
  `rkRKF45.embedMethod`, `rkDOPRI5.embedMethod`). Each already has a
  tableau-level `_embed_orderN` certificate in
  `OpenMath/EmbeddedRK.lean` (e.g. `rkHeunEuler21_embed_order1`,
  `rkBS32_embed_order2`, `rkRKF45_embed_order4`, `rkDOPRI5_embed_order4`)
  and `_consistent.embed_consistent` provides the consistency hypothesis.
  Same plug-and-play pattern as cycle 792, ~8–12 more witnesses.
- **Or**, the three stretch `_hasOrderGe1` witnesses noted above.
- **Or**, pivot to §531 truncation-error infrastructure if §530's
  embed-method coverage is considered done after the embed-side
  follow-up.
- LMM-side §530 for `s ≥ 5` HasOrderGe2 / `s ≥ 3` HasOrderGe3 stays
  blocked per cycles 786/789 (heartbeat ceiling on the natural
  Nordsieck Taylor template).
