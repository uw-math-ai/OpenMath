# Issue: AM3 LMM-as-GLM `HasOrderGe4` obstruction (cycle 1138)

## Blocker

The cycle 1138 strategy template (which extended the cycle 1132 `AM3GE3` Pascal
formula to order 4) does not satisfy the §530 `HasOrderGe4` obligation for
`adamsMoulton3.toGLM`. After exhaustive symbolic analysis the constants on
past-`y` and past-`h·f` available as Nordsieck-witness freedom **cannot**
simultaneously close both the last past-`y` row (k = s−1 = 2) and the last
past-`h·f` row (k = 2s−1 = 5).

This is **not** a heartbeat or tactic problem — the witness `q''''N` does not
exist with the cycle 1132 template.

## Context — concrete numerical residues

With the strategy's q'''' template
```
q''''(past-y, j)    = j⁴ − 6 C j²        (C = 27/4)
q''''(past-h·f, j)  = 4 j³ − 12 C j
```
and the existing `AM3GE3` lower-order vectors, the six `q''''_obligation_*`
helpers compile as expected at `k = 0, 1, 3, 4` but report `False` (i.e.
non-zero residue after `simp; norm_num`) at `k = 2` and `k = 5`. After
`ring_nf` the residues are:

```
k = 2 (last past-y, V row uses LMM α/β):     LHS − RHS = −17415/64
k = 5 (last past-h·f, V row = 0):            LHS − RHS = −5805/8
```

Adding a constant `a` to past-`h·f` q'''' (i.e. `q''''(past-h·f, j) = a + 4j³ − 12Cj`)
changes the residues by:

- k = 2: residue gets `+ (5/8)·a`   (because Σ_{l<s} β_l · 1 = ∑β − β_s = 5/8 for AM3)
- k = 5: residue gets `− a`

A constant `b` on past-`y` cancels at every row (it adds `+b` to both LHS via
V·q'''' and RHS), so it has zero net effect.

To close k = 5 we need `a = −5805/8`. To close k = 2 we need `a = +17415/40`.
These are inconsistent.

This was empirically verified by setting `a = −5805/8` in the Lean source: the
goal at k = 5 closes (`goals_after: []`), and the goal at k = 2 becomes
`−8073/8 = −567/2` (i.e. the residue widens to exactly the predicted
`−5805/8 = −46440/64 = −17415/64 + (5/8)·(−5805/8)`).

## Symbolic analysis — why the template cannot work

Define `B = ∑β`, `B₁ = ∑β j`, `B₃ = ∑β j³` (sums over all `j = 0..s`).
Using the LMM order-1, 2, 4 conditions (`∑α j = ∑β`, `∑α j² = 2 B₁`,
`∑α j⁴ = 4 B₃`) and `α_s = 1`, the symbolic LHS at the two critical rows is

```
24·moment(k=s−1)  =  −120 β_s³ s + 144 β_s² s² − 48 β_s s³
24·moment(k=2s−1) =  −120 β_s² s + 144 β_s s² − 48 s³

V·q''''(row s−1)  =  −5 s⁴ + 20 β_s s³ − 24 β_s² s² + b + a·(B − β_s)
V·q''''(row 2s−1) = 0
```

The constraints LHS = RHS reduce (after the `b` cancellations) to:

```
[k = s−1]   a · (B − β_s) = 40 β_s s · (s² − 3 β_s s + 3 β_s²)
[k = 2s−1]  a            = −40 s    · (s² − 3 β_s s + 3 β_s²)
```

For both to hold simultaneously, either
- `s² − 3 β_s s + 3 β_s² = 0`  — discriminant `9 s² − 12 s² = −3 s² < 0` for `s > 0`, so no real solution; or
- `−(B − β_s) · 40 s = 40 β_s s` ⇒ `B = 0`.

For AM3, `B = ∑β = 1/24 − 5/24 + 19/24 + 9/24 = 1 ≠ 0`. The two constraints
therefore force two different values of `a`, and the witness does not exist
in the cycle 1132 template.

For the stretch-goal AB4 (`β_s = 0`, explicit), the constraint at `k = s−1`
becomes `a · B = 0`, i.e. `a = 0` (since `B = ∑β ≠ 0` for any consistent
order-≥1 LMM); and at `k = 2s−1` it becomes `a = −40 s³ ≠ 0`. Same obstruction.

This rules out **all** consistent LMMs (any with `B ≠ 0`) under the
cycle 1132 template, regardless of explicit/implicit, regardless of `s`.

## Why this is not just a "tweak the constants" fix

The strategy's "empirical fit" carve-out (constant D, then linear E) cannot
help, because:

- Any non-constant correction on past-`y` breaks `k = 0` and/or `k = 1`
  (non-last past-`y` rows enforce `f(j+1) = f(j)` for any added correction
  function `f`).
- Any non-constant correction on past-`h·f` breaks `k = 3` and/or `k = 4`
  (same reason on past-`h·f`).
- Constant on past-`y` cancels everywhere.
- Constant on past-`h·f` is the single available DOF, and the two row
  obligations at k = s−1 and k = 2s−1 give it inconsistent values.

So the carve-out at the bottom of the strategy ("If after **two** rounds of
empirical fitting (constants D, then linear E) **two** branches still
report non-zero residues, **stop** and write a structured issue file.")
applies, and we exit with this issue.

## What was tried

1. Wrote out the `AM3GE4` namespace with the strategy's exact template:
   q''''(past-y, j) = j⁴ − 6 C j², q''''(past-h·f, j) = 4 j³ − 12 C j.
   Six per-case `q''''_obligation_*` helpers, dispatched by `fin_cases k`.
2. `lake env lean OpenMath/LMMAsGLM.lean` reported:
   - `q''''_obligation_two` (k = 2): `unsolved goals ⊢ False`
   - `q''''_obligation_five` (k = 5): `unsolved goals ⊢ False`
   - `q'''` headline obligation: `simp` deterministic timeout (separate, see
     below).
3. Replaced `; norm_num` with `ring_nf; sorry` at k=2 and k=5 to read the
   residue, then queried with `mcp__lean-lsp__lean_goal`. Got
   `−35559/64 = −567/2` (residue −17415/64) and `−6885/8 = −135` (residue
   −5805/8) respectively.
4. Tried setting `q''''(past-h·f, j) = −5805/8 + 4j³ − 12Cj` (the value
   forced by k = 5). Lean confirmed: k = 5 closes, k = 2 fails with goal
   `−8073/8 = −567/2`, i.e. the new residue is exactly `−17415/64 +
   (5/8)·(−5805/8) = −46440/64 = −5805/8` as predicted.
5. Symbolic derivation (above) confirms the obstruction is structural: no
   choice of `a, b` constants on past-`h·f` / past-`y` can satisfy both
   constraints because `B = ∑β ≠ 0` for AM3.

## Possible solutions

These are **not** in scope for the cycle 1138 strategy — surfacing them here
for the planner.

1. **Different Nordsieck representation.** The cycle 1132 template chose
   `C := s² − 2 β_s s` and `q'(past-y, j) = j` (no shift on q'). For
   `HasOrderGe4` we may need a fundamentally different choice — perhaps with
   non-zero shifts on the lower-order vectors that cascade into a workable
   q''''. Concretely: perturb `q''(past-y)` by a constant `δ` (allowed; q''
   obligation still holds), which propagates to `q'''(past-y, j) = j³ −
   3(C−δ) j`. The new q''' has effective C-shift `C − δ`. This may give
   enough freedom to balance both q'''' constraints at order 4. Worth
   exploring: parametrize q'', q''', q'''' shifts as four constants
   (`δ_y`, `δ_hf`, `γ_y`, `γ_hf` for q''/q''' past-y/past-h·f, plus the
   `a, b` for q''''), set up the four linear equations from k = s−1, k = 2s−1
   for both q'' obligation, q''' obligation, q'''' obligation, and solve.
2. **Alternative GLM embedding.** It may be that the LMM-as-GLM
   `OpenMath/LMMAsGLM.lean:59` embedding (`r = 2s`, A = β_s constant) is
   correct for `HasOrderGe ≤ 3` but not for `HasOrderGe4`. A higher-`r`
   Nordsieck-style embedding (e.g. `r = s + p` with explicit polynomial
   moment encodings) might be the textbook standard at order 4.
3. **Skip the HasOrderGe4 LMM-as-GLM tier.** The current rotation
   (cycles 1132–1136) landed `HasOrderGe3` for AM3/AB4/BDF4/AM4. If the
   structural obstruction holds for all four, the order-4 frontier is
   unreachable from this embedding and the rotation should pivot back to
   §530 RK or §544 ARK theorems.

## Reference points

- `HasOrderGe4` predicate: `OpenMath/GeneralLinearMethod.lean:253`.
- LMM-as-GLM embedding: `OpenMath/LMMAsGLM.lean:59`.
- Cycle 1132 `AM3GE3` recipe (the working `HasOrderGe3` template):
  `OpenMath/LMMAsGLM.lean:2197`.
- `adamsMoulton3` definition: `OpenMath/AdamsMethods.lean:48`.
- This cycle's task result: `.prover-state/task_results/cycle_1138.md`.
