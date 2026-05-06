# Cycle 1138 Results

## Worked on

`adamsMoulton3_toGLM_hasOrderGe4` in `OpenMath/LMMAsGLM.lean` — the
strategy's primary target.

## Approach

Followed the strategy's recipe verbatim:

1. Inserted the `AM3GE4` namespace immediately after
   `adamsMoulton3_toGLM_hasOrderGe3` (line 2259) and before the `AB4GE3`
   doc-comment header (line 2261), with five Nordsieck input vectors
   `qN, q'N, q''N, q'''N, q''''N`.
2. The new q''''N used the strategy's Pascal-binomial template:
   `j⁴ − 6 C j²` on past-`y`, `4 j³ − 12 C j` on past-`h·f`, with
   `C = 27/4`.
3. Front-loaded six per-case helper theorems
   `q''''_obligation_zero` … `q''''_obligation_five`, each with the
   `simp [LMM.toGLM, adamsMoulton3, Fin.addCases, Fin.sum_univ_succ,
    qN, q'N, q''N, q'''N, q''''N]; norm_num` block.
4. Dispatched the per-case helpers via `fin_cases k` in
   `q''''_obligation`.
5. Wrote the headline `adamsMoulton3_toGLM_hasOrderGe4` mirroring the
   cycle 1132 `_hasOrderGe3` shape with one extra Nordsieck slot.

## Result

**FAILED — structural obstruction documented in
`.prover-state/issues/cycle_1138_am3_hasOrderGe4_obstruction.md`.**

The cycle 1132 Pascal template for q'''' does not yield a `HasOrderGe4`
witness for AM3 LMM-as-GLM. Concretely:

- `q''''_obligation_two` (k = 2, last past-`y`) reports
  `unsolved goals ⊢ False`.
- `q''''_obligation_five` (k = 5, last past-`h·f`) reports
  `unsolved goals ⊢ False`.

After `ring_nf` the residues are `LHS − RHS = −17415/64` at k = 2 and
`−5805/8` at k = 5. The strategy's empirical-fit carve-out (constant
D on past-`y`, then linear E) cannot work:

- A constant on past-`y` cancels at every row (V·q'''' picks up the
  constant exactly once at non-last past-`y`, and once times `1` at last
  past-`y`; RHS picks up the constant exactly once each time too).
- A constant `a` on past-`h·f` changes residue(k=2) by `+(5/8)·a` and
  residue(k=5) by `−a`. The k = 5 constraint forces `a = −5805/8`; the
  k = 2 constraint forces `a = +17415/40`. Inconsistent.
- Linear corrections in `j` break the non-last rows (k = 0, 1 on
  past-`y`; k = 3, 4 on past-`h·f`).

A symbolic derivation (issue file) shows this generalises: for **any**
LMM with `B = ∑β ≠ 0` (i.e. any consistent order-≥ 1 LMM), the cycle 1132
template gives inconsistent constraints for `a` at the last past-`y` and
last past-`h·f` rows. The k = s−1 row forces
`a · (B − β_s) = 40 β_s s · (s² − 3 β_s s + 3 β_s²)`, while k = 2s−1
forces `a = −40 s · (s² − 3 β_s s + 3 β_s²)`. These match only if
`B = 0` or `s² − 3 β_s s + 3 β_s² = 0` (the latter has no real solutions
for `s > 0`).

This means the stretch goal `adamsBashforth4_toGLM_hasOrderGe4`
(β_s = 0, but still B = ∑β ≠ 0) is also unreachable under this template.

## Dead ends

1. **Strategy's Pascal template.** `q''''(past-y, j) = j⁴ − 6 C j²`,
   `q''''(past-h·f, j) = 4 j³ − 12 C j`. Closes k = 0, 1, 3, 4 but fails
   at k = 2, 5.
2. **Constant on past-`h·f`.** Setting `q''''(past-h·f, j) = a + 4j³ −
   12Cj` with `a = −5805/8` (the k = 5 constraint). Verified in Lean
   that this closes k = 5 (`goals_after: []`) but breaks k = 2
   (residue widens from −17415/64 to −5805/8 = −46440/64, exactly as
   predicted by the symbolic analysis).

## Discovery

**The cycle 1132 LMM-as-GLM Pascal template plateaus at order 3.** For
`HasOrderGe4`, the template's constraint structure overdetermines the
single available Nordsieck constant. Specifically:

- The non-last past-`y` rows (k = 0..s−2) force the past-`y` formula up
  to a constant `b` that always cancels.
- The non-last past-`h·f` rows (k = s..2s−2) force the past-`h·f`
  formula up to a constant `a`.
- The last past-`y` row (k = s−1) and last past-`h·f` row (k = 2s−1)
  give two scalar equations in the single unknown `a` (since `b`
  cancels). Generically these two equations are inconsistent, and they
  *are* inconsistent for AM3 (and for any LMM with `B = ∑β ≠ 0`).

This was hidden at orders 2 and 3 because (i) at order 2 the q''
template `j² − C` with `C = s² − 2 β_s s` was specifically tuned so
that `∑U·q'' = 0`, which collapses one of the order-3 constraints to
an automatic identity; and (ii) at order 3 the analogous identity at
k = 2s−1 reduces to `6 β_s s = q + 3q' + 3q'' + q'''` which holds for
any consistent LMM (verified symbolically: `6 β_s s = 6 β_s s` after
expansion).

At order 4 there is no analogous cancellation: the moment expression at
k = 2s−1 evaluates to `−120 β_s² s + 120 β_s s² − 40 s³` (independent
of the LMM-specific α/β beyond `β_s`), and the LHS `24·moment(k=2s−1)`
must match `q + 4q' + 6q'' + 4q''' + q''''(at past-`h·f`, j=s−1)`.
The required `a` to balance this is the **same for every LMM** of given
`s, β_s`, but the corresponding constraint at k = s−1 (which involves
`B − β_s`) gives a different `a`.

## Suggested next approach

**For the planner — do NOT re-issue the same strategy.** The cycle 1132
template is provably blocked at HasOrderGe4 by the symbolic argument in
the issue file. The planner has three reasonable rotations:

1. **Investigate a four-parameter Nordsieck reparameterisation.**
   Allow constant shifts on q''(past-y), q''(past-h·f), q'''(past-y),
   q'''(past-h·f) (call them `δ_y, δ_hf, γ_y, γ_hf`), all of which are
   admissible under the lower-order obligations. These cascade into the
   q'''' obligation as additional linear terms in `(δ_y, δ_hf, γ_y,
   γ_hf)`. With 4 + 2 = 6 unknowns and a small finite number of row
   constraints, the system **may** be solvable — worth setting up
   symbolically before attempting another Lean run. If solvable, the
   resulting q'''' formula will have non-trivial constant offsets and
   extra linear-in-j terms; the cycle 1132 "C = s² − 2 β_s s" lemma is
   still load-bearing but not sufficient at order 4.
2. **Alternative GLM embedding.** Rebuild a higher-`r` LMM-as-GLM
   embedding (e.g. an explicit Nordsieck embedding `r = s + p` for
   polynomial-of-degree-`p` test functions, where the V matrix is the
   shift register on `(y, hy', h²y''/2, …, h^p y^(p)/p!)`). This is
   more textbook-standard for higher-order multistep methods and is
   what Butcher §530 actually uses for the polynomial-Nordsieck
   construction. The current `r = 2s` embedding is a "y/h*f"
   representation, not the polynomial-Nordsieck one.
3. **Pivot away from order 4 LMM-as-GLM.** Rotate to §530 RK
   `HasOrderGe4` (which has its own ladder), or to §544 ARK examples
   (paused per cycle 786 for `r ≥ 2` reasons but with no order-4
   blocker).

The decisive choice should depend on whether the four-parameter
reparameterisation in (1) actually solves the system. I recommend the
planner spend one cycle on a paper-only reparameterisation analysis
before issuing another worker cycle.

## File state

`OpenMath/LMMAsGLM.lean` is unchanged from cycle 1136
(2715 lines, all `_toGLM_hasOrderGe3` witnesses for s = 3, 4 LMM
triplet still landed). The structured issue file
`.prover-state/issues/cycle_1138_am3_hasOrderGe4_obstruction.md`
documents the obstruction in full detail with concrete residues,
symbolic constraints, and dead ends.
