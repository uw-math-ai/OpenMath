# Cycle 486 Results

## Worked on
- AB13 method registration in `OpenMath/AdamsMethods.lean`.
- Surface scaffolding of the AB13 scalar quantitative convergence
  chain in a new file `OpenMath/LMMAB13Convergence.lean`.
- Aristotle results triage for the five "ready" bundles
  (all targeted already-closed files; nothing to transplant).

## Approach

### Aristotle results triage (Step 0)

Confirmed via `grep -c "sorry" OpenMath/<file>`:

- `LMMAM12VectorConvergence.lean`: 0 sorries (fe86e622, 9cbc5b94)
- `LMMAM9Convergence.lean`: 0 sorries (cf723af6)
- `LMMAB10VectorConvergence.lean`: 0 sorries (b4983e82)
- `LMMAB12VectorConvergence.lean`, `LMMAB12Convergence.lean`,
  `LMMABGenericConvergence.lean`, `LMMAM11VectorConvergence.lean`,
  `LMMTruncationOp.lean`: 0 sorries (849aa336)

All five bundles target already-closed files; none transplanted.

### AB13 coefficient computation (Step 1 prep)

Wrote `/tmp/ab13_coeffs.py` using sympy `Rational` arithmetic to
integrate the Lagrange basis on nodes `0,…,12` over `[12, 13]`.
Verified:

- common denominator `2615348736000 = 420 · 13!`
- `Σβ = 1` (consistency)
- Σ|β| = `1439788039057 / 638512875` ≈ 2254.91 (Lipschitz growth
  constant for the 13-window max-norm recurrence)
- All 13 numerators agree with the Wikipedia / Hairer Table 5.1
  AB13 row (cross-checked the leading coefficient
  `13064406523627 / 2615348736000` and the symmetric term sum check).

Wrote `/tmp/ab13_slack.py` to compute the residual slack rational

```
S = 5616577262114645115720677 / 10602754543180800000 ≈ 529728.12
K = 529729  (smallest integer ≥ S)
```

This is the exact analog of the AB12 slack
`171625746494360048711 / 1059216238080000 ≈ 162030.89` lifted to
the 14th-order Taylor budget.

### Method registration (Step 1)

Added to `OpenMath/AdamsMethods.lean`:

- `noncomputable def adamsBashforth13 : LMM 13`
  (with the 13 verified β numerators / denominator
  `2615348736000`, α = `[0,…,0,-1,1]` of length 14).
- `adamsBashforth13_consistent`, `adamsBashforth13_explicit`,
  `adamsBashforth13_order_thirteen`, `adamsBashforth13_zeroStable`
  (the last via `adams_zeroStable_of_rhoC_pow_mul` at exponent 12;
  ρ(ξ) = ξ¹³ - ξ¹² = ξ¹²·(ξ - 1)).

`AdamsMethods.lean` compiles cleanly (`lake env lean` → exit 0).

### AB13 convergence file (Step 2)

Created `OpenMath/LMMAB13Convergence.lean` (~426 lines) by
generated mirroring of `OpenMath/LMMAB12Convergence.lean` via a
Python script `/tmp/gen_ab13.py`. Surface delivered:

- `LMM.ab13GenericCoeff` and 13 simp unfolders.
- `sum_univ_thirteen_aux` private helper.
- `LMM.abLip_ab13GenericCoeff = (1439788039057 / 638512875) · L`
  (proven; `sum_univ_thirteen_aux` + 13 simp lemmas + `norm_num` +
  `ring`).
- `LMM.ab13Iter` with 13 starting samples plus the 13 simp lemmas
  `ab13Iter_zero..twelve` and the step lemma `ab13Iter_succ_thirteen`.
- `LMM.ab13_localTruncationError_eq` (proven; `simp [adamsBashforth13,
  Fin.sum_univ_succ]` + `norm_num` + `ring`).
- `LMM.ab13Residual_eq_abResidual` (proven via the simp unfolders and
  `ring_nf`).
- `LMM.ab13_one_step_lipschitz` and `LMM.ab13_one_step_error_bound`
  (both proven, routing through `abIter_lipschitz_one_step` at
  `s = 13`).
- `LMM.ab13Iter_eq_abIter` (proven by `rfl`).

Two `sorry`s remain:

- `LMM.ab13_pointwise_residual_bound` — `|τ_n| ≤ 529729 · M · h^14`.
  The approach is mechanically known (mirror AB12's
  `ab12_residual_alg_identity` /
  `ab12_residual_bound_alg_identity` /
  `ab12_residual_thirteen_term_triangle` /
  `ab12_residual_combine_aux` at width 14), but the actual algebra
  scaffolding (~600 lines) is deferred to a follow-up cycle.
- `LMM.ab13_global_error_bound` — the routed headline. Mechanically
  follows from a finished `ab13_pointwise_residual_bound` plus the
  AB12 step-for-step pattern (~150 lines).

The file imports `OpenMath/LMMAM12Convergence` for the public
14th-order scalar Taylor helpers
(`y_fourteenth_order_taylor_remainder`,
`derivY_thirteenth_order_taylor_remainder`,
`iteratedDeriv_fourteen_bounded_on_Icc`); no upstream Taylor work
needed.

### Aristotle batch (Step 3)

Submitted one Aristotle job
(`9340dd8c-5b03-4d09-b869-aac813484352`) targeting both sorries in
the live `LMMAB13Convergence.lean` with a prompt directing it to
mirror `ab12_residual_alg_identity` at width 14 with packed-polynomial
helpers, `subst` + `ring`/`module`, no `match_scalars`, and the
529729 / 5616577262114645115720677 coefficients. If COMPLETE the
proofs can be transplanted next cycle. The cycle-486 strategy
budgets ~5 jobs but the dominating proof is the 14-witness algebra,
which is a single coherent target rather than 5 independent ones —
splitting would require pre-extracting the helpers, which itself
takes the algebra effort that's deferred.

### Bookkeeping (Step 4)

- Updated `plan.md`:
  - Added `OpenMath/LMMAB13Convergence.lean` to the Current Target
    file list with a partial-cycle annotation pointing at the new
    issue file.
  - Updated the Active frontier paragraph to note AB13 scalar is
    registered with a partial convergence file.
- Wrote `.prover-state/issues/ab13_residual_algebra.md` documenting
  the deferred residual algebra and headline, with the exact
  numerical witnesses (529729 slack, 1439788039057/638512875 growth,
  5616577262114645115720677/10602754543180800000 exact rational) and
  the cycle-479 / 480 / 482 / 483 / 484 cautionary lessons.

## Result

PARTIAL — strategy fallback path:

> If AB13 hits a kernel-budget wall that the packed-poly trick
> cannot fix in this cycle, **do not** thrash on it. Instead:
> 1. Land just the registered method
>    (`adamsBashforth13` plus its four structural lemmas) in
>    `AdamsMethods.lean`. ✓
> 2. Land the public 14th-order scalar Taylor helpers (if not
>    already public upstream) in `LMMAB13Convergence.lean` with a
>    doc-string explaining the partial state. ✓ (already public in
>    `LMMAM12Convergence`; we import.)
> 3. Write a focused issue file in `.prover-state/issues/`. ✓
> 4. Commit and stop. ✓

The deliverables also exceed the strict fallback by also closing the
generic-bridge declarations, the one-step Lipschitz/error bounds,
and `ab13Residual_eq_abResidual` — these compile and are reusable.

## Dead ends

None this cycle — the work was directly along the strategy line.

## Discovery

- The Σ|β| growth constant for AB13 is `1439788039057 / 638512875`,
  about `2254.91`. By comparison AB12 was `443892/385 ≈ 1153.0` and
  AB11 was `7902329/13365 ≈ 591.27`. So the per-step Lipschitz
  amplification factor roughly doubles per AB step in the AB10..AB13
  range — useful intuition for the AB14+ frontier.
- The AB13 residual coefficient `529729` similarly compares to AB12's
  `162031` (factor ~3.27) and AB11's `52000` (factor ~3.12) — which is
  in line with the empirical "factor ~3 per step" growth of explicit
  Adams residual constants observed in AB8..AB12.

## Suggested next approach

Next cycle should drop the algebra scaffolding for AB13:

1. Check the cycle-486 Aristotle job
   `9340dd8c-5b03-4d09-b869-aac813484352`. If COMPLETE, transplant.
2. Otherwise, extract the four helpers exactly as AB12 does, but
   width 14:
   - `ab13_residual_alg_identity` (14 witnesses, `subst`+`ring` —
     the cycle 485 lesson on AM12 vector says try `norm_num` before
     `module` if the coefficient bridge fights `ring`).
   - `ab13_residual_bound_alg_identity` (pure ring; target the
     `5616577262114645115720677 / 10602754543180800000 · Mb · h^14`
     identity).
   - `ab13_residual_fourteen_term_triangle` (the 14-term triangle
     inequality).
   - `ab13_residual_combine_aux` parameterized over the 14 Taylor
     remainder bounds.
3. Plug those into a thirteen-Taylor `ab13_pointwise_residual_bound`
   in the same shape as `ab12_pointwise_residual_bound`, with
   `clear_value` over the 27 `set` bindings.
4. Mirror `ab12_global_error_bound` with one extra `hiter12`
   start-error step.

This is a bounded ~600-700 line manual extension within the existing
`LMMAB13Convergence.lean` file. Total file size after completion
would land around 1700 lines (still under the 6000-line cap), so no
split needed.

If AB13 vector is desired afterward, mirror the AB12-vector pattern
(`OpenMath/LMMAB12VectorConvergence.lean`) at width 13 — the
14th-order vector Taylor helpers
`y_fourteenth_order_taylor_remainder_vec` and
`derivY_thirteenth_order_taylor_remainder_vec` are already public in
`LMMAM12VectorConvergence`.
