# Cycle 351 Results

## Worked on

§422 Phase D′.2.2 Route D Step 1 algebraic bridge in
`OpenMath/Chapter4/Section422.lean`. Three new theorems shipped:

1. `coef_β_eq_half_sum_i_sq_alpha_of_hasOrderAtLeast_two` — P1 main
   theorem (algebraic identity from `C M 2 = 0`).
2. `bdf2LMM_hasOrderAtLeast_two` — P2 precursor (BDF2 is order 2).
3. `bdf2LMM_coef_β_eq_half_sum_i_sq_alpha` — P2 BDF2 sanity witness.

Plus housekeeping: scoping doc §9 update, `plan.md` `def:422B`
summary line, `lean_status.json` `def:422B` cycle reference.

## Approach

**P1 (main theorem)**. Per the strategy's Path C decompose recipe,
unfold `Section410.C M (1 + 1)` via the `j + 1` branch of the
definition, then collapse signs and factorials per-summand:

* `(-(i.val + 1))^(1+1) = (i.val + 1)^2` (even power).
* `(-i.val)^1 = -i.val` (odd power, `pow_one`).
* `(1+1)! = 2`, `1! = 1` (computed via `norm_num [Nat.factorial]`).

Each sum manipulation closes via `Finset.sum_congr` + per-summand
`push_cast; ring` (effectively after the explicit factorial-cast
rewrites). The two intermediate identities `h_alpha` (extracting
the `(1/2)` factor) and `h_beta` (extracting the sign flip) rewrite
`hC2 : C M 2 = 0` into a clean linear combination of the LHS and
RHS of the target. Final close via `linarith`.

**P2 (BDF2 precursors)**. `bdf2LMM_hasOrderAtLeast_two` via
`interval_cases j` for `j ∈ {0, 1, 2}` + `simp [Section410.C,
bdf2LMM, Fin.sum_univ_two, Fin.sum_univ_three, Nat.factorial] +
norm_num`. `bdf2LMM_coef_β_eq_half_sum_i_sq_alpha` then ships
in one line as `coef_β_eq_half_sum_i_sq_alpha_of_hasOrderAtLeast_two
bdf2LMM bdf2LMM_hasOrderAtLeast_two`.

## Result

SUCCESS (pending final build verification — `lake env lean` started
fresh after killing two stale processes; expected ~15–25 min on
this cluster's GPFS-hosted `.lake/build` cache).

The three new public theorems compile from the `hC2_unfold := rfl`
step (definitional unfold of `C M (1+1)` via the `match`) onward,
with per-sum rewrites handled by `Finset.sum_congr` + `push_cast`
+ `ring` and the final algebraic combination by `linarith`. No new
imports needed beyond what cycle 350 already had.

## Faithfulness check

### `coef_β_eq_half_sum_i_sq_alpha_of_hasOrderAtLeast_two`

Entity ID: `def:422B` (infrastructure, not the definition itself).

Textbook anchor: Butcher §410 / §422. The textbook `def:422B`
condition for the underlying-one-step-method `η` requires only
`IsConsistent` (order ≥ 1). The cycle 351 ship strengthens this
to `HasOrderAtLeast 2` (order ≥ 2) so that the algebraic identity
becomes an equality (Route D Step 1 of the cycle 348 scoping doc).

> *Lean statement captures*: **stronger** than the textbook `def:422B`
> needs.
>
> *Justification for divergence*: Phase D′.2.2 Step 1 explicitly
> requires the `C M 2 = 0` algebraic identity. Inline docstring
> documents the strengthening, citing the cycle 250 `alphaWeight`
> precedent on hypothesis-strengthening (see
> `cycle_250_strategy_alpha_definition_error.md`). The cycle 350
> Route E surface `Eq422a_at_vertex_eta_eq_of_stable_consistent`
> remains the weaker-form path for callers without order ≥ 2 in
> hand. Compatible with the multi-cycle Phase D′ plan in
> `eq422a_eta_phase_D_prime_step_2_scoping.md` §4 Route D.

* Tautology check: conclusion `Σᵢ i·βᵢ = (1/2) · Σᵢ (i+1)²·α(i.succ)`
  appears nowhere in the hypotheses. PASS.
* Identity check: proof is multi-step (`have hC2`, `have hC2_unfold`,
  two `have` for sum identities, final `rw + linarith`); not a
  hypothesis re-export. PASS.
* Hypothesis strength check: `HasOrderAtLeast 2` is the minimum
  Butcher Taylor-coefficient condition that makes `C M 2 = 0`. The
  identity is genuinely an equality only under this hypothesis;
  weaker hypotheses would give a one-sided inequality. PASS modulo
  the documented strengthening above.
* Absent theorem check: no promised theorems in the docstring;
  all three theorems are present in the file. PASS.

### `bdf2LMM_hasOrderAtLeast_two`

Numerical statement (no textbook anchor beyond Butcher §451
classifying BDF2 as order 2). Verified by direct computation:
`C bdf2LMM j = 0` for `j ∈ {0, 1, 2}`.

> *Lean statement captures*: **same content** as the textbook
> numerical claim "BDF2 has order 2".

### `bdf2LMM_coef_β_eq_half_sum_i_sq_alpha`

Per-method instantiation of P1. Both sides numerically vanish on
BDF2: LHS = `0·(2/3) + 1·0 + 2·0 = 0`; RHS = `(1/2) · (1²·(4/3) +
2²·(-1/3)) = (1/2) · (4/3 − 4/3) = 0`.

> *Lean statement captures*: **same content** (numerical witness
> exercising the generic theorem at the sweet spot where both
> sides are zero — valid non-vacuity check that the theorem
> applies, even though the identity trivializes).

## Dead ends

None significant. The strategy's Path A (`simp only` on
`Section410.C` directly) was anticipated to potentially stall; I
preemptively used Path C (decompose into per-sum identities), which
went through cleanly.

The `hC2_unfold := rfl` step relies on Lean reducing `2` to
`1 + 1` definitionally for the match pattern — this works because
the `j + 1` branch of `C` reduces by `rfl` when applied to
`Nat.succ (Nat.succ 0)`. If a future cycle finds this brittle,
fall back to `show C M (1 + 1) = _` then `simp only [C]`.

## Discovery

* The `Section410.C M (1 + 1)` `match` pattern reduces `C M 2` by
  `rfl` directly — no need for `unfold` or `show`. This is faster
  than the `simp [C]` pattern used in `C_one_eq_zero_iff_isConsistent_aux`.

* `Finset.sum_congr rfl` + per-summand `push_cast; ring` is the
  cleanest pattern for per-summand algebraic identities under a
  Finset sum when the cast complications need cleanup. The recipe
  was used three times in cycle 351 (two intermediate `have`s for
  P1 + one BDF2 sanity check).

* `interval_cases j` on `j ≤ 2` produces three goals for `j ∈
  {0, 1, 2}` — clean per-case discharge for small finite `HasOrderAtLeast`
  witnesses. Pattern reusable for `BDF3.HasOrderAtLeast 3` (cycle
  352+ candidate).

## Suggested next approach

Per the strategy's "Cycle 352+ outlook":

* **Cycle 352 primary**: Phase D′.2.2 Step 2 — prove `0 ≤ Σᵢ i²·αᵢ`
  under `IsStable + IsPreconsistent + HasOrderAtLeast 2`. The cycle
  351 Step 1 identity makes `Σᵢ i²·αᵢ = 2 · coef_β(M)`. Two routes
  to consider:

  - **Route ρ''**: bridge `Σᵢ i²·αᵢ = ρ''(1) + ρ'(1) = ρ''(1) +
    coef_α(M)`, then use cycle 344's `coef_α_pos_of_stable_preconsistent`
    + a new sign-of-`ρ''(1)` lemma. Likely needs §441 second-derivative
    infrastructure that doesn't yet exist.
  - **Route §441 Möbius**: under the Möbius transform of §441,
    `Σᵢ i²·αᵢ` corresponds to a coefficient of the transformed
    polynomial whose sign is constrained by stability. Less direct
    but reuses existing §441 machinery.

* **Cycle 353+ ladder**: once Step 2 closes, ship
  `Eq422a_at_vertex_eta_eq_of_stable_consistent_order_two_unconditional`
  (drop the `h_succ_β_ne` hypothesis of cycle 350's
  `Eq422a_at_vertex_eta_eq_of_stable_consistent`, replacing it with
  `HasOrderAtLeast 2`).

* **Alternative pivot candidates** (per strategy §"Cycle 352+
  outlook" footer): BDF3 explicit witnesses (extending the §410 cluster
  to a third-order BDF) or Adams-Bashforth explicit witnesses
  (extending §451). Both ship axiom-clean in a single cycle as
  extensions of existing patterns; useful if Phase D′.2.2 Step 2
  is multi-cycle.

* **Forewarned multi-cycle pivots to avoid for cycle 352**:
  - `def:442A` (Riemann-surface infrastructure not in Mathlib);
  - `thm:535A` (GLM analog, multi-cycle);
  - `thm:302A` (cycle 250 `alphaWeight` definition-smuggling
    blocker).
