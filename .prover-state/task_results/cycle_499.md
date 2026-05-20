# Cycle 499 Results

## Worked on

Phase α'.5.2.0 ship per `def_422B_phase_alpha_prime_5_2_scoping.md` §B
— `elementaryWeightQ_phi_inv_bushy₄` (order-5 broom closed form for
`Φ_{η_q⁻¹}`) + Priority 2 m=0 corollary
`powRep_sum_eq_of_agreement_at_bushy₄_zero` + two `⟦explicitEuler⟧`
non-vacuity examples.

## Approach

Verbatim mechanical port of cycle 370's `elementaryWeightQ_phi_inv_bushy`
proof body (`Section422.lean:3011–3169`) with one extra cons-case
unfold layer per helper:

* Reuse 9 cycle 367/368/370 helpers (`h_inv_v`, `h_vertex`,
  `h_dw_cherry`, `h_cherry`, `h_dw_broom₃`, `h_broom₃`, `h_dw_bushy`,
  `h_bushy`) verbatim — `h_dws_bushy` from cycle 370 is *not* reused
  as a separate named helper, since the layer-3 expansion is captured
  directly inside `h_dws_bushy₄`'s nested `h_prod_step_3` step.
* Three new `_bushy₄` helpers (`h_dw_bushy₄`, `h_bushy₄`,
  `h_dws_bushy₄`) extending cycle 370 with one additional
  `h_prod_step_3` layer for the fourth child.
* Main computation: `_inv_mk` + `_mk` × 5 + `h_sum` substitution +
  `Finset.sum_*_distrib` chain (`add, sub, add, sub`) + `← Finset.mul_sum`
  × 4 + 5 helper rewrites + `ring`.

No Aristotle submitted — the cycle 370 template is mechanical enough
that manual closure was direct. No Aristotle context budget needed.

## Result

SUCCESS — file compiles axiom-clean, both new public theorems return
`[propext, Classical.choice, Quot.sound]`, non-vacuity example pins
to `-1` (matches cycle 498 task results Discovery #3), m=0 corollary
non-vacuity example discharges five `rfl` agreements.

LOC delta: Section422.lean 12564 → 12932 (+368 LOC, including ~50 LOC
of structured docstrings).

Sorry count: 5 (4 docstring + 1 grandfathered cycle 365 sorry at
line 2279). Unchanged from cycle 498.

§422 axiom-clean streak: 70 substantive + 6 doc → **72 substantive +
6 doc** (cycles 336–499).

## Faithfulness check

This cycle introduced two new public symbols. Both are derived
algebraic identities (closed-form expansions of the cycle 358
`elementaryWeightQ_phi_inv_mk` formula at named `bushy₄ = mk[v,v,v,v]`
+ five-hypothesis m=0 specialization of cycle 365's Sub-lemma A), not
textbook entity definitions.

### `elementaryWeightQ_phi_inv_bushy₄`

* Entity ID: derived helper for `def:422B`'s Phase α'.5.2 ladder per
  `.prover-state/issues/def_422B_phase_alpha_prime_5_2_scoping.md` §B.
  No direct textbook statement — this is an algebraic identity
  consumed by `inversePolyTree`'s upcoming 6-arm dispatch (cycle 500's
  Phase α'.5.2.1 job).
* Lean statement captures: derived from cycle 358's
  `elementaryWeightQ_phi_inv_mk` formula at `bushy₄`, via per-row
  factorisation `(M.inverse.eW vertex + Σⱼ M.A i j)^4` and binomial
  expansion `(s − v)⁴ = s⁴ − 4s³v + 6s²v² − 4sv³ + v⁴`.
* TAUTOLOGY check: the LHS `Φ_{η⁻¹}(bushy₄)` does NOT appear verbatim
  as the RHS — the RHS is a polynomial in five DISTINCT named
  elementary weights (`vertex`, `cherry`, `broom₃`, `bushy`,
  `bushy₄`). The `-Φ_η(bushy₄)` term on the RHS is `Φ_{η}(bushy₄)`
  (not `Φ_{η⁻¹}(bushy₄)`), so no tautology.
* IDENTITY check: the proof is NOT `exact h`; it routes through 8
  cycle-367/368/370-reused helpers + 3 new `_bushy₄`-suffixed helpers
  + a substantial sum manipulation + `ring`. Real mathematical work.
* HYPOTHESIS strength: only `η_q : Quotient PhiEquivalent.setoidSigma`
  parameter (no additional hypotheses). Faithful to the cycle 370
  bushy template — no strengthening over `_inv_bushy`'s signature.

### `powRep_sum_eq_of_agreement_at_bushy₄_zero`

* Entity ID: m=0 specialization of cycle 365's Sub-lemma A
  `powRep_sum_eq_of_strict_subtree_agreement` (grandfathered sorry
  at Section422.lean:2279). Mirrors the m=0 corollary pattern used
  in cycles 366/367/368/369/370/371/372/378/384/386/491/492/493/494.
* Lean statement captures: under agreement at the five named subtrees
  `vertex`, `cherry`, `broom₃`, `bushy`, `bushy₄` (= the factorisation
  basis of `elementaryWeightQ_phi_inv_bushy₄`), the `η_q^(-1)` images
  at `bushy₄` coincide.
* TAUTOLOGY check: the conclusion is an equation between two distinct
  `η_q ^ (-(((0+1):ℕ):ℤ))` images (LHS = `η_q⁻¹`, RHS = `η_q'⁻¹`).
  No hypothesis matches the conclusion verbatim.
* IDENTITY check: the proof routes through a `h_pow` cast bridge
  (`Nat.cast_one + zpow_neg_one`) + two applications of
  `elementaryWeightQ_phi_inv_bushy₄` + five `h_*` substitutions.
  Real work.
* HYPOTHESIS strength: five agreement hypotheses correspond exactly
  to the five named elementary weights in the closed form's RHS.
  No extra hypotheses. Faithful to the cycle 370 m=0 corollary
  template.

## Dead ends

None — the cycle 370 template is mechanical enough that the depth-4
extension applied without rework. The only minor design call was
inlining `h_dws_bushy` (cycle 370's depth-3 source-aware helper)
directly inside `h_dws_bushy₄`'s `h_prod_step_3` step rather than
naming it separately. This kept the LOC footprint identical to a
cycle-370-verbatim port (no redundant depth-3 derivation).

The `h_sum` `sum_*_distrib` chain order required care: depth-4 has
5 terms with signs `+, -, +, -, +` (vs cycle 370's depth-3 `+, -, +,
-`), so the outer-to-inner chain is `add, sub, add, sub` (one more
distrib step than cycle 370). Verified by parsing the per-summand
expression left-to-right.

## Discovery

1. **The cycle 370 nested-helper recipe extends linearly to depth k**:
   adding one extra child to a broom tree requires exactly one
   additional `h_prod_step_k` layer per helper, with the `show + rw`
   chain identical in shape. This validates the scoping doc §6.2's
   `~90–110 LOC` estimate for cycle 500's k=4 dispatch ship.

2. **Binomial coefficient signs** in the closed form (`-1, +4, -6,
   +4, -1`) match the standard `(s − v)⁴` Pascal-triangle row 4. The
   §422 closed forms for depth-k brooms (`mk [v, ..., v]` with k
   children) are thus parameterised entirely by Pascal row k — a
   useful observation for cycle ~501+'s extension to non-symmetric
   quadruples (where the inner-sum bookkeeping varies but the outer
   binomial expansion stays the same).

3. **Build cost** of the `_inv_bushy₄` block was significantly
   shorter than the cycle 386 (`mkBroomCherry`, +801 LOC, ~5–6 min)
   precedent, since the new code is purely additive (no `inversePolyTree`
   dispatch table to recompile). Warm rebuild stayed inside the
   3-min default-heartbeat envelope.

## Suggested next approach

**Cycle 500 (Phase α'.5.2.1)** per scoping doc §6.2:

* Ship `tetrachildPolynomial` (5-block absorbed Pascal-row-4 outer
  polynomial) + `tetrachildCrossTerm` (4-branch if-then-else cascade)
  defs.
* Extend `inversePolyTree`'s pattern match from 5 arms to 6 arms
  (adding the symmetric quadruple `[v, v, v, v]` arm dispatching to
  `tetrachildPolynomial`).
* Ship `inversePolyTree_bushy₄` calibration witness theorem (the
  Phase γ bridge connecting `inversePolyTree`'s `bushy₄` evaluation
  to `elementaryWeightQ_phi_inv_bushy₄`).
* Anticipated LOC: ~90–110 LOC. Build cost may approach 1500s per
  cycle 401's 5-arm extension precedent; monitor and consider sibling
  file extraction if exceeded.

**Forward agenda** (cycles 501–509+, Phase α'.5.2.k):
non-symmetric quadruple witnesses ladder per §5.3, starting with
`mkVertexVertexVertexCherry := mk[v, v, v, c]` (Block 6 single-cherry
arm). One witness per cycle, mirroring the cycle 403/491–494 k=3
ladder template.

**Eventual Phase β.2 carve-out** (cycle ~512+): the cycle 365 sorry
becomes attackable at tree-order ≤ O once Phase α'.5.2 + β.1/γ
extensions ship.
