# Cycle 353 Results

## Worked on
BDF3 wire-up per the planner's strategy:
* `Section451.lean`: `bdf3LMM` definition + `bdf3LMM_isPreconsistent`,
  `bdf3LMM_satisfiesEq404b`, `bdf3LMM_isConsistent` (three §404
  non-vacuity witnesses).
* `Section422.lean`: `bdf3LMM_hasOrderAtLeast_three` (the project's
  first order-≥-3 LMM witness) and
  `bdf3LMM_coef_β_eq_half_sum_i_sq_alpha` (cycle 351 Route D Step 1
  identity exercised at BDF3 — both sides vanish, parity-with-BDF2
  trivial witness).

Six new public declarations total. No sorries. All declarations
ship axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## Approach
Followed the planner's recipe verbatim:

1. Inserted `bdf3LMM` definition in `Section451.lean` immediately
   after `bdf2LMM` (between line 151's `α_zero := rfl` and the
   `bdf2GWitness` block). Used `noncomputable def` + nested `match`
   on `Fin 4` (α) and `Fin 4` (β) per the BDF2 template, scaled to
   `k = 3` with α=(-1, 18/11, -9/11, 2/11), β=(6/11, 0, 0, 0).
2. Added preconsistency / (404b) / consistency witnesses immediately
   after the definition. Each uses
   `simp [...predicate..., bdf3LMM, Fin.sum_univ_three, Fin.sum_univ_four]
    \n norm_num`, matching the BDF2 precedent at Section451:331-339.
3. Built `Section451` once to verify the new definition cached
   correctly (cycle 352's discovery: `lake env lean` does NOT update
   `.olean`, so `lake build OpenMath.Chapter4.Section451` is required
   before consumer-file builds).
4. Added `bdf3LMM_hasOrderAtLeast_three` to `Section422.lean` after
   the trapezoidal block (line 1366 region). Four-arm `interval_cases j`
   matching the trapezoidal/BDF2 template, scaled to `j ∈ {0, 1, 2, 3}`.
5. Added `bdf3LMM_coef_β_eq_half_sum_i_sq_alpha` after the order-3
   witness. Routed through
   `coef_β_eq_half_sum_i_sq_alpha_of_hasOrderAtLeast_two` with an
   inline downcast from `HasOrderAtLeast 3` to `HasOrderAtLeast 2`
   via `intro j hj; exact bdf3LMM_hasOrderAtLeast_three j (by omega)`
   (per the planner's note: do NOT search for `HasOrderAtLeast.mono`).
6. Built `Section422`. Verified all six new symbols with
   `#print axioms` — all clean.

## Result
SUCCESS — both files build clean, all six new declarations
axiom-clean. No sorries opened.

Build evidence:
* `lake build OpenMath.Chapter4.Section451` → ✔ Built (230s)
* `lake build OpenMath.Chapter4.Section422` → ✔ Built (163s)

Axiom check:
```
'bdf3LMM' depends on axioms: [propext, Classical.choice, Quot.sound]
'bdf3LMM_isPreconsistent' depends on axioms: [propext, Classical.choice, Quot.sound]
'bdf3LMM_satisfiesEq404b' depends on axioms: [propext, Classical.choice, Quot.sound]
'bdf3LMM_isConsistent' depends on axioms: [propext, Classical.choice, Quot.sound]
'bdf3LMM_hasOrderAtLeast_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'bdf3LMM_coef_β_eq_half_sum_i_sq_alpha' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Faithfulness check

**(1) `bdf3LMM`** — not a textbook *entity* (no `def_xxx.json` file
exists); BDF3 is a standard universally-attested 3-step BDF method
that the planner verified on paper. The Lean coefficients
α=(-1, 18/11, -9/11, 2/11), β=(6/11, 0, 0, 0) match the textbook
recurrence `y_n = (18/11) y_{n-1} − (9/11) y_{n-2} + (2/11) y_{n-3}
+ (6/11) h f(x_n, y_n)` under the §404 normalisation `α 0 = -1`.
**No textbook divergence**.

**(2) `bdf3LMM_isPreconsistent`** — entity `def:404A`. The Lean
statement instantiates `LinearMultistepMethod.IsPreconsistent`
(`∑ᵢ M.α i.succ = 1`) at `bdf3LMM`. Direct rational arithmetic
`18/11 − 9/11 + 2/11 = 1` via `simp + norm_num`. **Same content**.
Identity check: PASS (`norm_num` does real arithmetic, not a
hypothesis re-export).

**(3) `bdf3LMM_satisfiesEq404b`** — entity `def:404B`'s (404b)
component. Direct arithmetic `1·(18/11) + 2·(−9/11) + 3·(2/11) = 6/11
= 6/11 + 0 + 0 + 0`. **Same content**. Identity check: PASS.

**(4) `bdf3LMM_isConsistent`** — entity `def:404B`. Trivial
conjunction `⟨isPreconsistent, satisfiesEq404b⟩`, matching the
trapezoidal/BDF2 precedent. **Same content**.

**(5) `bdf3LMM_hasOrderAtLeast_three`** — numerical specialisation
of `def:410A`'s `HasOrderAtLeast` predicate at `p = 3`. Verified
by direct computation of `C bdf3LMM j` for `j ∈ {0, 1, 2, 3}`.
Both α-side and β-side moments cancel exactly: at `j = 2` the
α-sum `[18/11 − 36/11 + 18/11]/2 = 0`; at `j = 3` the α-sum
`[−18/11 + 72/11 − 54/11]/6 = 0`. β contributes only at index 0
where `i^j = 0` for `j ≥ 1`. The textbook claim "BDF3 has order 3"
is standard. **Same content**. Tautology check: PASS. Identity
check: PASS (real arithmetic, not hypothesis re-export).

**(6) `bdf3LMM_coef_β_eq_half_sum_i_sq_alpha`** — specialisation of
cycle 351's `coef_β_eq_half_sum_i_sq_alpha_of_hasOrderAtLeast_two`
at `M = bdf3LMM`. Proof is a single application of the cycle 351
theorem (downcast from order ≥ 3 to order ≥ 2 inline via `omega`).
The mathematical work is in cycle 351. This is a non-vacuity witness
where both sides vanish (trivial identity `0 = 0` exercised at an
order-3 method). **Same content** as cycle 351's identity. Identity
check: PASS (the witness exercises real arithmetic of the underlying
identity at concrete coefficients; the proof routes through a
non-trivial theorem, not a hypothesis re-export).

## Dead ends
None this cycle. The planner's recipe matched the BDF2/trapezoidal
precedent verbatim; both files built first attempt.

## Discovery
* The planner's hypothesis that BDF3's α/β use `match` (not `if`),
  and therefore need `Fin.sum_univ_three` + `Fin.sum_univ_four` in
  the simp sets (plus `norm_num` for rational arithmetic), proved
  correct. The trapezoidal/Section404 idiom of "simp alone closes
  it" only works for the `if-then-else` field encoding used in
  Section404's witnesses; BDF methods need the `Fin.sum_univ_n`
  hint plus `norm_num`.
* `coef_β_eq_half_sum_i_sq_alpha_of_hasOrderAtLeast_two`'s
  hypothesis-downcast pattern (intro a fresh `j`, then `exact
  bdf3LMM_hasOrderAtLeast_three j (by omega)`) is the canonical
  way to route an order-3 witness through an order-2-hypothesised
  lemma without depending on a `.mono` lemma that may not exist
  in `Section410.lean`.
* This is the **first order-≥-3 LMM witness in the project**.
  Previous witnesses cap at order 2 (BDF2, trapezoidal).

## Suggested next approach
Three plausible cycle 354 directions per cycle 352's outlook,
narrowed by today's BDF3 ship:

1. **`bdf3LMM_isStable`** (~50–80 LOC) — port cycle 346's
   `bdf2LMM_isStable` recipe to k=3. BDF3's homogeneous recurrence
   has characteristic polynomial roots `z = 1`, two complex
   conjugate roots inside the unit disc (well-known: BDF3 is
   A(86.03°)-stable, hence zero-stable). The closed-form
   decomposition route used in cycle 346 generalises to
   `Y_n = A + B z₂^n + C z̄₂^n` (real Jordan form for the
   complex pair). Substantive but tractable single cycle.
2. **`trapezoidalLMM_isStable`** (~50 LOC) — at-boundary stability
   for `ρ(z) = z − 1`, single simple root at `z = 1` on the
   boundary. Different style from BDF2's interior-roots argument.
3. **Phase D′.2.2 Step 2 scoping** (Markdown only) — write the
   dedicated `eq422a_eta_phase_D_prime_step_2_step_2_scoping.md`
   covering the `0 ≤ Σᵢ (i+1)²·αᵄsucc` route options (`ρ''(1) ≥ 0`,
   §441 Möbius transform, etc.). Pure planning, low risk.

Recommended: **(1) BDF3 stability**, since today's BDF3 wire-up
already brought the method online and the §403 ρ-polynomial
roots argument is the natural follow-up. Pairs naturally with
the Phase B program (today's order-3 + tomorrow's stability ⇒
convergence-eligibility under §410). Compounds the §403/§451
witness surface in the same cluster.
