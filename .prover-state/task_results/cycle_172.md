# Cycle 172 Results

## Worked on
- **Priority 0** — Rolled back cycle 171's incorrect
  `LinearMultistepMethod.aPoly_even_coeff_neg` (the sorry'd theorem
  that claimed to formalise `lem:441B` but was actually mathematically
  wrong — see `.prover-state/issues/lem_441B_misinterpretation.md`).
- **Priority 1 (DEFERRED)** — Attempted `bdf2LMM_aPoly_eq` (k=2 BDF2
  closed form `aPoly = C(4/3) X + C(8/3) X²`). The algebra is
  straightforward but `ring` does not fold `Polynomial.C` constants
  (`C(4/3) - C(-1/3) = C(5/3)` is outside `ring`'s normal form).
  Per strategy time-box guidance ("If it does not close, drop
  Priority 1 and proceed to Priority 2"), the witness was dropped
  for cycle 172. The algebraic refutation of cycle 171 still
  appears in the issue file (just not in Lean).
- **Priority 2** — Added `LinearMultistepMethod.aPoly_natDegree_le`
  (degree bound `aPoly.natDegree ≤ k`).
- **Priority 3** — Reverted `lem:441B` row in
  `extraction/formalization_data/lean_status.json` from `partial`
  back to `unformalized`; reverted `plan.md`'s `[~]` mark to `[ ]`
  with footnote pointing to the issue file.
- **Priority 4** — Wrote `.prover-state/issues/lem_441B_misinterpretation.md`
  documenting the conflation, the BDF2 algebraic refutation, and
  the corrected multi-cycle plan for `lem:441B`.
- **Priority 5 (STRETCH)** — Skipped per strategy guard ("sorry
  count must NOT regress to 1"; `lem:441A` requires non-trivial
  derivative-of-α work that doesn't fit cleanly in the remaining
  budget).

## Approach

### Rollback (Priority 0)
The cycle 171 theorem `aPoly_even_coeff_neg` was deleted from
`OpenMath/Chapter4/Section441.lean`. The file header docstring
was rewritten to (a) explicitly distinguish the two §441
sequences (`a_i` vs universal `c_{2i}`), (b) describe Phase A
scope as the `aPoly` def + witnesses + degree bound, (c) point
to the new issue file in a "Lemma 441B — DEFERRED" subsection.

### BDF2 witness (Priority 1) — DEFERRED
The intended `bdf2LMM_aPoly_eq` proves
`bdf2LMM.aPoly = C(4/3) X + C(8/3) X²`. Approaches tried:
1. `unfold; rw [Fin.sum_univ_two]; simp [bdf2LMM, ...]; ring` —
   `simp` deterministic timeout (200000 heartbeats) at
   `isDefEq` (likely chasing the `match`-on-`Fin` reduction).
2. `unfold; rw [Fin.sum_univ_two]; show <concrete>; rw [αrfls];
   ring` — `ring` cannot fold `Polynomial.C` constants, leaving
   `(-C(4/3) - C(-1/3)) + 1 = 0` as an unsolved residue.
   Confirmed by an isolated stand-alone test
   (`Polynomial.C (4/3) * X + Polynomial.C (8/3) * X^2 = ...`
   with the same `ring` error).
3. `push_cast` does nothing on `Polynomial.C` constants.

The algebra is correct (see issue file's BDF2 refutation), but
the Lean closure requires either coefficient-by-coefficient
extensionality (`Polynomial.ext` + `Polynomial.coeff_*`) or a
`linear_combination` setup combining `C` constants explicitly.
Both paths are doable in a future cycle; for cycle 172, the
strategy's explicit time-box ("drop Priority 1 if it does not
close") was applied and the witness was removed.

The BDF2 refutation of cycle 171 is preserved in the issue file
as a hand-computation, with explicit polynomial expansion.

### Degree bound (Priority 2)
`aPoly_natDegree_le` proves `aPoly.natDegree ≤ k`. The proof
follows the Section410 `αPoly_natDegree_le` recipe:
* `natDegree_sub_le` → bound `(1+X)^k` and the sum separately.
* `(1+X)^k`: `natDegree_pow_le` plus `(1+X).natDegree ≤ 1`
  (via `natDegree_add_le` on `1` and `X`).
* Sum: `natDegree_sum_le` + `Finset.sup_le`. Each summand
  decomposes via `natDegree_mul_le` into:
  - `(C(α i.succ) * (1+X)^(k-(i+1))).natDegree ≤ k-(i+1)`
    (via `natDegree_C_mul_le` + `natDegree_pow_le`).
  - `((1-X)^(i+1)).natDegree ≤ i+1`.
  Summing: `(k-(i+1)) + (i+1) = k` via `Nat.sub_add_cancel`
  using `i.isLt : i.val + 1 ≤ k`.

The proof is fully explicit (no `omega`, no `norm_num` finisher);
it ports the Section410 pattern with the additional product
structure of the summand.

### lem_441B_misinterpretation.md
The issue file documents:
- Algebraic verification that BDF2's `aPoly` has positive even
  coefficients despite BDF2 being stable (refutes cycle 171).
- The correct interpretation: `lem:441B`'s `c_{2i}` are universal
  constants of `(1/z)·log((1+z)/(1−z))`'s inverse series, with no
  `M` dependency.
- The correct multi-cycle plan: define `cInverseLog : ℕ → ℝ`,
  prove the (441c) inverse-series identity in `PowerSeries ℝ`,
  base cases `c₀ = 1/2`, `c₂ = -1/6`, induction via (441d).
- Pointer to `lem:441A` as the *correct* §441 negativity-style
  lemma about `aPoly` coefficients (deferred to a future cycle).

## Result

SUCCESS — Sorry count `1 → 0`. One new axiom-clean theorem
(`aPoly_natDegree_le`). One incorrect theorem removed. Issue
file documents the misinterpretation and re-plan. Priority 1
(`bdf2LMM_aPoly_eq`) deferred per strategy time-box; the
algebraic refutation of cycle 171 is preserved in the issue
file (hand-computation).

## Faithfulness check

For each new entity introduced this cycle:

### `LinearMultistepMethod.aPoly_natDegree_le` (helper, no entity ID)
- This is a generic structural lemma about `aPoly`'s degree;
  not a textbook entity. Faithful: `(1+X)^k` and each summand
  `αᵢ(1+X)^{k-i}(1-X)^i` have textbook degree `≤ k` since
  `1 ≤ i ≤ k`. The Lean bound matches.

### `bdf2LMM_aPoly_eq` (helper, deferred — NOT in this cycle)
- The intended witness was textbook-faithful (BDF2's `aPoly =
  C(4/3) X + C(8/3) X²` is direct-algebra). Deferred only for
  proof-engineering reasons (`ring` does not fold
  `Polynomial.C` arithmetic); no faithfulness concern.

### Rollback — `aPoly_even_coeff_neg` (was lem:441B claim)
- Cycle 171's claim: even coefficients of `aPoly` are negative
  for stable `M`.
- Textbook (`lem:441B` per `entities/lem_441B.json`): "The
  coefficients c₂, c₄, … are all negative" — referring to the
  universal `c_{2i}` of the inverse series, NOT `aPoly`.
- Lean statement captured: **different — and wrong**. Removed.
  The textbook-correct `lem:441B` requires a separate
  `cInverseLog : ℕ → ℝ` definition (see issue file). Cycle 172
  does not introduce `lem:441B`'s formalisation.

## Dead ends

- Initial draft of `bdf2LMM_aPoly_eq` used `simp [bdf2LMM,
  Fin.sum_univ_two]; ring` per the strategy's recipe. Adjusted
  to explicitly extract `bdf2LMM.α (Fin.succ 0) = 4/3` and
  `bdf2LMM.α (Fin.succ 1) = -1/3` as `rfl` lemmas before the
  general simp set, since `simp` does not always unfold the
  Fin-pattern-match through `Fin.succ` reliably.

## Discovery

Cycle 171's `aPoly_even_coeff_neg` is the second instance of a
pattern worth flagging to the planner: **a textbook lemma in §X
references coefficients `c_i` that look syntactically like the
expansion of an `aPoly`-style polynomial in the same section, but
are actually constants of a separate (universal) power series**.
The cycle 171 worker correctly extracted Butcher's polynomial
`a(z)` (cycle 171 `aPoly` def is sound) but conflated `a(z)`'s
output coefficients with the universal `c_{2i}` Butcher introduces
later in the same proof.

Mitigation for future cycles: when a §X lemma claim has the form
"coefficients `c_i` of <polynomial expression> are <sign>", grep
the raw text for *all* occurrences of `c_2`, `c_0`, `c_i` near
that claim — Butcher often defines a second sequence (universal
constants) within the proof of a lemma about the first sequence,
without fanfare.

## Suggested next approach

Cycle 173 should choose between:

1. **`lem:441A`** (the *correct* §441 negativity lemma about
   `aPoly` coefficients). Strategy §C Priority 5 outlines the
   proof. The `a₁ > 0` half hinges on `α'(1) > 0` (positive
   derivative at the simple root z=1 of α(z) for stable `M`).
   The `aᵢ ≥ 0` half requires factoring `aPoly` over the
   left-half-plane; this is heavier and may need its own cycle.
   Splitting into `aPoly_coeff_one_pos` (closed) + a deferred
   `aPoly_coeff_ge_zero_of_stable` is the recommended decomposition.

2. **`lem:441B` Phase B** (universal `c_{2i}` infrastructure).
   Define `cInverseLog : ℕ → ℝ` via the (441c) inverse-series
   identity. This is a stand-alone `PowerSeries ℝ` problem —
   suitable for one cycle if Mathlib's `PowerSeries.inv` and
   `PowerSeries.mul_inv_cancel` cover the algebraic skeleton.

3. Pivot to a §44 entity not blocked by `lem:441A/B`
   (`thm:441C` Dahlquist barrier needs both lemmas; deferring is
   correct). Candidates: `def:442A` "principal sheet" (§442) is
   independent; `thm:443A` "order arrows" or `thm:443B` "A
   stability error constant upper bound" lean on §443
   infrastructure not yet built.

The recommended pick is **(1)**, since cycle 172 left a clean
`aPoly`-centric file ready for the lem:441A proof, the textbook
proof is short, and the `a₁ > 0` half is ~60 lines based on the
strategy outline.
