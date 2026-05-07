# Cycle 179 Results

## Worked on

`lem:441A` Phase B.4 — closing the `a₁ > 0` half of Butcher's
Lemma 441A (§441 p. 376).

Two new theorems in `OpenMath/Chapter4/Section441.lean`:

* `LinearMultistepMethod.aPoly_coeff_one_pos_of_stable_preconsistent`
  — generic statement: under `0 < k`, `M.IsStable`,
  `M.IsPreconsistent`, `0 < M.aPoly.coeff 1`.
* `bdf2LMM_aPoly_coeff_one_pos` — BDF2 numerical sanity:
  `0 < bdf2LMM.aPoly.coeff 1`.

## Approach

Followed the cycle 179 strategy verbatim. Phase B.4 is a one-line
corollary chain:

1. Cycle 174's bridge
   `aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent`
   (`Section441.lean:455`) reduces `0 < a₁` to `0 < 2·ρ'(1)` under
   preconsistency.
2. Cycle 178's
   `ρPoly_deriv_eval_one_pos_of_stable_preconsistent`
   (`Section441.lean:767`) supplies `0 < ρ'(1)` under stability +
   preconsistency + `0 < k`.
3. `linarith` closes `0 < 2·ρ'(1)` from `0 < ρ'(1)`.

For the BDF2 sanity, cycle 175's `bdf2LMM_aPoly_coeff_one_eq = 4/3`
(`Section441.lean:858`) reduces the goal to `0 < 4/3`, which
`norm_num` closes.

Both theorems were placed in the `OpenMath.Chapter4.Section441`
namespace just before `end OpenMath.Chapter4.Section441`, after
`bdf2LMM_ρPoly_pos_at_two`. The generic theorem is named
`LinearMultistepMethod.aPoly_coeff_one_pos_of_stable_preconsistent`
to match the dot-notation pattern used by other §441 theorems
(though the type `LinearMultistepMethod` itself lives in the
`Section404` namespace, so the full name is
`OpenMath.Chapter4.Section441.LinearMultistepMethod.aPoly_coeff_one_pos_of_stable_preconsistent`).

## Result

**SUCCESS** — both theorems compile and are axiom-clean.

* `lake env lean OpenMath/Chapter4/Section441.lean` — exit 0,
  no errors or warnings on the new code.
* `lake build OpenMath.Chapter4.Section441` — full project build
  green (`✔ [8032/8032]`), preserving the .olean cache.
* `grep -c '\bsorry\b' OpenMath/Chapter4/Section441.lean` — 0.
* Tautology-scanner regex
  (`:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$`) — no matches.
* `#print axioms` on both new theorems —
  `[propext, Classical.choice, Quot.sound]` only.

  - `OpenMath.Chapter4.Section441.LinearMultistepMethod.aPoly_coeff_one_pos_of_stable_preconsistent`
    — axiom-clean.
  - `OpenMath.Chapter4.Section441.bdf2LMM_aPoly_coeff_one_pos`
    — axiom-clean.

The proof bodies are exactly what the strategy specified — no
edits needed:

```lean
theorem LinearMultistepMethod.aPoly_coeff_one_pos_of_stable_preconsistent
    {k : ℕ} (M : LinearMultistepMethod k) (hk : 0 < k)
    (hStable : M.IsStable) (hPre : M.IsPreconsistent) :
    0 < M.aPoly.coeff 1 := by
  rw [M.aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent hPre]
  have hρ : 0 < M.ρPoly.derivative.eval 1 :=
    M.ρPoly_deriv_eval_one_pos_of_stable_preconsistent hk hStable hPre
  linarith

theorem bdf2LMM_aPoly_coeff_one_pos : 0 < bdf2LMM.aPoly.coeff 1 := by
  rw [bdf2LMM_aPoly_coeff_one_eq]
  norm_num
```

## Faithfulness check

### `LinearMultistepMethod.aPoly_coeff_one_pos_of_stable_preconsistent`

* Entity ID: `lem:441A` (intermediate result; first conjunct
  only — `aᵢ ≥ 0` for `i ≥ 2` is Phase C, deferred).
* Textbook statement (Butcher §441 p. 375, quoted from
  `extraction/formalization_data/entities/lem_441A.json`):
  > "If the method under consideration is stable then **a₁ > 0**
  > and aᵢ ≥ 0, for i = 2, 3, ..., k."
* Lean statement captures: the **first conjunct only** (`a₁ > 0`),
  with hypotheses `0 < k`, `M.IsStable`, `M.IsPreconsistent`.
* Justification for the extra `IsPreconsistent` hypothesis: the
  cycle 174 bridge `aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent`
  is conditional on preconsistency (it depends on `α(1) = 0` to
  match the textbook's
  `k − (k − 2)α₁ − ⋯ − (−k)αₖ = kα(1) − 2α'(1) = −2α'(1)` step).
  Butcher's §441 implicitly assumes consistency in the chapter
  scope; surfacing it as an explicit hypothesis is the faithful
  Lean encoding.
* Justification for the extra `0 < k` hypothesis: passed through
  to `ρPoly_deriv_eval_one_pos_of_stable_preconsistent` (cycle
  178), which needs `0 < k` to invoke `ρPoly_pos_on_Ioi_one`
  (cycle 177), which uses leading-coefficient analysis on
  `ρPoly` (degree `k`); a 0-step LMM has degenerate `ρPoly`.
  Trivially true for any LMM with at least one history step,
  the textbook's setting.
* Tautology check: conclusion `0 < M.aPoly.coeff 1` does NOT
  appear among hypotheses (which are about `IsStable`,
  `IsPreconsistent`, `0 < k`). **Pass.**
* Identity check: proof uses `rw` + `linarith` — genuine work
  via cycle 174 bridge + cycle 178 positivity. Not an `exact h`.
  **Pass.**
* Hypothesis strength: `IsStable` is the textbook's named
  hypothesis, `IsPreconsistent` is implicit in §441's chapter
  scope, `0 < k` is trivially true for any LMM. None can be
  weakened without restructuring upstream lemmas. **Pass.**

### `bdf2LMM_aPoly_coeff_one_pos`

Lean-internal numerical sanity witness on the canonical `k = 2`
example. Not a textbook entity — confirms the cycle 174 bridge
`a₁ = 2·ρ'(1)` numerically via the chain `4/3 = 2·(2/3)` (cycle
175 + cycle 176). No faithfulness question.

## Dead ends

None — both theorems closed on the first try, exactly as the
strategy predicted (a one-`rw` + `linarith` for Priority 1, a
one-`rw` + `norm_num` for Priority 2).

## Discovery

The `lean_verify` MCP tool errored on
`OpenMath.Chapter4.Section441.LinearMultistepMethod.aPoly_coeff_one_pos_of_stable_preconsistent`
with `%d format: a real number is required, not NoneType` — but
the same theorem name worked with `#print axioms` directly (via
`lake env lean` on a one-shot file). The bug is in the MCP
wrapper, not in Lean. For axiom-checking long fully qualified
names through nested namespaces, the
`lake env lean` + `#print axioms` route is more reliable than
the MCP `lean_verify` tool. Worth noting for future cycles
that need to verify deeply namespaced theorems.

(`bdf2LMM_aPoly_coeff_one_pos`, the shorter name, verified
fine through `lean_verify`.)

## Suggested next approach

Phase B is now fully closed for `lem:441A`. The natural next
target is **Phase C**: `aᵢ ≥ 0` for `i = 2, …, k`. Per the
strategy's §7 stretch-goal scoping (and the existing analysis in
`.prover-state/issues/lem_441A_alpha_prime_negative.md`), Phase C
is multi-cycle infrastructure:

1. **Phase C.1** — bridge `M.IsStable` to a complex-root
   property of `aPoly`: every complex root `ζ` of `aPoly`
   satisfies `Re(ζ) ≤ 0`. The textbook argument routes through
   the Möbius transformation `ζ ↦ (1−ζ)/(1+ζ)` mapping roots of
   `aPoly` to roots of `α` in the closed unit disk (the
   stability assumption). Mathlib hooks: `Polynomial.roots`
   over `ℂ`, `Polynomial.IsRoot`, complex Möbius transformations.
2. **Phase C.2** — quadratic-factor non-negativity: each real
   linear factor `z − ξ` of `aPoly` has `−ξ ≥ 0` (since
   `ξ ≤ 0`); each conjugate-pair quadratic factor
   `z² − 2(Re ζ)z + |ζ|²` has `−2(Re ζ) ≥ 0` and `|ζ|² ≥ 0`
   coefficients.
3. **Phase C.3** — sum-of-products: a polynomial whose factors
   all have non-negative coefficients itself has non-negative
   coefficients (by induction on the number of factors).

The complex-root decomposition argument is novel infrastructure
in this codebase (no prior cycle has worked over `ℂ` extensively
for §441); the planner should consider whether to scope Phase C
as a fresh §441 strategy doc or to break it into ~3 sub-cycles
matching C.1/C.2/C.3. Either way, the BDF2 sanity witness will
need to extend beyond `aPoly.coeff 1` to all of `aPoly.coeff 0`,
`aPoly.coeff 1`, `aPoly.coeff 2` (and confirm each is ≥ 0).

A separate orthogonal direction is to ship `bdf2LMM.IsStable` —
currently the BDF2 numerical witnesses route around this
hypothesis (e.g. `bdf2LMM_ρPoly_pos_at_two` does not invoke
`ρPoly_pos_on_Ioi_one`). Proving stability for BDF2 would let
the BDF2 sanity witnesses route through the generic theorems
end-to-end, providing a stronger non-vacuity check.
