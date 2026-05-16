# Cycle 324 Results

## Worked on
§344 Phase D.4 — Radau IIA `s = 2` `RKTableau` (Butcher Table 344(II) p. 245).
Ship the two-stage Radau IIA collocation A-matrix + `RKTableau`,
direct form, coincidence theorem, and a `SatisfiesB` non-vacuity
example. Direct port of cycle 322's Radau IIA `s = 1` and cycle 323's
Lobatto IIIA `s = 2` ladder, but with the first substantive
`[0, 1/3]` integration in the §344 stack.

## Approach
1. **Define `butcherRadauII_collocationA_two : Fin 2 → Fin 2 → ℝ`**
   as `∫₀^{c_i} L_j(x) dx` over `butcherRadauII_zeros_two = (1/3, 1)`
   and `Lagrange.basis Finset.univ butcherRadauII_zeros_two j`.
2. **Prove four `_apply` theorems** using the cycle 321 / 323 recipe:
   - For the `(1, j)` entries (`c_1 = 1`): direct cycle 321 mirror —
     same Lagrange-basis polynomial expansion as
     `butcherRadauII_quadratureWeights_two_apply_*`, just prepended
     by an explicit `show ∫ x in (0 : ℝ)..butcherRadauII_zeros_two ⟨1, _⟩,
     … = …` reframing and an `h_c1 := rfl` bridge to swap the
     pattern-matched abscissa to `1`. Same final
     `∫₀¹ ((3/2) − (3/2)x) dx = 3/4` and `∫₀¹ ((3/2)x − 1/2) dx = 1/4`
     integration chains.
   - For the `(0, j)` entries (`c_0 = 1/3`): substantive new
     `[0, 1/3]` integration. Recipe was the cycle 321 chain with two
     key swaps — `(b := 1/3)` in `integral_pow`, and
     `continuous_id.intervalIntegrable 0 (1/3)` for the `x`
     integrability witness. The resulting `hx : ∫₀^{1/3} x = 1/18`
     plug-in closes both arms by `norm_num`.
3. **Assemble `butcherRadauIIA_two : RKTableau 2`** from cycle 320's
   `_zeros_two`, cycle 321's `_quadratureWeights_two`, and this
   cycle's `_collocationA_two`.
4. **Ship `butcherRadauIIADirect_two`** as the direct form
   `c = (1/3, 1)`, `b = (3/4, 1/4)`, `A = !![5/12, -1/12; 3/4, 1/4]`
   and `butcherRadauIIA_two_eq_direct` via `RKTableau.mk.injEq` +
   four `_apply` rewrites + two `_quadratureWeights` rewrites + four
   `rfl` reductions.
5. **Non-vacuity stretch — `SatisfiesB 3`**: Radau IIA `s = 2` has
   classical order `2s − 1 = 3`. Tried `B(3)` first per the
   strategy's stretch directive; closed cleanly in one
   `simp [butcherRadauIIADirect_two, Fin.sum_univ_two]; norm_num` per
   arm (`k = 1, 2, 3`). Upgraded from the default `B(2)` to `B(3)`.

## Result
SUCCESS — all 8 new public symbols compile axiom-clean
(`[propext, Classical.choice, Quot.sound]`). `lake env lean
OpenMath/Chapter3/Section344.lean` exits 0; `lake build
OpenMath.Chapter3` completes 2939/2939 jobs. Section344.lean grew
from 1397 → 1631 LOC (~234 added). `SatisfiesB 3` stretch ships
instead of the default `B(2)` — saves a cycle on the natural
follow-up of "verify Radau IIA s=2 actually hits its classical
order."

## Faithfulness check
For each new `def` / `theorem`:

- **`butcherRadauII_collocationA_two`** (def): Butcher §344 p. 245,
  Table 344(II) collocation A-matrix.
  > "Radau IIA: Radau II quadrature, [collocation A] = the
  > reflections of Radau I" — at `s = 2` this evaluates to the
  > Table 344(II) tableau `A_{ij} = ∫₀^{c_i} L_j(x) dx` over the
  > Radau II abscissae `(1/3, 1)`.
  Lean def: `∫ x in (0 : ℝ)..butcherRadauII_zeros_two i,
  (Lagrange.basis Finset.univ butcherRadauII_zeros_two j).eval x`.
  Captures: **same content**. The collocation recipe is literally
  the textbook definition.

- **`butcherRadauII_collocationA_two_apply_zero_zero = 5 / 12`**:
  Butcher Table 344(II) p. 245 entry `A_{11}`.
  Lean statement: `... ⟨0, _⟩ ⟨0, _⟩ = 5 / 12`. Paper-verified
  arithmetic: `∫₀^{1/3} ((3/2) − (3/2)x) dx = (3/2)(1/3) − (3/4)(1/9)
  = 1/2 − 1/12 = 5/12`. **Same content**.

- **`butcherRadauII_collocationA_two_apply_zero_one = -(1 / 12)`**:
  Butcher Table 344(II) p. 245 entry `A_{12}`.
  Lean: `... ⟨0, _⟩ ⟨1, _⟩ = -(1/12)`. Paper: `∫₀^{1/3}
  ((3/2)x − 1/2) dx = (3/4)(1/9) − (1/2)(1/3) = 1/12 − 1/6 = −1/12`.
  **Same content** (sign-bearing reformulation `-(1/12)` matches the
  textbook negative-twelfth value).

- **`butcherRadauII_collocationA_two_apply_one_zero = 3 / 4`**:
  Butcher Table 344(II) p. 245 entry `A_{21}`.
  Lean: `... ⟨1, _⟩ ⟨0, _⟩ = 3 / 4`. Same as cycle 321's
  `butcherRadauII_quadratureWeights_two_apply_zero` integral (the
  `c_1 = 1` upper limit recovers the `[0, 1]` quadrature weight).
  **Same content**.

- **`butcherRadauII_collocationA_two_apply_one_one = 1 / 4`**:
  Butcher Table 344(II) p. 245 entry `A_{22}`.
  Lean: `... ⟨1, _⟩ ⟨1, _⟩ = 1 / 4`. Same as cycle 321's
  `butcherRadauII_quadratureWeights_two_apply_one`. **Same content**.

- **`butcherRadauIIA_two`** (def): Butcher §344 Table 344(II) p. 245
  Radau IIA at `s = 2`.
  Lean: `RKTableau 2` with `A := butcherRadauII_collocationA_two`,
  `b := butcherRadauII_quadratureWeights_two`,
  `c := butcherRadauII_zeros_two`. **Same content** (collocation
  assembly from the canonical Lagrange weights, zeros, and A-matrix).
  No definition smuggling — `RKTableau.mk` is the structural
  packaging, not a derived claim.

- **`butcherRadauIIADirect_two`** (def): direct-form mirror with
  inline matrix literal `!![5/12, -(1/12); 3/4, 1/4]` and vectors
  `![3/4, 1/4]`, `![1/3, 1]`. **Same content** — concrete witness
  for cross-validation.

- **`butcherRadauIIA_two_eq_direct`** (coincidence theorem):
  collocation form equals direct form. Routes through
  `RKTableau.mk.injEq` + four `_apply` rewrites + two
  `_quadratureWeights_two_apply_*` rewrites + four `rfl` reductions.
  Tautology check: conclusion is structure equality across two
  distinct definitions, not a hypothesis re-export. Identity check:
  proof routes through 10 substantive rewrites, not `exact h`.

- **`SatisfiesB 3` non-vacuity** (example, anonymous): Radau IIA
  `s = 2` is exact for polynomials of degree ≤ `2s − 1 = 3`. The
  example verifies the three quadrature-condition arms
  (`∑ⱼ bⱼ · cⱼ^{k−1} = 1/k` for `k ∈ {1, 2, 3}`):
  - `k = 1`: `3/4 + 1/4 = 1`
  - `k = 2`: `(3/4)·(1/3) + (1/4)·1 = 1/4 + 1/4 = 1/2`
  - `k = 3`: `(3/4)·(1/9) + (1/4)·1 = 1/12 + 3/12 = 1/3`
  All paper-verified. The example is anonymous (no theorem name) so
  there's no tautology / identity / smuggling risk.

No divergences from the textbook. No new hypotheses introduced
beyond what cycle 322 / 323's analogous tableaux required (none —
these are unconditional concrete `RKTableau` witnesses).

## Dead ends
None this cycle. The strategy's recipe was verbatim what worked: the
`(1, j)` entries lifted cycle 321 with a one-line `show` reframing
and an `h_c1 := rfl` bridge, and the `(0, j)` entries swapped
cycle 321's `(b := 1)` `integral_pow` argument to `(b := 1/3)`
without further adjustment. The `(0, 1) = -(1/12)` sign was
handled by stating the goal as `-(1 / 12)` and letting `norm_num`
collapse to the textbook value — no `neg_div` / `neg_eq_neg_one_mul`
intervention needed.

The `SatisfiesB 3` stretch was tried first per the strategy's
directive (rather than the safer `B(2)` default); the
`simp + norm_num` per arm closed all three cases on the first
attempt, so the stretch shipped as the default example.

## Discovery
- **`integral_pow` works fine over fractional upper limits without
  any extra setup.** Cycle 321/322/323 only ever used `(b := 1)`;
  cycle 324 now confirms `(b := 1/3)` produces the standard
  `(1/3)^2 / 2 = 1/18` arithmetic without needing `pow_two` /
  `mul_self` rewriting. This unlocks future `[0, c_i]` integration
  steps for any rational `c_i`.
- **`continuous_id.intervalIntegrable 0 (1/3)` produces the right
  witness shape directly.** No need to unfold or restate; the
  `MeasureTheory.volume` parameter is inferred and the resulting
  `IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume 0 (1/3)`
  feeds `.const_mul (3/2)` cleanly.
- **`SatisfiesB k` arms close uniformly under `simp [direct_form,
  Fin.sum_univ_two]; norm_num` for the two-stage direct-matrix-form
  Radau IIA**, regardless of `k`. This means future
  classical-order-equals-`2s − 1` checks at `s = 2` are essentially
  free if the underlying `_eq_direct` coincidence theorem is in
  place.
- **The `B(3)` stretch was cheaper than the strategy estimated.**
  Strategy budgeted "drop back to B(2) if norm_num doesn't close in
  ~30 seconds"; in practice the three-arm `B(3)` proof was indistinguishable
  in cost from the two-arm `B(2)` proof. Future Radau / Lobatto
  cycles should default to the maximal `B(k)` their classical order
  supports.

## Suggested next approach
Cycle 325 candidates, in increasing scope:

1. **Radau IA `s = 1` (forward Euler analogue)** — easiest. Single
   entry, `c = (0)`, so the A-matrix integral is vacuous via
   `intervalIntegral.integral_same` (cycle 323 `(0, *)` template).
   Adds `butcherRadauI_collocationA_one` + 1 `_apply` + 1 RKTableau
   + 1 direct form + 1 coincidence + `SatisfiesB 1`. ~80 LOC.
   Mirrors cycle 322 with a swap of `RadauII → RadauI` and a swap of
   `(1)` for `(0)` in the upper limit.
2. **Radau IA `s = 2`** — `c = (0, 2/3)`, b = `(1/4, 3/4)`. The
   `(0, *)` entries vacuous, the `(1, *)` entries need `[0, 2/3]`
   integration (new fractional upper limit beyond `1/3`, but
   `integral_pow` confirmed in this cycle to work for any rational).
   ~150 LOC; doable in one cycle.
3. **Lobatto IIIA `s = 3` (Simpson's rule)** — 9-entry A-matrix.
   Multi-cycle scope per cycle 323's task results; the `(2, *)`
   integrals need `[0, 1]` Lagrange-basis-quadratic integration that
   the cycle 321 `s = 3` weight machinery already exercises, but the
   `(1, *)` integrals need fresh `[0, 1/2]` integration on three
   quadratic basis polynomials.

If the planner wants to close out the four-strong "small-`s`
RKTableau" family quickly, cycle 325 = Radau IA `s = 1` is the
right pick. If the planner wants to start a substantive
multi-cycle arc, cycle 325 = Lobatto IIIB `s = 2` (the Radau II /
Lobatto IIIA reflection partner) is a sensible counterpart.

Independent of family-completion, **Phase B.2 (polynomial exactness
`2s − 2` / `2s − 3` via polynomial division)** remains the
headline `thm:344A` deliverable. Phase D ladder is non-vacuity
infrastructure; the iff core requires the orthogonality →
exactness chain that cycle 318 set up but cycle 319+ has not yet
exercised. That's the multi-cycle target after the small-`s`
RKTableau family closes.
