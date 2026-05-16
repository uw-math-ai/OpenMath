# Cycle 316 Results

## Worked on

`thm:342C` clause (342n) — `B(2s) ∧ E(s, s) ⇒ C(s)` — shipped as
`OpenMath.Chapter3.Section312.RKTableau.satisfiesC_of_satisfiesB_satisfiesE`
in `OpenMath/Chapter3/Section321.lean`. This is the matching
Vandermonde-converse partner of cycle 315's (342p)
`satisfiesD_of_satisfiesB_satisfiesE`.

## Approach

Direct port of cycle 315's Vandermonde-inversion recipe with three
changes:

1. **Residual structure is "per-row" instead of "per-column".**
   `C(s)` is indexed by stage `i` (target row), so the C-residual
   `u i' := (∑ⱼ Aᵢ'ⱼ cⱼ^(k-1)) − cᵢ'^k / k` lives on the row index
   `i'`. Define the weighted residual `w i' := M.b i' * u i'` so that
   `Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hc` (with
   `hc : Function.Injective M.c`) yields `w = 0`.
2. **Variable swap inside `E(s, s)`.** In `h_first`, we need the
   matrix sum `∑ᵢ' bᵢ' cᵢ'^(l-1) Aᵢ'ⱼ cⱼ^(k-1)`, so apply
   `hE l hl1 hl_le_s k hk1 hk` (swapping the lemma's two pairs of
   exponent args from cycle 315's `hE k hk1 hk l hl1 hl_le_s`). The
   output `1/(k·(l+k))` matches the (342n) target `1/(k·(k+l))` up to
   `add_comm` on the denominator; trailing `ring` closes.
3. **Final extraction needs `hb`.** After `congrFun hw_zero i` gives
   `w i = M.b i * u i = 0`, `rcases mul_eq_zero.mp hwi with hbi | hui`
   plus `hb i : M.b i ≠ 0` gives `u i = 0`, then `linarith` rearranges
   to the `C(s)` form `∑ⱼ Aᵢⱼ cⱼ^(k-1) = cᵢ^k / k`.

The `h_first` reshape required a slight refinement from the strategy
sketch: the residual has shape `(b · (∑ A · c^(k-1))) · c^(l-1)`, not
`(∑ b · A · c^(k-1)) · c^(l-1)`, so `Finset.sum_mul` doesn't fire
directly. Instead, first re-bracket to
`b · c^(l-1) · (∑ A · c^(k-1))` via `ring`, then `Finset.mul_sum`,
then ring inside.

Non-vacuity ships as a `gaussLegendre1Stage.SatisfiesC 1` example
through the abstract bridge, mirroring cycle 315's (342p) abstract-
route example. `hc` is vacuous at `s = 1`; `hb` reduces to
`simp [gaussLegendre1Stage]` (since `b 0 = 1`); `hB`/`hE` reuse the
existing hand-built witnesses' tactic blocks.

## Result

**SUCCESS** — `lake env lean OpenMath/Chapter3/Section321.lean`
returns exit 0, no errors. `lake build OpenMath.Chapter3.Section321`
completes successfully. Axiom profile:
`'OpenMath.Chapter3.Section312.RKTableau.satisfiesC_of_satisfiesB_satisfiesE'
depends on axioms: [propext, Classical.choice, Quot.sound]` — matches
cycles 313/314/315 exactly. No `sorry`, no `axiom`.

## Faithfulness check

- **Entity ID and textbook statement** (quoted from
  `extraction/formalization_data/entities/thm_342C.json`):
  > `B(2s) ∧ E(s, s) ⇒ C(s)` (342n)
- **Lean statement captures**: **same content**, plus two extra
  explicit hypotheses surfacing Butcher's implicit "non-singular
  matrix multiplier" assumption:
  - `hc : Function.Injective M.c` — distinct abscissae (Vandermonde
    core, same as cycle 315 for (342p)).
  - `hb : ∀ i : Fin s, M.b i ≠ 0` — non-vanishing weights (diagonal
    multiplier non-singularity, specific to the C(s) converse).
- **Justification for divergence**: Butcher's proof says "because the
  matrix multiplier is non-singular, (342n) also follows". The
  multiplier is `(bᵢ · cⱼ^{l-1})_{l, j}` (a Vandermonde scaled by `b`
  on the diagonal), which is non-singular iff both `c` is injective
  and every `bᵢ` is non-zero. We surface both. The canonical
  Gauss–Legendre tableau satisfies both via cycle 302's
  `butcherShiftedLegendre_zeros_strictMono` (injectivity) and cycle
  305's `butcherShiftedLegendre_quadratureWeights_pos`
  (positivity ⇒ non-vanishing).
- **Tautology check** ✓: conclusion `M.SatisfiesC s` is not a
  hypothesis.
- **Identity check** ✓: proof is substantive (~140 LOC) — Vandermonde
  inversion via `Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero`,
  two named sub-sums (`h_first`/`h_second`), `mul_eq_zero` +
  `linarith` extraction.
- **Definition smuggling** ✓: no new defs/structures.
- **Hypothesis strength** ✓: all four hypotheses minimal and
  documented. `B(2s)` applied at `k+l ∈ [2, 2s]`. `E(s, s)` applied
  at all `(l, k) ∈ [1, s]²`. `hc` and `hb` jointly required for the
  matrix multiplier's non-singularity. None can be weakened.
- **Absent theorem check** N/A.

For the non-vacuity `example : gaussLegendre1Stage.SatisfiesC 1` via
the abstract bridge: standard pattern, mirrors the existing
hand-built `SatisfiesC 1` example. No new content beyond exercising
the new bridge.

## Dead ends

- Initial naive `rw [Finset.sum_mul]` in `h_first` failed:
  `Finset.sum_mul` expects the LHS shape `(∑ f) * a`, but our shape
  is `(b · (∑ A · c^(k-1))) · c^(l-1)`. Resolved by inserting an
  explicit `ring`-based re-bracketing
  `b · (∑ A · c^(k-1)) · c^(l-1) = b · c^(l-1) · (∑ A · c^(k-1))`
  before applying `Finset.mul_sum`. This is the difference from
  cycle 315 where the D-residual already had the outer factor on
  the left.

## Discovery

- The "purely algebraic" §342C clause set (m/n/o/p) decomposes into
  two pairs of symmetric proofs. The forward direction (m/o) is a
  one-step algebraic composition; the converse direction (n/p) is a
  Vandermonde inversion. The converse direction additionally needs
  a non-singularity hypothesis on the Vandermonde-style matrix
  multiplier — for (342p) this is purely `Function.Injective M.c`
  (the multiplier is `(cⱼ^{l-1})_{l,j}`), while for (342n) it is
  the conjunction `Function.Injective M.c ∧ ∀ i, M.b i ≠ 0` (the
  multiplier is the `b`-diagonal-scaled Vandermonde
  `(bᵢ · cᵢ^{l-1})_{l,i}`). Future C(s)-side converse-style proofs
  in §342–§344 should expect both hypotheses.
- The reshape recipe in `h_first` (re-bracket via `ring` to put the
  inner `(∑ A · c^(k-1))` rightmost, then `Finset.mul_sum`, then
  ring inside) is a useful general pattern for converting between
  shapes when `Finset.sum_mul` doesn't fire directly. Worth keeping
  in mind for future C(s)-style residuals.

## Suggested next approach

With (342m/n/o/p) all formalised, the §342C "purely algebraic" core
is complete. Next single-cycle targets in order of leverage:

1. **`thm:344A` Radau and Lobatto methods** (§344). Concrete tableau
   constructions analogous to cycle 308's `butcherGaussLegendreRK`.
   Likely 2–3 cycles for the Radau IA/IIA and Lobatto IIIA/IIIB/IIIC
   families. Independent of `thm:314A`. **Recommended next.**
2. **`lem:359A` V and W transformations** (§359). Single named
   transformation lemmas; downstream §357/§358 unlock.
3. **`lem:351A` / `thm:351B` A-stability criteria** (§351). Verify
   Mathlib's `Polynomial.IsRoot` plumbing first.
4. **Phase A.3/B of `lem:310B`** per
   `.prover-state/issues/lem_310B_plan.md` — opens the `thm:314A`
   elementary-differential infrastructure that would unlock the
   (342j/k/l) G(2s) clauses.

The cycle 317 planner should re-check `lem_310B_plan.md` for any
intervening Phase A.3 / Phase B progress before picking a path.
