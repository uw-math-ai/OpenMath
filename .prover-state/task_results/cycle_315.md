# Cycle 315 Results

## Worked on

`thm:342C` clause **(342p)** — `B(2s) ∧ E(s, s) ⇒ D(s)` — formalised
as `satisfiesD_of_satisfiesB_satisfiesE` in
`OpenMath/Chapter3/Section321.lean`. This is the first
Vandermonde-converse clause of the §342C seven-way equivalence.

## Approach

Followed the Cycle 315 strategy verbatim:

1. Added `import Mathlib.LinearAlgebra.Vandermonde` to
   `Section321.lean` (not transitively imported by the existing
   `Section312` chain).
2. Stated the theorem with the side hypothesis
   `hc : Function.Injective M.c` to surface Butcher's implicit
   "matrix multiplier is non-singular" assumption explicitly.
3. Defined the residual vector `v : Fin s → ℝ` at exponent `k` as
   `v j' = (∑ᵢ bᵢ cᵢ^(k-1) Aᵢⱼ') − (bⱼ'/k)(1 − cⱼ'^k)`. `D(s)`
   at `(j, k)` is exactly `v j = 0`.
4. Showed `v = 0` (as a function) via
   `Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero` applied with
   `f = M.c` and `hc` for injectivity. The Vandermonde hypothesis
   reduces to: for every `i : Fin s`, `∑ j', v j' · cⱼ'^i = 0`.
5. Reparameterised `(i : ℕ)` as `l - 1` with `l = i.val + 1`,
   giving `1 ≤ l ≤ s`. Split the goal sum into two halves:
   * `h_first`: pull `cⱼ'^(l-1)` inside the inner `i'`-sum,
     `Finset.sum_comm` to swap, then directly apply `hE k hk1 hk l
     hl1 hl_le_s` to get `1 / (l (k + l))`.
   * `h_second`: per-`j'` rewrite via the power identity
     `cⱼ'^k · cⱼ'^(l-1) = cⱼ'^((k+l)-1)` (Nat-subtraction handled
     by `omega`), distribute `(1/k)`, split, apply `B(2s)` at `l`
     and `k + l`, close with `push_cast; field_simp; ring`.
6. `calc` chain: the difference of the two sums is
   `1/(l(k+l)) - 1/(l(k+l)) = 0`.
7. Extracted `v j = 0` via `congrFun`, then `simp only [v_def]` +
   `linarith` to rearrange to the textbook D(s) form.
8. Added the abstract-route non-vacuity example
   `gaussLegendre1Stage.SatisfiesD 1`, which discharges injectivity
   vacuously at `s = 1` via `fin_cases i; fin_cases j; rfl`.

## Result

**SUCCESS** — `lake build OpenMath.Chapter3` exits 0.
`grep -c sorry OpenMath/Chapter3/Section321.lean` returns 0.
`#print axioms
OpenMath.Chapter3.Section312.RKTableau.satisfiesD_of_satisfiesB_satisfiesE`
returns `[propext, Classical.choice, Quot.sound]` — axiom-clean,
matching the cycle 313/314 siblings exactly.

Total new content: ~146 LOC for the theorem (including ~50 lines
of docstring), ~26 LOC for the non-vacuity example. Well within
the strategy's 130–160 LOC estimate.

## Faithfulness check

`satisfiesD_of_satisfiesB_satisfiesE`:

* Entity ID: `thm:342C`, clause (342p), Butcher §342, p. 238.
* Textbook statement (quoted from
  `extraction/formalization_data/entities/thm_342C.json`):
  > `B(2s) \land E(s, s) \Rightarrow D(s)` (342p)
* Lean statement captures: **same content**, **plus** the extra
  explicit hypothesis `Function.Injective M.c` (distinct abscissae).
* Justification for divergence: Butcher's textbook proof says "the
  matrix multiplier is non-singular", which is implicitly assuming
  distinct abscissae (the Vandermonde matrix `(cⱼ^(l-1))_{l,j}` is
  invertible iff the `cⱼ` are distinct). We surface this as an
  explicit `Function.Injective M.c` hypothesis rather than leaving
  it implicit. The canonical Gauss-Legendre tableau satisfies
  injectivity automatically via cycle 302's
  `butcherShiftedLegendre_zeros_strictMono` +
  `StrictMono.injective`, so downstream consumers are unaffected.
  The 1-stage `gaussLegendre1Stage` consumer discharges injectivity
  vacuously by `fin_cases`.
* Tautology check: ✓ Conclusion `M.SatisfiesD s` does NOT appear
  among hypotheses (B and E are distinct §321 predicates).
* Identity check: ✓ Proof is substantive (~146 LOC including
  docstring) including a genuine Vandermonde-inversion appeal and
  two named algebraic sub-lemmas (`h_first`, `h_second`); not
  `exact h_*`.
* Definition smuggling check: ✓ No new defs/structures; consumes
  §321's existing B/D/E predicates (audited cycle 306).
* Hypothesis strength check: All four hypotheses are minimal.
  `B(2s)` is used at exponents `l` (where `1 ≤ l ≤ s ≤ 2s`) and
  `k + l` (where `1 ≤ k + l ≤ 2s`). `E(s, s)` is used at all
  `(k, l) ∈ [1, s]²`. `Function.Injective M.c` is required for the
  Vandermonde matrix to be invertible. None can be weakened.
* Absent theorem check: N/A — no comments promising deferred
  content.

## Dead ends

None. The strategy was followed essentially verbatim with one minor
correction: in the `h_per_j` step, after `rw [← h_pow_split]` and
`field_simp`, the trailing `ring` produced "No goals to be solved"
(verified pitfall #1 from the strategy). Removed the trailing
`ring`; the goal closes on `field_simp` alone.

## Discovery

1. **`Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero` is the
   right tool** for D(s) inversion: its hypothesis shape
   `∀ i : Fin n, ∑ j, v j * f j ^ i = 0` matches exactly the
   residual-times-`c^(l-1)` form that arises after factoring
   `cⱼ'^(l-1)` out of the inner sum. No transposition or
   reformulation needed.

2. **The `(i : ℕ) = l - 1` reparameterisation** via
   `set l := i.val + 1` + `hi_eq : (i : ℕ) = l - 1 := by simp [l_def]`
   works cleanly. Once `rw [hi_eq]` is applied, the goal exponent
   matches the `(l - 1)` form used throughout the §321 B/C/D/E
   predicates, and the rest of the proof flows naturally.

3. **`field_simp` alone closes the per-`j'` power identity** after
   `rw [← h_pow_split]`. The strategy correctly flagged this as a
   likely "No goals to be solved" trap from a trailing `ring`; we
   confirm and remove.

4. **`Finset.sum_sub_distrib`** is indeed the canonical Mathlib
   name (NOT `sub_sum` or `Finset.sum_sub`), used twice in this
   proof. Transitively imported by `Mathlib.Algebra.BigOperators.Fin`.

## Suggested next approach

**Cycle 316: ship (342n) `B(2s) ∧ E(s, s) ⇒ C(s)`.** This is the
matching Vandermonde-converse clause; the strategy file already
provides the recipe. Structurally identical to (342p) but with an
additional hypothesis `(hb : ∀ i, M.b i ≠ 0)` because the
Vandermonde matrix appears as `diag(b) · V`, requiring both factors
invertible.

The proof should follow the same skeleton:
* Define the C(s) residual `v i' := b i' · ((∑ⱼ Aᵢ'ⱼ cⱼ^(k-1)) − cᵢ'^k/k)`
  (or equivalent scaling).
* Apply `Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero` with
  `f = M.c` and injectivity.
* Two named sub-sums: one routed through `E(s, s)`, one through
  `B(2s) × (sum of bᵢ cᵢ^(p-1))`.
* Divide by `M.b i` (using `hb i`) to extract the C(s) form.

With (342p) shipped as the template and `eq_zero_of_forall_pow_sum_mul_pow_eq_zero`
already imported, (342n) should close in a single cycle (~150 LOC).

After (342n), the four "purely algebraic" clauses (342m, n, o, p)
of `thm:342C` are all formalised. The remaining clauses (342j, k, l)
require `G(2s)` and elementary-differential machinery from
`thm:314A`, which is blocked per `lem_310B_plan.md`. So after cycle
316, the natural pivots are:

* `thm:344A` Radau/Lobatto methods (concrete-tableau ships)
* `cor:342D` (corollary of `thm:342C` already shipped piecewise)
* `lem:359A` V/W transformations
