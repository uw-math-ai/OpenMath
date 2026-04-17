# Cycle 98 Results

## Worked on
Converse implications of Theorem 342C:
- `SatisfiesC_of_B_E`: B(2s) ∧ E(s,s) ⇒ C(s) (implication 342n)
- `SatisfiesD_of_B_E`: B(2s) ∧ E(s,s) ⇒ D(s) (implication 342p)

## Approach
Both proofs use Vandermonde matrix uniqueness via `Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero` from `Mathlib.LinearAlgebra.Vandermonde`.

**D converse (SatisfiesD_of_B_E):**
1. For fixed k, define defect `u_j = (∑_i b_i c_i^{k-1} A_{ij}) - b_j/k * (1 - c_j^k)`
2. Show `∑_j u_j * c_j^{l-1} = 0` for all l = 1,...,s by combining E(s,s) with B(2s)
3. Apply Vandermonde uniqueness (using `Function.Injective t.c`) to conclude `u = 0`
4. Hypothesis: only needs distinct nodes (`hc_inj`)

**C converse (SatisfiesC_of_B_E):**
1. For fixed l, define weighted defect `v_i = b_i * (∑_j A_{ij} c_j^{l-1} - c_i^l / l)`
2. Show `∑_i v_i * c_i^{k-1} = 0` for all k = 1,...,s by combining E(s,s) with B(2s)
3. Apply Vandermonde uniqueness to conclude `v = 0`
4. Since `b_i ≠ 0` for all i, the C-defect itself is zero
5. Hypothesis: needs both distinct nodes (`hc_inj`) and nonzero weights (`hb_ne`)

## Result
SUCCESS — both theorems proved, verified axiom-clean (propext, Classical.choice, Quot.sound only).

## Dead ends
- `Nat.sub_one_add_one_of_pos` doesn't exist; used `set l' := ↑l + 1` pattern instead to bridge index offset
- `Finset.sum_sub_distrib` needs `(a - b)` not `(a - b) * c`; had to distribute multiplication first via `simp_rw`
- After `Finset.sum_mul`, the goal was already solved without needing further `sum_congr + ring`

## Discovery
- `Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero` is the transposed Vandermonde uniqueness lemma — the outer quantifier is over the exponent index, matching our sum shape for both C and D converses
- The index shift from `l ∈ {1,...,s}` to `Fin s` (0-indexed) is cleanly handled by `set l' := ↑l + 1` pattern
- Added `import Mathlib.LinearAlgebra.Vandermonde` to Collocation.lean

## Suggested next approach
- Theorem 342C implications (342j), (342k), (342l) require rooted tree infrastructure from thm:301A
- Next major target: define `RootedTree` inductive type, `order`, `symmetry`, `density` (thm:301A)
- Independent branch: def:355A (order stars/arrows) using complex analysis
