# Cycle 321 Results

## Worked on

§344 Phase D.1 — small-`s` Lagrange quadrature weights for the
Radau I, Radau II, and Lobatto quadrature families: six
`_quadratureWeights` definitions plus seven `_apply` theorems
verifying each entry's textbook value, plus three weight-sum
non-vacuity examples.

The cycle 320 task results explicitly recommended "Cycle 321
target: small-`s` Lagrange quadrature weights"; this cycle
delivers that target end-to-end.

## Approach

Followed the cycle 321 strategy verbatim, mirroring cycle 303's
`butcherShiftedLegendre_quadratureWeights` construction
(`OpenMath/Chapter3/Section342.lean:6233`) at the six
cycle-320 abscissae arrays.

### Step 1 — Definitions (six total, ~6 LOC each).

Each `_quadratureWeights_<s>` is a `noncomputable def : Fin s → ℝ`
defined as `b_j := ∫₀¹ (Lagrange.basis Finset.univ <abscissae> j).eval x dx`
— the integral over `[0, 1]` of the Lagrange basis polynomial
interpolating `δ_jk` at the abscissae:

- `butcherRadauI_quadratureWeights_one  : Fin 1 → ℝ`
- `butcherRadauI_quadratureWeights_two  : Fin 2 → ℝ`
- `butcherRadauII_quadratureWeights_one : Fin 1 → ℝ`
- `butcherRadauII_quadratureWeights_two : Fin 2 → ℝ`
- `butcherLobatto_quadratureWeights_two : Fin 2 → ℝ`
- `butcherLobatto_quadratureWeights_three: Fin 3 → ℝ`

### Step 2 — `s = 1` `_apply` theorems (~3 LOC each).

Two theorems (`butcherRadauI_quadratureWeights_one_apply` and
`butcherRadauII_quadratureWeights_one_apply`), each closed by
`unfold + simp [Lagrange.basis_singleton, Polynomial.eval_one]`
— the cycle 308
`butcherShiftedLegendre_quadratureWeights_one_apply` one-liner
template applied verbatim. The Lagrange basis on a singleton is
identically `1`, so the defining integral collapses to
`∫₀¹ 1 dx = 1`.

### Step 3 — `s = 2` `_apply` theorems (~22 LOC each).

Four theorems (`butcherLobatto_quadratureWeights_two_apply_zero`,
`butcherLobatto_quadratureWeights_two_apply_one`,
`butcherRadauI_quadratureWeights_two_apply_zero/_one`,
`butcherRadauII_quadratureWeights_two_apply_zero/_one`). Recipe:

1. `unfold` the weight def.
2. `have h_erase : (Finset.univ : Finset (Fin 2)).erase ⟨j, _⟩ = {⟨1-j, _⟩} := by decide`
   — the `decide` discharges the small `Finset (Fin 2)` equality
   via the `DecidableEq` instance.
3. Inside a `have h_eval : ∀ x : ℝ, (Lagrange.basis …).eval x = <explicit>`,
   apply `rw [Lagrange.basis, h_erase, Finset.prod_singleton,
   Lagrange.basisDivisor]` to reduce the Lagrange basis polynomial
   to the explicit `(x − c_k)/(c_j − c_k)` expression. Closed by
   `simp [<abscissae_def>, Polynomial.eval_*]` (plus `ring` for the
   four cases with non-trivial slope coefficients; the three cases
   where simp closes the goal arithmetically have no trailing `ring`).
4. `simp_rw [h_eval]` rewrites the integrand inside the integral
   to the explicit polynomial expression.
5. Split the integral via `intervalIntegral.integral_sub` /
   `_add` / `_const_mul`, citing
   `IntervalIntegrable (fun x => x) MeasureTheory.volume 0 1`
   from `continuous_id.intervalIntegrable 0 1`.
6. Close numerically with `integral_pow` (for `∫ x = 1/2` and
   `∫ x^2 = 1/3`) + `integral_one` + `norm_num`.

### Step 4 — `s = 3` `_apply` theorems (~28 LOC each).

Three theorems
(`butcherLobatto_quadratureWeights_three_apply_zero`, `_one`,
`_two`). Recipe extends Step 3:

1. `unfold` + `h_erase` (now to a pair `{⟨k, _⟩, ⟨l, _⟩}` via
   `decide`) + `h_ne : ⟨k, _⟩ ≠ ⟨l, _⟩` (via `decide`).
2. The basis polynomial is a `Finset.prod_pair h_ne` of two
   `basisDivisor` factors. `rw [Lagrange.basis, h_erase,
   Finset.prod_pair h_ne, Polynomial.eval_mul, Lagrange.basisDivisor,
   Lagrange.basisDivisor]` reduces to the explicit polynomial form
   `(slope₀ · (x − c_a)) · (slope₁ · (x − c_b))`.
3. `simp [<abscissae_def>, Polynomial.eval_*] + ring` closes the
   pointwise polynomial identity.
4. `simp_rw [h_eval]` rewrites the integrand to the quadratic
   polynomial `α x² + β x + γ`.
5. Split via `intervalIntegral.integral_add` / `_sub` /
   `_const_mul`, citing `(continuous_pow 2).intervalIntegrable 0 1`
   for `x^2`.
6. Close with `integral_pow` (for `∫ x^2 = 1/3` and `∫ x = 1/2`) +
   `integral_one` + `norm_num`.

### Step 5 — Weight-sum non-vacuity examples.

Three `example` blocks confirm `∑ⱼ bⱼ = 1` for the multi-stage
cases (the elementary observation that any interpolatory
quadrature exact on constants has weights summing to `1` =
`∫₀¹ 1 dx`):

- Radau I `s = 2`: `1/4 + 3/4 = 1`
- Lobatto `s = 2`: `1/2 + 1/2 = 1` (trapezoidal)
- Lobatto `s = 3`: `1/6 + 2/3 + 1/6 = 1` (Simpson)

Each closed by `rw [<apply_lemmas>] + norm_num`.

### Verification

- `lake env lean OpenMath/Chapter3/Section344.lean` clean exit
  (no errors, no warnings).
- `lake env lean OpenMath/Chapter3.lean` clean exit (~28 s, full
  Chapter 3 rebuild).
- `lean_verify` on three representative theorems
  (`butcherRadauI_quadratureWeights_two_apply_zero`,
  `butcherLobatto_quadratureWeights_two_apply_zero`,
  `butcherLobatto_quadratureWeights_three_apply_zero`) all return
  `["propext", "Classical.choice", "Quot.sound"]`, no extra
  axioms.

## Result

**SUCCESS.** All twelve cycle-321 deliverables shipped axiom-clean
plus three non-vacuity examples. Section344.lean grew from
768 → 1158 LOC (390 net LOC, above the ~200 LOC strategy
estimate because each `s = 2`/`s = 3` proof carried the full
`integral_pow` / `intervalIntegrable` boilerplate inline rather
than via a shared helper — keeping with cycle 274's
`_norm_sq_*` template precedent).

No sorries introduced. No `axiom` / `constant` declarations.
No `maxHeartbeats` bumps. No Aristotle calls (per strategy —
each proof is mechanical, manual closure fits well within a
single cycle).

## Faithfulness check

Six new `noncomputable def`s — each a packaging of textbook
Lagrange quadrature weights `b_j := ∫₀¹ L_j(x) dx`. Anchor
entity `thm:344A` (Butcher §344 p. 244):

> Furthermore, for each of the three quadrature formulae,
> `c_i ∈ [0, 1]` for `i = 1, 2, …, s`, and `b_i > 0` for
> `i = 1, 2, …, s`.

The `_quadratureWeights_*` definitions ship the `b_i` values
(closed-form rationals at small `s`); the positivity clause
`b_i > 0` is a downstream Phase-B clause not in the cycle 321
scope.

- **`butcherRadauI_quadratureWeights_one : Fin 1 → ℝ`**
  = `(1)` via `_one_apply`. Single node `c_1 = 0`, unique
  weight `b_1 = ∫₀¹ 1 dx = 1`.
  Lean statement captures: same content as the textbook's
  implicit single-stage Radau I rule (one node, weight `1`,
  consistent with the constant-1 quadrature).

- **`butcherRadauI_quadratureWeights_two : Fin 2 → ℝ`**
  = `(1/4, 3/4)` via `_two_apply_zero` and `_two_apply_one`.
  Two nodes `(0, 2/3)`. Matches Butcher Table 344(I) p. 245.

- **`butcherRadauII_quadratureWeights_one : Fin 1 → ℝ`**
  = `(1)` via `_one_apply`. Single node `c_1 = 1`.

- **`butcherRadauII_quadratureWeights_two : Fin 2 → ℝ`**
  = `(3/4, 1/4)` via `_two_apply_zero` and `_two_apply_one`.
  Two nodes `(1/3, 1)`. Matches Butcher Table 344(II) p. 245.

- **`butcherLobatto_quadratureWeights_two : Fin 2 → ℝ`**
  = `(1/2, 1/2)` via `_two_apply_zero` and `_two_apply_one`.
  Two nodes `(0, 1)`. This is the textbook trapezoidal rule.

- **`butcherLobatto_quadratureWeights_three : Fin 3 → ℝ`**
  = `(1/6, 2/3, 1/6)` via `_three_apply_zero/_one/_two`. Three
  nodes `(0, 1/2, 1)`. This is Simpson's rule.

All values were paper-verified prior to formalization (strategy
table reproduced in the cycle 321 docstrings):

- Lobatto `s=2`: `L_0 = 1 − x, L_1 = x`,
  `∫₀¹ L_0 = 1 − 1/2 = 1/2` ✓; `∫₀¹ L_1 = 1/2` ✓.
- Radau I `s=2`: `L_0 = 1 − (3/2)x, L_1 = (3/2)x`,
  `∫₀¹ L_0 = 1 − 3/4 = 1/4` ✓; `∫₀¹ L_1 = 3/4` ✓.
- Radau II `s=2`: `L_0 = 3/2 − (3/2)x, L_1 = (3/2)x − 1/2`,
  `∫₀¹ L_0 = 3/2 − 3/4 = 3/4` ✓; `∫₀¹ L_1 = 3/4 − 1/2 = 1/4` ✓.
- Lobatto `s=3`: `L_0 = 2x² − 3x + 1, L_1 = −4x² + 4x,
  L_2 = 2x² − x`. Integrals `(1/6, 2/3, 1/6)` ✓ (Simpson).

Seven new `theorem`s plus three new `example` blocks:

- **Tautology check**: no theorem conclusion appears as a
  hypothesis (each `_apply` theorem has no hypotheses beyond
  the implicit `Fin n` typing). No vacuous statements.

- **Identity check**: no proof is `exact h` or a pure
  re-export. Each proof does real arithmetic work — unfolds the
  Lagrange basis polynomial, splits the integral via interval
  integration lemmas, and closes the residue with `norm_num`.

- **Definition smuggling check**: the `_quadratureWeights_*`
  definitions capture the *primary* mathematical meaning (the
  integral of the Lagrange basis polynomial); the `_apply`
  theorems compute the closed-form rational values as genuine
  arithmetic consequences, not as part of the definition. The
  weights are NOT defined as `(1/4, 3/4)` directly — they are
  defined as integrals, and the `_apply` theorems prove the
  values via direct computation.

- **Hypothesis strength check**: all twelve `_apply` theorems
  have no hypotheses beyond the implicit `Fin n` index. The
  three weight-sum examples have no hypotheses either. Minimal
  signatures throughout.

- **Absent theorem check**: every theorem promised in the
  strategy (12 deliverables) is present and proved. No
  `sorry` placeholders, no orphan promises.

## Dead ends

None this cycle — all deliverables landed on the first
implementation pass after one small correction. The initial
draft of the `s = 2` proofs included unconditional trailing
`ring` calls after `simp`; for three of the six cases
(Lobatto `j=0`, Lobatto `j=1`, Radau I `j=1`) the `simp` over
`Polynomial.eval_*` plus the Lagrange basisDivisor unfolding
already closed the goal arithmetically (basisDivisor evaluates
to a sufficiently simple polynomial that `simp`'s field-aware
norm_num closes the equality directly), leaving the trailing
`ring` to produce a "No goals to be solved" error. Resolved by
removing the spurious `ring`s and trimming the now-unused
`Polynomial.eval_mul` / `_C` / `_sub` simp arguments. The
remaining three `s = 2` cases (Radau I `j=0`, Radau II `j=0`,
Radau II `j=1`) and all three `s = 3` Lobatto cases retain a
trailing `ring` because the `simp` arithmetic leaves a small
residue (e.g. `(2/3)⁻¹ * x` vs `(3/2) * x` requires `simp`
inverse reasoning that misses the rearrangement).

Heartbeat risk R1 (Lobatto `s = 3` quartic blowup) did not
materialize — the integrand is quadratic, the `Finset.prod_pair`
expansion plus `simp` closes the pointwise identity within
default heartbeats, and the integral split via three
`integral_add`/`_sub`/`_const_mul` rewrites + `norm_num` runs
clean. No fallback to per-weight decomposition was needed.

## Discovery

* **`decide` discharges small `Finset (Fin n).erase` equalities
  efficiently** (`n ≤ 3`). The
  `(Finset.univ : Finset (Fin 3)).erase ⟨k, _⟩ = {⟨a, _⟩, ⟨b, _⟩}`
  identities used in the `s = 3` proofs all close by `decide`
  with no observable slowdown. Likewise for `Fin n` pair
  inequalities like `⟨1, _⟩ ≠ ⟨2, _⟩`.

* **`Finset.prod_pair h_ne` is the canonical reducer for
  two-factor Lagrange basis products**. Given the `h_erase`
  identity to a literal pair `{a, b}` and the distinctness
  hypothesis `h_ne : a ≠ b`,
  `rw [Lagrange.basis, h_erase, Finset.prod_pair h_ne]` reduces
  the basis polynomial to `basisDivisor (v i) (v a) *
  basisDivisor (v i) (v b)` in one step. The product expansion
  follows by `rw [Polynomial.eval_mul, Lagrange.basisDivisor,
  Lagrange.basisDivisor]` plus `simp` for the basisDivisor's
  internal `C (...)⁻¹ * (X - C ...)` structure.

* **`simp` field-aware normalization closes Lagrange basis
  pointwise identities for s=2 cases without `ring`** when the
  basisDivisor slope is a unit fraction (e.g. `(1)⁻¹ = 1`, or
  `(-1)⁻¹ = -1` simplifying `(-1) * (x - 1)` to `1 - x`). For
  non-unit slopes (e.g. `(2/3)⁻¹` requiring rearrangement to
  `3/2`), `simp` leaves a small residue closed by `ring`.

* **`(continuous_pow 2).intervalIntegrable 0 1` is the cycle 274
  template idiom for `IntervalIntegrable (fun x => x ^ 2)` —
  cleaner than `(continuous_id.intervalIntegrable 0 1).pow 2` or
  similar combinator chains**. Used identically in cycle 274's
  `butcherShiftedLegendre_norm_sq_two` and replicated here for
  Lobatto `s = 3`.

* **The strategy's "tail -80 | head -100" pipe interaction with
  bash's job control can mask `lake env lean` exit codes**: a
  500 s `timeout` on the outer command kills lake, but the
  `tail -80` pipe survives and prints `Terminated` instead of
  the partial build output. Re-running with a 1500 s timeout
  succeeded with no output (clean compile). Lesson: when
  `lake env lean` reports no output, treat it as `BUILD OK` —
  it does NOT write to stdout on a clean compile.

## Suggested next approach

**Cycle 322 target**: small-`s` `RKTableau` construction
(Phase D.2 — direct lift of the cycle 320 abscissae + cycle 321
weights into the `OpenMath.Chapter3.Section312.RKTableau`
typeclass packaging). Two natural starting candidates per the
cycle 321 strategy §10:

- **Radau IIA `s = 1`** = backward Euler with
  `A = !![1]`, `b = !![1]`, `c = !![1]`. The simplest one-stage
  assembly; tests the `RKTableau` packaging end-to-end on a
  trivial stage count.

- **Lobatto IIIA `s = 2`** = trapezoidal rule with
  `A = !![0, 0; 1/2, 1/2]`. Two-stage, but the `A`-matrix is
  triangular (in fact has a zero first row, making it
  semi-explicit) so the collocation `Aᵢⱼ := ∫₀^{cᵢ} L_j(x) dx`
  computation reduces to small closed-form integrals analogous
  to cycle 321's `b_j` computations. The natural test bed for
  the collocation A-matrix construction analogous to cycle 308's
  `butcherShiftedLegendre_collocationA`.

A cleaner third option: **Lobatto IIIB `s = 2`** has
`A = !![1/2, 0; 1/2, 0]` (also semi-explicit), differing from
IIIA by the column-stage choice — also a natural sequel.

Per Butcher's Table 344(I) p. 245, the `s = 1` Radau IIA tableau
is `c = !![1], b = !![1], A = !![1]`, exactly the backward
Euler form. The cycle 322 deliverable would package these into
`butcherRadauIIA_one : RKTableau 1` (or analogous Lobatto IIIA
witness) with the `c = butcherRadauII_zeros_one`,
`b = butcherRadauII_quadratureWeights_one`, and `A` derived
either via the collocation construction
`Aᵢⱼ := ∫₀^{cᵢ} L_j(x) dx` (mirroring cycle 308's
`butcherShiftedLegendre_collocationA_one_apply`) or via direct
`Matrix.of` packaging at small `s`. The Phase D.2 §342
collocation precedent suggests the former is the textbook-
faithful path; cycle 322 should ship one such tableau axiom-
clean as the simplest §344 `RKTableau` non-vacuity anchor.

Phase B.2 (`2s-2` / `2s-3` polynomial exactness via the
textbook polynomial-division argument with cycle 318's
orthogonality lemmas) and general-`s` Phase C.2+ (abscissae
construction via sign-change argument) remain multi-cycle
deferred per cycle 320's task results — small-`s` `RKTableau`
construction is the natural next stepping stone.
