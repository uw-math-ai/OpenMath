# Cycle 087 Results

## Worked on
`def:520C` — three definitions and two non-vacuity witnesses in
`OpenMath/Chapter5/Section520.lean`:

- `GeneralLinearMethod.stabilityFunction : ℂ → ℂ → ℂ`
  (`Φ(w, z) = det(wI − M(z))`)
- `GeneralLinearMethod.stabilityRegion : Set ℂ`
  (`{ z | ∃ C, PowerBounded C (M.stabilityMatrix z) }`)
- `GeneralLinearMethod.instabilityRegion : Set ℂ`
  (`(M.stabilityRegion)ᶜ`)
- `explicitEulerGLM_stabilityFunction_at_zero : Φ(w, 0) = w − 1`
- `explicitEulerGLM_zero_mem_stabilityRegion : 0 ∈ stabilityRegion`

## Approach
Followed the planner's strategy verbatim. Appended the three new
`noncomputable def`s and the two witnesses to the existing
`namespace OpenMath.Chapter5.Section510` block in
`OpenMath/Chapter5/Section520.lean`, so dot notation
`M.stabilityFunction`, `M.stabilityRegion`, `M.instabilityRegion`
works on values of `GeneralLinearMethod s r` (avoiding the cycle 086
namespace footgun).

## Result
SUCCESS — all five declarations compile cleanly. Single-file check
`lake env lean OpenMath/Chapter5/Section520.lean` produces no
diagnostics. After `lake build OpenMath.Chapter5.Section520`,
`#print axioms` reports `[propext, Classical.choice, Quot.sound]` for
each of the five new declarations.

Two minor fixups beyond the planner's draft:

1. **Missing scoped `open`**: `Section520.lean`'s `Section510`
   namespace block needed `open scoped Matrix.Norms.Operator` to
   bring the `linftyOpSemiNormedRing` instance into scope so
   `PowerBounded C (M.stabilityMatrix z)` typechecks. The companion
   file `Section510.lean` had the open already; scoped opens do not
   propagate across files. Added one line.
2. **`Matrix.one_fin_one` not visible**: the planner's draft
   `simp [Matrix.one_fin_one]` failed with "Unknown constant". Bare
   `simp` already closes `!![(1 : ℂ) + 0] i j = (1 : Matrix _ _ ℂ) i j`
   pointwise after `fin_cases`, so removed the lemma argument.
   `lean_run_code` confirmed it was an unused simp argument.

Aristotle was not used this cycle: all five proofs closed manually
in one edit cycle, matching the planner's "likely unnecessary" call.

## Faithfulness check

### `def GeneralLinearMethod.stabilityFunction`
- Entity ID: `def:520C` (first clause)
- Textbook statement (from `entities/def_520C.json`):
  > The 'stability function' for the method is the polynomial
  > Φ(w, z) given by Φ(w, z) = det(wI − M(z))
- Lean statement captures: same content. We encode `Φ : ℂ → ℂ → ℂ`
  by literal `det(w • 1 − M.stabilityMatrix z)`.
- Divergence: the textbook calls Φ "the polynomial" then
  immediately notes it is "in fact a rational function" because
  `M(z)` involves `(I − zA)⁻¹`. We encode the function form,
  matching the literal formula. The "numerator of Φ" notational
  alternative is documented in the docstring and explicitly
  out of scope (no downstream consumer of `def:520C` needs it).

### `def GeneralLinearMethod.stabilityRegion`
- Entity ID: `def:520C` (second clause)
- Textbook statement:
  > the 'stability region' is the subset of the complex plane such
  > that if z is in this subset, then sup_{n=1..∞} ‖M(z)^n‖ < ∞
- Lean statement captures: same content. The supremum-finiteness
  condition `sup_n ‖a^n‖ < ∞` is equivalent on a `SeminormedRing`
  to `∃ C, ∀ k, ‖a^k‖ ≤ C` — the spelling already adopted as
  `OpenMath.Chapter1.Section142.PowerBounded`. We re-use that
  predicate via `∃ C, PowerBounded C (M.stabilityMatrix z)`,
  matching the canonical §142 form already used by `def:510C`.
- Divergence (none in content): the textbook quantifies `n = 1, ..., ∞`
  while `PowerBounded` quantifies all `k : ℕ`. The two are
  equivalent on a normed ring (`a^0 = 1` adds at most a fixed
  constant `‖1‖`), and the §510C docstring documents this
  equivalence already.

### `def GeneralLinearMethod.instabilityRegion`
- Entity ID: `def:520C` (third clause)
- Textbook statement:
  > We refer to the 'instability region' as the complement of the
  > stability region.
- Lean statement captures: same content (literal complement
  `(M.stabilityRegion)ᶜ`).

### `theorem explicitEulerGLM_stabilityFunction_at_zero`
- Tautology check: conclusion is a concrete equality
  `Φ(w, 0) = w − 1`, not a hypothesis re-export. ✓
- Identity check: proof unfolds `stabilityFunction`, applies the
  cycle-086 lemma `explicitEulerGLM_stabilityMatrix`, then reduces
  the 1×1 determinant via `Matrix.det_fin_one` and `simp`.
  Real reduction. ✓

### `theorem explicitEulerGLM_zero_mem_stabilityRegion`
- Tautology check: conclusion is set-membership
  `(0 : ℂ) ∈ stabilityRegion`, providing the bound
  `C = ‖(1 : Matrix (Fin 1) (Fin 1) ℂ)‖`. ✓
- Identity check: proof rewrites `M(0) = !![1 + 0]`, identifies
  `!![1 + 0]` with the matrix-`1`, then closes with `one_pow` and
  `le_refl`. Real reduction. ✓

### Hypothesis-strength check
All three definitions are hypothesis-free. Both witnesses take the
unfixed scalar `w` (or no arguments) and prove from the universally
applicable `explicitEulerGLM_stabilityMatrix` lemma. No extraneous
hypotheses introduced.

### Definition smuggling check
- `stabilityFunction` is the literal `det(wI − M(z))` formula, not
  a derived characterization.
- `stabilityRegion` uses the `PowerBounded` predicate which is the
  literal supremum-finiteness condition (existence of uniform
  bound iff bounded supremum on a `SeminormedRing`). The §510C
  docstring already documents this equivalence as the
  §142-canonical spelling. Not smuggling.
- `instabilityRegion` is literal complement.

## Dead ends
- Initial draft missed `open scoped Matrix.Norms.Operator` inside
  the `Section510` namespace block of `Section520.lean`, so the
  `SeminormedRing (Matrix _ _ ℂ)` synthesis failed. One-line fix
  identified by `lean_diagnostic_messages`.
- Initial draft used `Matrix.one_fin_one` as a `simp` argument; the
  lemma is not in the current Mathlib pin under that name (or is
  already a `simp` lemma so the argument is unused). Bare `simp`
  closes the goal; replaced.

## Discovery
- The default Mathlib `Matrix.linftyOpSemiNormedRing` instance is
  scoped behind `Matrix.Norms.Operator`. Scoped opens do **not**
  propagate across files: each file that wants the instance must
  re-open the scope inside its namespace. Section510.lean already
  did this; Section520.lean did not for the `Section510` namespace
  block where the new `def`s landed. Worth noting for future
  cycles that add normed-matrix predicates: always re-open the
  scope at the top of the namespace block, regardless of which
  file the namespace was originally declared in.
- `Matrix.det_fin_one` collapses the 1×1 determinant cleanly to
  `M 0 0`; combined with `!!` notation the result simp's to a
  scalar arithmetic goal. Useful pattern for explicit-Euler-style
  non-vacuity witnesses on §520-class predicates.
- `lean_run_code` (with self-contained imports) is much faster
  than full `lake env lean` for testing single proof steps. Using
  it to validate `simp` argument lists pre-edit saves an
  edit-compile cycle.

## Suggested next approach
Per the planner's Cycle 088 suggestion, target `thm:520B`:
"for a linear differential equation `y' = qy`, the GLM iteration
yields `y^[n] = M(z) y^[n-1]` with `z = hq`". The infrastructure
gap is: there is no Lean encoding of "the GLM iteration `(500c)`"
yet. The Cycle 088 planner will need to decide the encoding —
options include:

1. A direct one-step propagation `propagate : (Fin r → ℝ) → ℝ → (Fin r → ℝ)`
   parameterised by stepsize `h` and a function `f : ℝ → ℝ`.
2. A more abstract `GLMStep` predicate relating two consecutive
   `y^[n-1]`, `y^[n]` vectors and the internal-stage values.

Option 2 is closer to Butcher's §500 presentation (the iteration
`(500c)` is implicit when `A` is non-zero); option 1 is easier to
state but requires additional hypotheses for implicit methods.

Independently, `def:520E` (A-stable) is a near-trivial follow-up
once `def:520C` is in place: A-stable means `{z | Re z < 0} ⊆
M.stabilityRegion`. It does not require `thm:520B` and could be
processed in parallel.
