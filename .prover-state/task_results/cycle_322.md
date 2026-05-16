# Cycle 322 Results

## Worked on
§344 Phase D.2 — small-`s` `RKTableau` (Radau IIA `s = 1`):
1. `butcherRadauII_collocationA_one` — collocation A-matrix at `s = 1`.
2. `butcherRadauII_collocationA_one_apply` — value `1`.
3. `butcherRadauIIA_one` — assembled 1-stage Radau IIA `RKTableau`.
4. `butcherBackwardEulerRK` — direct backward-Euler `RKTableau` for cross-validation.
5. `butcherRadauIIA_one_eq_backwardEuler` — coincidence theorem.
6. `SatisfiesB 1` non-vacuity example for `butcherRadauIIA_one`.

## Approach
Followed the cycle 308 / `butcherGaussLegendreRK_one_eq_gaussLegendre1Stage`
template verbatim (`Section342.lean:6840–6912`):
- Define the collocation A-matrix as
  `∫₀^{c_i} L_j(x) dx` (integral over `[0, butcherRadauII_zeros_one 0]`).
- Close the `_apply` theorem via `simp [butcherRadauII_zeros_one,
  Lagrange.basis_singleton, Polynomial.eval_one]` after unfolding +
  a `show` ascription that reframes the integrand to its
  canonical form.
- Assemble the `RKTableau 1` with the cycle 320 zeros, cycle 321
  weights, and the new collocation A-matrix as the three fields.
- Cross-validate against a directly defined backward-Euler tableau
  via `RKTableau.mk.injEq` decomposition + `funext` + `fin_cases`
  on each field; close each branch with the appropriate `_apply`
  theorem (for `c` the equation reduces to `rfl` since the
  pattern-matched zero array evaluates the singleton entry to `1`
  by definition).
- Lift `SatisfiesB 1` through the coincidence theorem and close
  via `interval_cases k` + `simp [butcherBackwardEulerRK]`.

## Result
SUCCESS — all six new public symbols compile and `lean_verify`
confirms axiom-clean (`[propext, Classical.choice, Quot.sound]`).

- `butcherRadauII_collocationA_one_apply`: axioms `[propext, Classical.choice, Quot.sound]`.
- `butcherRadauIIA_one_eq_backwardEuler`: axioms `[propext, Classical.choice, Quot.sound]`.
- `Section344.lean` LOC: 1158 → 1247 (+89 LOC; estimate was 65–70 — within range).
- `lake env lean OpenMath/Chapter3.lean` clean (no errors, no warnings).
- 0 explicit sorries introduced.

## Faithfulness check

### `butcherRadauII_collocationA_one` (new `def`)
- Entity ID: `thm:344A` — *"Methods based on Radau and Lobatto
  quadrature"* (Butcher §344, p. 244). Textbook (quoted from
  `extraction/formalization_data/entities/thm_344A.json`):
  > Furthermore, for each of the three quadrature formulae,
  > c_i ∈ [0, 1], for i = 1, 2, …, s, and b_i > 0, for i = 1, 2, …, s.
  Also (from `proof_text`):
  > Table 344(I) Methods in the Radau and Lobatto families … Radau
  > IIA — Radau II quadrature — The reflections of Radau I.
- Lean statement captures: **same content** — the collocation
  A-matrix at the canonical Radau II abscissae is the standard
  recipe `A_{ij} := ∫₀^{c_i} L_j(x) dx`. At `s = 1` the integral
  collapses to `∫₀^1 1 dx = 1`, matching Butcher Table 344(II)
  entry at `s = 1` (backward Euler).
- No definition smuggling: the integral is the literal collocation
  definition, not a backward-engineered tautology.

### `butcherRadauIIA_one` (new `def`)
- Field-by-field correspondence with Butcher §344 / Table 344(II)
  at `s = 1`: `c = (1)`, `b = (1)`, `A = ((1))`. **same content**.
- No `Prop` fields; pure data.

### `butcherBackwardEulerRK` (new `def`)
- Standard backward Euler form `y_{n+1} = y_n + h · f(y_{n+1})`
  via implicit-stage equation `Y = y₀ + h · 1 · f(Y)`,
  `y₁ = y₀ + h · 1 · f(Y) = Y`. Recovers `y₁ = y₀ + h · f(y₁)`.
  **Faithful** to backward Euler.
- Independently declared (not derived from collocation) so the
  coincidence theorem is genuine cross-validation.

### `butcherRadauII_collocationA_one_apply` (new `theorem`)
- Tautology check: hypothesis-free; conclusion `... = 1` is not a
  hypothesis re-export.
- Identity check: closed via `unfold + show + simp`, not `exact h`.
- Hypothesis strength: no hypotheses.
- Absent theorem check: theorem is fully present and proved.

### `butcherRadauIIA_one_eq_backwardEuler` (new `theorem`)
- Tautology check: structure equality, not a hypothesis re-export.
- Identity check: proof routes through three substantive
  evaluations (`_collocationA_one_apply`, `_quadratureWeights_one_apply`,
  and `rfl` reduction of the pattern-matched `_zeros_one`),
  not `exact h` for any single `h`.
- Hypothesis strength: no hypotheses; minimal signature.
- Absent theorem check: all three `?_` branches realised.
- Faithfulness: textbook identification of Radau IIA `s = 1` with
  backward Euler (Butcher §344, Hairer–Wanner Vol. II §IV.5).

### `SatisfiesB 1` example
- Genuine non-vacuity: exercises the `SatisfiesB` predicate from
  `Section321` on the new `butcherRadauIIA_one`.

## Dead ends
None substantive. Minor wrinkle: the strategy template suggested
`exact butcherRadauII_zeros_one_apply` for the `c`-field branch,
but no such named theorem exists in §344 (the `_zeros_one` array
is defined by direct pattern matching, so `butcherRadauII_zeros_one
⟨0, _⟩` reduces to `1` definitionally). Closed the branch with
`rfl` instead — equivalent strength, simpler proof.

## Discovery
- **Pattern-matched abscissae reduce by `rfl`.** Unlike §342's
  `butcherShiftedLegendre_zeros 1 ⟨0, _⟩` (which goes through the
  `Finset.orderEmbOfFin` enumeration of roots-in-Ioo and needs a
  named `_apply` theorem), the §344 `butcherRadau{I,II}_zeros_one`
  and `butcherLobatto_zeros_two` arrays are explicit `noncomputable
  def`s with `Fin n → ℝ` pattern matches. Evaluation at concrete
  indices is `rfl`. This simplifies downstream `RKTableau`
  coincidence proofs: the `c`-field branch is one line.
- **`show` ascription pattern is load-bearing.** Inside
  `funext + fin_cases + fin_cases`, the proof state retains the
  `⟨0, _⟩`/`⟨0, _⟩` pattern from `fin_cases` rather than reducing
  the `Fin 1` indexing. Without the `show ...` line, `exact
  butcherRadauII_collocationA_one_apply` would not unify. With the
  `show`, the goal is concretely the apply-theorem statement,
  closing in one line.

## Suggested next approach
The cycle 322 deliverable lands the Radau IIA `s = 1` end-to-end
pattern axiom-clean. The natural follow-ups (cycle 323+):

1. **Cycle 323 (recommended):** Lobatto IIIA `s = 2` `RKTableau`
   (trapezoidal-form collocation: `c = (0, 1)`, `b = (1/2, 1/2)`,
   `A = !![0, 0; 1/2, 1/2]`). Same collocation recipe as Radau
   IIA, applied at cycle 320's `butcherLobatto_zeros_two`. The
   two-stage collocation A-matrix requires four entries (Lagrange
   basis evaluation at two abscissae × two integration upper
   limits), each closing via a `Lagrange.basisDivisor`
   manipulation analogous to cycle 321's two-stage weight proofs.
   ~100 LOC expected (two-stage proofs).
2. **Cycle 324+:** Radau IA `s = 1` (forward-shift analogue:
   `c = (0)`, `b = (1)`, `A = !![0]`; this is forward Euler), or
   Radau IIA `s = 2` (`c = (1/3, 1)`, `b = (3/4, 1/4)`, plus a
   four-entry A-matrix).
3. **Eventually:** revisit the Phase B.2 polynomial-exactness
   clauses (`2s − 2` for Radau, `2s − 3` for Lobatto) via the
   cycle 318 orthogonality lemmas + polynomial division — once
   more concrete `RKTableau`s are landed to motivate the
   exactness theorem's `_apply` form.

If the planner judges that Phase D.2 should be deepened before
moving to two-stage `RKTableau`s, an alternative is to add the
`B(1)` non-vacuity example for Radau IIA `s = 1` *via the direct
collocation form without going through coincidence* — this
exercises the `_collocationA_one_apply` theorem directly and
provides a second independent witness for the tableau's basic
order-1 quadrature consistency. ~5 LOC.

Did **not** apply the Priority 0 scanner false-positive restructure
this cycle — the cycle 322 substantive ship is the headline; the
scanner hit at line 573 of cycle 319 content is unaffected by this
cycle's appended content and remains a known false positive.
