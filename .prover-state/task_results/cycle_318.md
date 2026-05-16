# Cycle 318 Results

## Worked on

`thm:344A` Phase B.1 — orthogonality of the §344 Radau/Lobatto
polynomial families against lower-degree test polynomials.

Three new theorems appended to `OpenMath/Chapter3/Section344.lean`:

* `butcherRadauI_orthogonal_to_lower_degree`
* `butcherRadauII_orthogonal_to_lower_degree`
* `butcherLobatto_orthogonal_to_lower_degree`

Plus one private helper (`intervalIntegrable_polyMul`) and three
non-vacuity `example`s firing each lemma on a constant test polynomial.

## Approach

The strategy recipe applied verbatim:

1. Unfold `butcherRadauI`/`butcherRadauII`/`butcherLobatto`.
2. Distribute the integrand `(P_s ± P_{s-k}).eval x * q.eval x` into
   `P_s.eval x * q.eval x ± P_{s-k}.eval x * q.eval x` via
   `Polynomial.eval_add` / `Polynomial.eval_sub` plus `ring`.
3. Split the integral via `intervalIntegral.integral_add`
   (`integral_sub` for Radau II / Lobatto).
4. Apply cycle 292's
   `butcherShiftedLegendre_orthogonal_to_lower_degree` at `m := s`
   (using the `s - k < s` Nat truncated-subtraction inequality, closed
   by `omega`) and `m := s - k` (using the hypothesis directly).
5. `0 + 0 = 0` / `0 - 0 = 0` closes by `ring`.

The integrability discharges for each summand factor through the
`intervalIntegrable_polyMul` helper:
`(p.continuous.mul q.continuous).intervalIntegrable _ _`.

## Result

**SUCCESS** — all three theorems compile, no sorries, axiom-clean
(`[propext, Classical.choice, Quot.sound]` for each). Section344.lean
builds and the Chapter3 aggregator builds without regressions.

LOC added: 154 (well under the 250 abort threshold, slightly over the
~150 LOC target due to per-theorem docstrings; the proof bodies
themselves are ~17 LOC each).

## Faithfulness check

The three new theorems are pure orthogonality corollaries — no new
`def`, `structure`, or `class` introduced this cycle. The textbook
proof on p. 244 of `thm:344A` invokes orthogonality of the
Radau/Lobatto polynomials against lower-degree test polynomials
implicitly when deriving the polynomial-exactness degree. Specifically:

* **Radau I orthogonality** (`butcherRadauI_orthogonal_to_lower_degree`):
  Lean statement
  > `∀ s ≥ 1, q : Polynomial ℝ, q.natDegree < s - 1, ∫₀¹ (P_s^* + P_{s-1}^*).eval x · q.eval x dx = 0`

  Textbook usage (p. 244):
  > "Evaluate the approximate integral of `φ` written in this form, and
  > the terms involving `Q` are zero because of orthogonality."

  The textbook applies this with `Q.natDegree < s - 1` (since
  `φ.natDegree ≤ 2s - 2` and `(P_s^* + P_{s-1}^*).natDegree = s`).
  **Captures: same content.**

* **Radau II orthogonality** (`butcherRadauII_orthogonal_to_lower_degree`):
  Dual statement, same textbook reference, same hypothesis strength.
  **Captures: same content.**

* **Lobatto orthogonality** (`butcherLobatto_orthogonal_to_lower_degree`):
  Lean statement
  > `∀ s ≥ 2, q : Polynomial ℝ, q.natDegree < s - 2, ∫₀¹ (P_s^* - P_{s-2}^*).eval x · q.eval x dx = 0`

  Textbook applies with `Q.natDegree < s - 2` (since `φ.natDegree ≤ 2s - 3`
  and `(P_s^* - P_{s-2}^*).natDegree = s`).
  **Captures: same content.**

### Tautology, identity, definition-smuggling, hypothesis-strength

* **Tautology check**: none of the three conclusions appear as
  hypotheses; each closes by a genuine algebraic collapse
  (`0 + 0 = 0` / `0 - 0 = 0`) after invoking cycle 292's orthogonality.
* **Identity check**: no proof is `exact h`; all three proofs do real
  work via `simp_rw`, `intervalIntegral.integral_add`/`integral_sub`,
  and two applications of cycle 292's main lemma.
* **Definition smuggling**: no new definitions introduced.
* **Hypothesis strength**: `1 ≤ s` (Radau) and `2 ≤ s` (Lobatto) are
  minimal — without them, `s - 1` / `s - 2` collapse to `0` under
  Nat truncated subtraction, the hypothesis `q.natDegree < 0` is
  vacuous, and the corresponding polynomial degenerates (`butcherRadauI 0 = 2 · P_0^* = 2C 1`,
  a constant). Aligned with cycle 317's `s ≥ 1` (Radau) and `s ≥ 2`
  (Lobatto) endpoint hypotheses.

## Dead ends

None. The recipe worked first time on Radau I and was duplicated
verbatim for Radau II and Lobatto with the obvious substitutions.

A minor linter warning (`Polynomial.natDegree_C` flagged as unused in
`simp` calls for the non-vacuity examples) was silenced by replacing
the explicit lemma with bare `simp` — `simp` already knows
`(C 1).natDegree = 0` without the hint.

## Discovery

* The private helper pattern `intervalIntegrable_polyMul` is a clean
  reusable tool — it should be promoted to a shared utility in §342
  or §344 infrastructure if/when the polynomial-exactness theorem
  (Phase B.2) reuses it, but for now its three uses in this cycle
  justify keeping it local to `Section344.lean`.
* `omega` handles `q.natDegree < s - 1` ∧ `1 ≤ s` → `q.natDegree < s`
  for Nat truncated subtraction with no fuss; same for the Lobatto
  `s - 2` variant.
* The `simp_rw` + `intervalIntegral.integral_add` pattern is the
  cleanest way to split a `∫ (f + g) * q` integral; trying to split
  before the `eval`/`mul` distribution leaves a less tractable form.

## Suggested next approach

Cycle 319 should attempt **Phase B.2 — polynomial-exactness for Radau I**:

* Given `φ : Polynomial ℝ` with `φ.natDegree < 2s - 1`, divide by
  `butcherRadauI s` to obtain `Q, R` with
  `Q.natDegree < s - 1` and `R.natDegree < s`.
* Apply this cycle's `butcherRadauI_orthogonal_to_lower_degree` at
  `q := Q` to vanish the `Q · butcherRadauI s` integral contribution.
* The `R` contribution requires Lagrange-interpolation infrastructure
  at the (yet-unconstructed) Radau abscissae; this part may be
  factored out as a separate Phase C deliverable mirroring cycles
  308–312's Gauss-Legendre construction.

Cycle 304's `butcherShiftedLegendre_quadrature_exact_lt_two_n` is the
direct template; the new wrinkles are (i) the divisor is no longer a
single shifted Legendre polynomial but a sum/difference, and (ii) the
`R.natDegree < s` bound (vs. the cleaner `< n` in the Gauss-Legendre
case) flows through `butcherRadauI_natDegree` (cycle 317).

If Phase B.2 turns out to need Phase C (abscissae) first, the
cycle 319 planner can pivot to small-`s` Radau/Lobatto abscissae
(extending cycle 295's `butcherShiftedLegendre_one_root` machinery to
the small-`s` explicit forms shipped in cycle 317).
