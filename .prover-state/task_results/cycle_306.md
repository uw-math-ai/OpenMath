# Cycle 306 Results

## Worked on

§321 prerequisite infrastructure for §342 / §344: the four
order-condition predicates `B(η)`, `C(ξ)`, `D(ζ)`, `E(η, ζ)` on
`RKTableau s`, plus the `simp`-tagged empty-case lemmas, monotonicity
lemmas in the parameter, and substantive non-vacuity witnesses on
`explicitEuler` and a new `gaussLegendre1Stage` (1-stage implicit
midpoint).

Created `OpenMath/Chapter3/Section321.lean` (266 LOC). Wired into
`OpenMath/Chapter3.lean` aggregator.

## Approach

Followed the cycle 306 strategy verbatim:

1. **Pre-flight**: confirmed cycle 305 commit `43d39a4` landed,
   Section342.lean is 6721 LOC with 0 sorries, `RKTableau`'s
   namespace is `OpenMath.Chapter3.Section312`, `explicitEuler` lives
   in `OpenMath/Chapter3/Section312.lean:78`.
2. **Faithfulness check (mandatory §C.1' step)**: read
   `extraction/raw_text/ch03.txt:1771–1929` to verify the textbook
   formulas verbatim:
   * `B(η)`: `∑ᵢ bᵢ cᵢ^{k-1} = 1/k` — line 1772.
   * `C(ξ)`: `∑ⱼ aᵢⱼ cⱼ^{k-1} = cᵢ^k / k` — equation (321b),
     lines 1857–1864.
   * `D(ζ)`: Butcher's prose at p. 173 + Figure 321(ii) introduces
     the `bᵢ cᵢ^{k-1} aᵢⱼ` left-hand factor and the `bⱼ` / `bⱼ cⱼ^k`
     right-hand factors. The k-indexed form
     `∑ᵢ bᵢ cᵢ^{k-1} aᵢⱼ = (bⱼ/k)(1 - cⱼ^k)` is the standard
     generalisation; Hairer–Wanner I.7.5 agrees.
   * `E(η, ζ)`: `1 / (l (k+l))` — equation (321c), lines 1922–1925.
3. Wrote the four `def`s under namespace
   `OpenMath.Chapter3.Section312.RKTableau` (matching the §323 pattern
   in `OpenMath/Chapter3/Section323.lean:51`).
4. Wrote four `@[simp]`-tagged empty-case lemmas closed by `omega` on
   the unsatisfiable `1 ≤ k ∧ k ≤ 0` premise.
5. Wrote four monotonicity lemmas (`SatisfiesB.mono` etc.) by direct
   composition of the upper-bound transitivity step.
6. Non-vacuity examples on `explicitEuler`: `B(1)` and `C(1)` close by
   `interval_cases k` + `simp [RKTableau.explicitEuler]`. Vacuous
   `D(0)` / `E(0,0)` examples close by the empty-case lemmas.
7. Substantive non-vacuity: defined `gaussLegendre1Stage : RKTableau 1`
   (the implicit midpoint method, `c = 1/2, b = 1, A = 1/2`,
   `noncomputable` because `1/2 : ℝ` uses `Real.instDivInvMonoid`).
   Verified it satisfies `B(2)`, `C(1)`, `D(1)`, `E(1,1)` — all four
   conditions for an order-2 method.

## Result

**SUCCESS**. `lake env lean OpenMath/Chapter3/Section321.lean` exits
cleanly (0 errors, 0 warnings after the simp-arg cleanup). `lake build`
fully rebuilds the project (`✔ [1941/1941]`). All 13 declarations
checked under `#print axioms` return `[propext, Classical.choice, Quot.sound]`
(or empty for the type-only ones) — fully axiom-clean. Sorry count
0 → 0.

## Faithfulness check

For each new `def`/`theorem`/`example`:

* **`RKTableau.SatisfiesB`** — Butcher §321 p. 171 statement quoted
  verbatim above. Lean type captures: **same content**. The Lean
  `(k : ℝ)` cast and `k - 1` natural subtraction (safe because the
  `1 ≤ k` hypothesis guarantees `k - 1 = k - 1` in ℕ truncation) match
  the textbook.

* **`RKTableau.SatisfiesC`** — Butcher §321 (321b) quoted verbatim
  above. Lean type captures: **same content**.

* **`RKTableau.SatisfiesD`** — Butcher §321 prose (p. 173) +
  Figure 321(ii) describe the three trees with factors
  `bᵢ cᵢ^{k-1} aᵢⱼ`, `bⱼ`, `bⱼ cⱼ^k`. Lean form
  `∑ᵢ bᵢ cᵢ^{k-1} aᵢⱼ = (bⱼ/k)(1 - cⱼ^k)` captures the standard
  k-indexed generalisation. The `k = 1` case reduces to
  `∑ᵢ bᵢ aᵢⱼ = bⱼ(1 - cⱼ)`, which matches Butcher's reduction in
  §322 p. 175 ("c4 = 1 and D(1) holds"). **Same content with one
  caveat**: Butcher does not write the general k-indexed form
  literally in §321; he describes it via the figure and uses it in
  §342. The k-indexed form is ubiquitous in the Runge–Kutta
  literature (Hairer–Wanner I.7.5) and is the form referenced by
  `cor:342D.context_latex`. Documented in the file docstring's
  faithfulness notes.

* **`RKTableau.SatisfiesE`** — Butcher (321c) quoted verbatim above.
  Lean type captures: **same content**.

* **Empty-case lemmas (`satisfiesB_zero` etc.)** — vacuously true
  because `1 ≤ k ∧ k ≤ 0` is unsatisfiable. `omega` discharges. Not
  smuggling: the predicate's content lives in `Satisfies* η` for
  `η ≥ 1`; `η = 0` being trivial is correct mathematical behaviour
  (no condition to check on an empty index range).

* **Monotonicity lemmas (`SatisfiesB.mono` etc.)** — captures the
  obvious "if the condition holds up to η it holds up to η' ≤ η".
  Useful infrastructure for `thm:342C` (which rephrases B(2s)/C(s)/D(s)
  hypotheses at smaller indices). Not a textbook-stated lemma; pure
  helper.

* **`explicitEuler.SatisfiesB 1`** — concrete arithmetic check.
  ∑ᵢ bᵢ cᵢ^0 = 1 · 0^0 = 1 = 1/1. Lean's `(0:ℝ)^0 = 1` via
  `Monoid.npow_zero` makes this go through.

* **`explicitEuler.SatisfiesC 1`** — for i = 0:
  ∑ⱼ A 0 j · cⱼ^0 = 0 · 0^0 = 0 = c₀^1 / 1.

* **`explicitEuler.SatisfiesD 0`, `.SatisfiesE 0 0`** — vacuous
  applications of the empty-case lemmas.

* **`gaussLegendre1Stage`** — concrete `RKTableau 1` witness with
  `c = 1/2, b = 1, A = 1/2`. The implicit midpoint method.
  Substantive non-vacuity: satisfies `B(2)`, `C(1)`, `D(1)`,
  `E(1, 1)` — verified by `simp + norm_num`.

**Tautology / Identity / Hypothesis-strength checks**: clean.

* No theorem conclusion equals a hypothesis verbatim.
* No proof is a bare `exact h` / `:= h_…`. The empty-case lemmas use
  `omega` (genuine arithmetic dispatch on the unsatisfiable premise).
  The monotonicity lemmas pass through a `Nat.le_trans` step inside
  the `fun … => h … (hk.trans hle)` thunk — the trans step *is* the
  mathematical work.
* Hypothesis strengths match the textbook. The empty-case lemmas have
  `M : RKTableau s` only (no extra premises). The monotonicity
  lemmas take `η' ≤ η` (the only mathematically necessary
  premise).

## Dead ends

* **`show … = 1 / (1 : ℝ)` definitional equality blockers**: the
  `interval_cases k` step substitutes `k = 1` in the predicate but
  leaves `↑1` (ℕ-to-ℝ cast) on the RHS, so `show … = 1 / (1 : ℝ)`
  does NOT reduce by `rfl`. Replaced the explicit `show` lines with
  bare `simp [<tableau-def>]`, which works because `simp` normalises
  the cast and reduces `Fin.sum_univ_one` automatically.
* **`SatisfiesD 1` / `SatisfiesE 1 1` for `gaussLegendre1Stage`
  needed `norm_num` after `simp`**: `simp` reduces the goal to a
  cleared-denominator arithmetic identity (`2 = 1 + 1`, etc.), and
  `norm_num` closes. Not a real dead end — just a two-tactic step
  rather than one.

## Discovery

* Cycle 305's `RKTableau` extension pattern (the `Section323.lean`
  file's `namespace OpenMath.Chapter3.Section312.RKTableau` block)
  is the right model for adding methods to `RKTableau` from
  downstream §32x files. Clean and namespace-correct. Followed
  uniformly here.
* `(0 : ℝ)^0 = 1` in Mathlib (via `Monoid.npow_zero`) — confirmed
  via `simp` reducing `explicitEuler.SatisfiesB 1` without any
  custom rewriting. Documented in the file docstring.
* `interval_cases k` after `intro k h1 hk` for `k : ℕ` with bounds
  `1 ≤ k ∧ k ≤ N` is the cleanest way to enumerate the (small)
  finite cases of B(N) / C(N) / D(N) / E(η, ζ). Should be reusable
  whenever a future cycle wants to verify a specific tableau against
  a small-index instance of these predicates.
* Substantive non-vacuity for `D(1)` / `E(1, 1)` requires an
  *implicit* tableau (`A ≠ 0`); explicit Euler fails both because
  `A = 0` makes the LHS zero while the RHS is generally nonzero.
  `gaussLegendre1Stage` is the minimal such witness.

## Suggested next approach

Cycle 307 should ship the **bridge from `lem:342B` to `B(2n)`**
(stretch goal carved out of cycle 306):

```lean
theorem butcherShiftedLegendre_quadratureWeights_satisfiesB (n : ℕ) :
    ∀ k : ℕ, 1 ≤ k → k ≤ 2 * n →
      (∑ i : Fin n, butcherShiftedLegendre_quadratureWeights n i *
            butcherShiftedLegendre_zeros n i ^ (k - 1))
        = 1 / (k : ℝ)
```

— i.e. the `B(2n)` condition holds for the canonical Lagrange weights
at the shifted-Legendre zeros. This is the substantive bridge between
§342 and the order-condition framework. Use cycle 305's
`butcherShiftedLegendre_quadratureWeights_*_exact` lemmas (degree-2n
exactness on Lagrange polynomials) as the engine.

After that, cycle 308+ can attempt the easier directions of
`thm:342C` — e.g. `G(2s) → B(2s)` or `B(2s) ∧ E(s, s) → C(s)` — but
this requires defining the `G(η)` predicate (RK method has order η)
in a clean B-series form, which is itself a single-cycle prerequisite.

The full §342 cluster (cor:342D + thm:344A) remains ~3–4 cycles out
from cycle 306.

## Notes on cycle 305 supervisor false-positives

Per the cycle 306 strategy §A and the standing remediation document
at `.prover-state/issues/tautology_scanner_false_positives.md`, the
`13 → 14` semantic-sorry-scanner deltas flagged by the cycle 305
supervisor are **false positives** of the well-known scanner
over-firing pattern. Cycle 305's deliverables are independently
verified axiom-clean. **No code changes attempted in cycle 306 to
"fix" the scanner false positives** — that is loop-maintainer
territory.
