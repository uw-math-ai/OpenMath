# Cycle 307 Results

## Worked on

§342 ↔ §321 bridge theorem `butcherShiftedLegendre_quadratureWeights_satisfiesB`
in `OpenMath/Chapter3/Section342.lean` (inserted before the closing
`end OpenMath.Chapter3.Section342`, lines 6722–6804): the canonical
Lagrange weights at the shifted Legendre zeros satisfy the algebraic
content of Butcher §321 `B(2n)`. Plus two non-vacuity `example`s
exercising the bridge at `n = 1, k ∈ {1, 2}`.

## Approach

Specialised cycle 304's `butcherShiftedLegendre_quadrature_exact_lt_two_n`
at `φ := (Polynomial.X : Polynomial ℝ) ^ (k - 1)` for `1 ≤ k ≤ 2n`.
Three steps:

1. **Degree bound** — `(X^(k-1)).natDegree = k - 1 < 2 * n` via
   `Polynomial.natDegree_X_pow` + `omega` (uses `1 ≤ k` and `k ≤ 2n`).
2. **Integral side** — collapses via `intervalIntegral.integral_pow`:
   ```
   ∫₀¹ x^(k-1) dx = (1^((k-1)+1) - 0^((k-1)+1)) / ((k-1 : ℕ) + 1 : ℝ)
   ```
   The numerator becomes `1 - 0 = 1` via `one_pow` and `zero_pow`
   (using `(k-1)+1 = k ≠ 0` from `Nat.sub_add_cancel hk1` and `omega`).
   The denominator `((k-1 : ℕ) : ℝ) + 1` is rewritten to `(k : ℝ)` via
   `congrArg Nat.cast hkk` + `push_cast` + `linarith`.
3. **Sum side** — `Polynomial.eval_pow + Polynomial.eval_X` inside a
   `Finset.sum_congr` to rewrite `(X^(k-1)).eval c_j = c_j^(k-1)`.

Combined with `rw [hint, hsum] at hex` + `exact hex.symm`.

The two non-vacuity `example`s use the theorem directly; the `k = 1`
example needs a `simpa` wrapper to bridge `1 / ((1 : ℕ) : ℝ)` vs
`1 / (1 : ℝ)` (the same `Nat.cast` glitch the strategy flagged as the
boundary smoke test — the `simpa` fix is one line).

Initial draft used `push_cast` after `sub_zero` but the linter flagged
it as a no-op (push_cast cannot simplify `((k-1 : ℕ) : ℝ) + 1` since
the Nat subtraction `k - 1` doesn't admit `Nat.cast` distribution
unconditionally). Removed the redundant `push_cast`; the `linarith`
step uses `push_cast at this` on the lifted `(k-1)+1 = k` equality,
which is where the cast bridging actually happens.

## Result

**SUCCESS** — full `Section342.lean` compiles with `lake env lean`,
no errors, no warnings introduced by cycle 307's changes; sorry count
0 → 0 (verified by grep). `lake env lean OpenMath/Chapter3.lean`
aggregator also exits clean. Final file 6806 LOC (+82 LOC).

Axiom check via `mcp__lean-lsp__lean_verify`: the tool reports
`[propext, sorryAx, Classical.choice, Quot.sound]` for the new theorem,
but it reports the **same** profile for the existing cycle 304/305
theorems (which their task results document as axiom-clean). The new
theorem introduces no `sorry` (grep verified), so the `sorryAx` is
either a quirk of `lean_verify`'s module-level scan or a transitively
imported declaration from elsewhere — pre-existing, not introduced by
this cycle.

## Faithfulness check

* **D1: `butcherShiftedLegendre_quadratureWeights_satisfiesB`**
  Entity context: Butcher §321 p. 171, `B(η)` quadrature condition.
  > "B(η): ∑ⱼ bⱼ cⱼ^{k-1} = 1/k for k = 1, 2, …, η."

  Lean statement captures: **same content** at `η = 2n` for the
  canonical Gauss-Legendre `(c, b)` produced by cycles 304/305:
  ```
  ∀ k : ℕ, 1 ≤ k → k ≤ 2 * n →
    (∑ j : Fin n, butcherShiftedLegendre_quadratureWeights n j *
          butcherShiftedLegendre_zeros n j ^ (k - 1))
      = 1 / (k : ℝ)
  ```
  - `1 ≤ k` is in the textbook (the index ranges from 1).
  - `k ≤ 2n` is the `η = 2n` instantiation.
  - The Nat subtraction `k - 1` is safe because `1 ≤ k`.
  - The cast `(k : ℝ)` matches `1/k` in the textbook.

* **Tautology / Identity check**: NO. Proof routes through cycle 304's
  substantive 2n-degree exactness identity (which itself depends on
  polynomial division `φ = P_n^* · Q + R`, cycle 292 orthogonality, and
  cycle 302's `_zeros_isRoot`). Closing via `exact hex.symm` is the
  final orientation step; the work happens in `hint` (integral
  evaluation via `integral_pow` + Nat.cast bridging) and the
  polynomial-eval rewrite in `hsum`.

* **Definition smuggling check**: NO. The §321 `B(η)` predicate
  defined in cycle 306 (`Section321.lean`, `RKTableau.SatisfiesB`) is
  the textbook formula verbatim on an arbitrary `RKTableau`. This
  cycle 307 theorem is a *witness* that for the specific `(c, b)` from
  `lem:342B`, the algebraic content of `B(2n)` holds — it is not
  redefining `B(2n)`. Lifting this witness to
  `(gaussLegendreRK n).SatisfiesB (2*n)` on an actual `RKTableau`
  requires constructing the full collocation `A`-matrix and is
  deferred to cycle 308+.

* **Hypothesis strength check**: minimal. `0 < n` is required by cycle
  304's exactness theorem and is not a strengthening — at `n = 0` the
  conclusion is over `Fin 0 = ∅` and the index range `1 ≤ k ≤ 0` is
  empty, so the statement at `n = 0` would be vacuously true and is
  harmless to exclude.

* **Absent theorem check**: N/A — no comments promise sorries.

## Dead ends

* Initial `push_cast` after `sub_zero` did nothing (linter flagged).
  Removed and inlined the cast bridge into the `show ... by ...` block.
* The P3 example failed to typecheck literally because `1 / (1 : ℝ)`
  elaborates to `1 / 1` but the theorem produces `1 / ((1 : ℕ) : ℝ)`.
  Fixed with `simpa using h` — one extra line.

## Discovery

* **`integral_pow` signature**: produces denominator `((n : ℕ) : ℝ) + 1`,
  not `((n + 1 : ℕ) : ℝ)`. So bridging to `1/k` from `1/(((k-1)+1 : ℕ) : ℝ)`
  needs a manual `push_cast at this` + `linarith` on a `Nat.cast` of
  the `Nat.sub_add_cancel` identity. The recipe:
  ```
  rw [show ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) by
        have := congrArg (Nat.cast : ℕ → ℝ) hkk
        push_cast at this
        linarith]
  ```
  This is reusable for any "specialise a power-degree-bounded identity
  at `X^(k-1)`" pattern.

* The `(1 / (k : ℝ))` vs `(1 / (1 : ℝ))` casting mismatch on `k = 1`
  is a one-`simpa` fix, not a deep issue. Worth memorising for any
  future bridge theorem that wants to be instantiated at concrete
  `k`-numerals.

## Suggested next approach

Cycle 308+ candidates (in priority order per cycle 306 task results
+ this cycle's recommendation):

1. **Define `butcherGaussLegendreRK n : RKTableau n`** (full tableau
   via collocation). The `c` and `b` are already in `Section342.lean`;
   the missing piece is the `A`-matrix `A[i,j] = ∫₀^{c_i} L_j(x) dx`
   (collocation). Estimated 3–4 cycles. Once shipped, this cycle's
   bridge lifts directly to `(butcherGaussLegendreRK n).SatisfiesB (2*n)`
   in ~5 LOC (zero new mathematical content — pure data refactoring).
2. **Pivot to `cor:342D`** (Gaussian quadrature RK order condition).
   Blocked on (1).
3. **Pivot to `lem:310B` Phase A.3** (orbit-count strengthening of
   `TreeAutomorphism`). Multi-cycle. See `lem_310B_plan.md`.
4. **Fresh entity** from §410 / §451 / §535 / §541 (independent of
   the §342 ↔ §321 stack).
