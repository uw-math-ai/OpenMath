# Cycle 304 Results

## Worked on

Phase B.1 of `lem:342B` (Gaussian quadrature exactness degree, Butcher
§342 p. 237 (342h) — the headline `2n`-degree exactness). Two new
theorems in `OpenMath/Chapter3/Section342.lean`:

* **D1** — `butcherShiftedLegendre_quadrature_exact_lt_two_n (n : ℕ) (hn : 0 < n) (φ : Polynomial ℝ) (hdeg : φ.natDegree < 2 * n) : ∫₀¹ φ.eval x dx = ∑ⱼ bⱼ · φ(cⱼ)`
  — the headline of `lem:342B` (existence half: Gaussian quadrature on
  the shifted Legendre nodes is exact on polynomials of degree `< 2n`).
* **D2** (P2 stretch) — `butcherShiftedLegendre_quadratureWeights_sum_eq_one (n : ℕ) (hn : 0 < n) : ∑ⱼ bⱼ = 1`
  — consistency witness derived by applying Phase A.2's exactness to
  the constant polynomial `1`. Confirms the quadrature reproduces
  `∫₀¹ 1 dx = 1` and the weights sum to the interval length.

File now 6418 LOC; cycle 304 added ~130 LOC.

## Approach

**Strategy doc's "Option A — EuclideanDomain general" worked first
try (after one rewrite-form correction).** The Mathlib hooks that
fired:

| Concept | Mathlib name | Note |
|---|---|---|
| Polynomial division `Pn * Q + R = φ` | `EuclideanDomain.div_add_mod` | works for `Polynomial ℝ` (Euclidean domain over a field) |
| `(φ % Pn).degree < Pn.degree` for `Pn ≠ 0` | `Polynomial.degree_mod_lt` | field-specific, ℝ qualifies |
| `degree ↔ natDegree` conversion for non-zero | `Polynomial.degree_eq_natDegree` | cycle 303 used it |
| `(p * q).natDegree = p.natDegree + q.natDegree` over integral domain | `Polynomial.natDegree_mul` | cycle 290 also used this |
| Leading-term domination `R.natDegree < (Pn*Q).natDegree ⇒ (R + Pn*Q).natDegree = (Pn*Q).natDegree` | `Polynomial.natDegree_add_eq_right_of_natDegree_lt` | cleaner than `Polynomial.degree_add_eq_right_of_degree_lt` for the `Q.natDegree < n` bookkeeping |
| Integral additivity | `intervalIntegral.integral_add` | exact application via `:=` (not `rw`) sidesteps higher-order unification on the integrand |
| Integral congruence | `intervalIntegral.integral_congr` | bridges `φ.eval x = (Pn*Q + R).eval x` after pointwise unfolding |
| `∫ x in a..b, c = (b−a) • c` | `intervalIntegral.integral_const` | for the P2 stretch: `∫₀¹ 1 = 1` via `smul_eq_mul` + `sub_zero` |

The proof structure follows the textbook recipe verbatim — split, kill
orthogonality, apply A.2 to remainder, identify `R(cⱼ) = φ(cⱼ)`. The
`Q.natDegree < n` bookkeeping was the load-bearing step beyond the
straight A.2 path: argued by observing that since
`R.natDegree < n ≤ n + Q.natDegree = (Pn*Q).natDegree`, the leading
term of `φ = Pn*Q + R` is the leading term of `Pn*Q`, so
`φ.natDegree = n + Q.natDegree`. Combined with `φ.natDegree < 2n`,
`omega` closes `Q.natDegree < n`.

## Result

**SUCCESS** — D1 and D2 axiom-clean
(`[propext, Classical.choice, Quot.sound]` only), full
`Section342.lean` compiles, 0 sorries. Health-check audit at cycle
start passed (HEAD = `d4b3d5d`, file compiled, sorry-free,
cycle 303's Phase A.2 lemmas axiom-clean).

## Faithfulness check

* **D1: `butcherShiftedLegendre_quadrature_exact_lt_two_n`**
  Entity ID: `lem:342B` (Butcher §342 p. 237).
  > "Let c₁, c₂, …, cₛ denote the zeros of Pₛ*. Then there exist
  > positive numbers b₁, b₂, …, bₛ such that ∫₀¹ φ(x) dx = ∑ᵢ bᵢ φ(cᵢ),
  > for any polynomial of degree less than 2s. The bᵢ are unique."

  Lean statement captures: **the existence + degree clause** of
  `lem:342B`. Specifically: at our shipped `bⱼ` (the canonical Lagrange
  weights from Phase A.2), the quadrature is exact on degree `< 2n`.
  **Still partial** because positivity (`0 < bⱼ`) and uniqueness are
  separate clauses. The textbook proof's `2n`-degree extension recipe
  is faithfully encoded:

  | Textbook step | Lean realization |
  |---|---|
  | "write `φ(x) = Pₛ*(x) Q(x) + R(x)`, where the quotient `Q` and the remainder `R` have degrees not exceeding `s − 1`" | `EuclideanDomain.div_add_mod φ Pn : Pn * (φ/Pn) + φ%Pn = φ` + the two degree bounds `hQ_lt : Q.natDegree < n`, `hR_lt : R.natDegree < n` |
  | "`∫₀¹ Pₛ*(x) Q(x) dx = 0`" | `butcherShiftedLegendre_orthogonal_to_lower_degree n Q hQ_lt` (cycle 292) |
  | "`∫₀¹ R(x) dx = ∑ᵢ bᵢ R(cᵢ)`" | `butcherShiftedLegendre_quadrature_exact_lt_n n R hR_lt` (cycle 303) |
  | "`∑ᵢ bᵢ R(cᵢ) = ∑ᵢ bᵢ φ(cᵢ)`" because `Pₛ*(cⱼ) = 0` | `Finset.sum_congr rfl` + `butcherShiftedLegendre_zeros_isRoot n j` (cycle 302) + algebraic collapse |

  Hypothesis `hn : 0 < n` is required because the empty-quadrature case
  (`n = 0`, i.e. summing over `Fin 0 = ∅`) would force `φ ≡ 0` for the
  identity to hold, and Butcher implicitly assumes `s ≥ 1` (one cannot
  have zeros of `P₀* = 1`). This is **not** a strengthening of the
  textbook hypothesis — it is the natural domain of the statement.

* **D2 (consistency witness): `butcherShiftedLegendre_quadratureWeights_sum_eq_one`**
  Not a textbook-named entity. Sanity check that the quadrature
  reproduces `∫₀¹ 1 dx = 1` — i.e. the weights sum to the interval
  length. Direct consequence of Phase A.2's `< n` exactness applied to
  `φ = 1`; *not* dependent on Phase B.1 (so it would ship even if B.1
  had stalled). Useful as a future-cycle anchor for the Runge–Kutta
  consistency conditions in `cor:342D`.

* **Tautology / Identity / Hypothesis-strength checks**: D1's
  hypothesis `hdeg : φ.natDegree < 2 * n` is exactly the textbook
  hypothesis ("polynomial of degree less than 2s"), no strengthening.
  D1's conclusion does not appear as a hypothesis. The proof is **not**
  a single `exact h` — it composes polynomial division
  (`EuclideanDomain.div_add_mod`), degree bookkeeping
  (`Polynomial.degree_mod_lt` + `Polynomial.natDegree_mul` +
  `Polynomial.natDegree_add_eq_right_of_natDegree_lt`), integral
  linearity (`intervalIntegral.integral_add`,
  `intervalIntegral.integral_congr`), and three cycle 292/302/303
  domain-specific lemmas. D1 is doing real mathematical work
  (encoding the textbook polynomial-division argument).

## Dead ends

**False start #1**: Initial proof used `rw [intervalIntegral.integral_add ...]`
inside a `conv_lhs`/`simp_rw` chain. Failed with "rewrite failed: Did
not find an occurrence of the pattern" because Lean's higher-order
unification couldn't match `f x + g x` against the integrand
`(Pn).eval x * Q.eval x + R.eval x` when the integrand had been built
up via `simp_rw [Polynomial.eval_add, Polynomial.eval_mul]`. Fix:
switch to `calc` block with `exact intervalIntegral.integral_add ...`
in term mode (no `rw`), which lets Lean unify the conclusion shape
directly with the calc step's target. Cleaner overall.

**False start #2**: P2 stretch used `intervalIntegral.integral_one`
(non-existent). Fixed to `intervalIntegral.integral_const` +
`smul_eq_mul` + `sub_zero` chain.

Both fixes were trivial. No genuine dead ends.

## Discovery

* **`Polynomial.degree_mod_lt` works over fields, no monicness
  required.** The strategy's Option B (monic normalisation) was
  unnecessary — Option A (EuclideanDomain.div_add_mod +
  Polynomial.degree_mod_lt) closed without any leading-coefficient
  scaling. ℝ being a field means `Polynomial ℝ` is a Euclidean domain
  with the obvious `%` and `/` operations.
* **`calc` blocks beat `rw`/`simp_rw` chains for integral arithmetic.**
  When the integrand has higher-order structure (e.g.
  `f x + g x`-shape), `rw [intervalIntegral.integral_add ...]` fails
  on HO unification. Switching to a `calc` block with each step's
  conclusion type pinned forces Lean to unify the goal first, then
  match the lemma — this works robustly. Pattern: for any integral-
  splitting argument, prefer `_ = ... := intervalIntegral.integral_add hf hg`
  over `rw [intervalIntegral.integral_add ...]`.
* **Aristotle was not used this cycle** — the recipe was concrete and
  the Mathlib hooks were well-established (all six load-bearing names
  hit on first try). Consistent with strategy §J directive ("Do NOT
  submit Phase B.1 to Aristotle. Manual closure is faster than a poll
  cycle.").

## Suggested next approach

**Cycle 305: Phase B.2 of `lem:342B`** — positivity of weights
(`0 < bⱼ`). Recipe per Butcher §342 p. 237:

> "To prove the bᵢ are positive, let φ(x) denote the square of the
> polynomial formed by dividing Pₛ*(x) by x − cᵢ. Substitute into
> (342h), and the result follows."

Concrete plan:

1. Define `butcherShiftedLegendre_div_X_sub_zero (n : ℕ) (j : Fin n) : Polynomial ℝ := P_n^* /ₘ (X - C (c_j))`
   via `Polynomial.divByMonic` on the monic `X - C c_j`. This is the
   polynomial of degree `n - 1` that vanishes at every `cₖ` for `k ≠ j`
   but not at `cⱼ` (since `cⱼ` is a simple root of `Pₙ*`).
2. Set `φⱼ := (P_n^* /ₘ (X - C c_j))^2`, which has `natDegree = 2(n-1) < 2n`
   when `n ≥ 1`. So Phase B.1's `butcherShiftedLegendre_quadrature_exact_lt_two_n`
   applies.
3. LHS: `∫₀¹ φⱼ(x) dx > 0` because `φⱼ` is a non-zero non-negative
   continuous polynomial on a non-degenerate interval. Hook:
   `MeasureTheory.integral_pos_iff_support_of_nonneg`
   or similar; possibly need to argue
   non-vanishing at some specific point in `(0, 1)`.
4. RHS: `∑ₖ bₖ · φⱼ(cₖ) = bⱼ · φⱼ(cⱼ)` because `φⱼ(cₖ) = 0` for
   `k ≠ j` (the `(X - C cₖ)` factor in `P_n^*` vanishes at `cₖ`) and
   `φⱼ(cⱼ) > 0` (it's a non-zero square — specifically, the leading-
   coefficient consideration shows `Pₙ* /ₘ (X - C cⱼ)` evaluated at
   `cⱼ` is the formal derivative `Pₙ*'(cⱼ)`, which is non-zero since
   `cⱼ` is a simple root).
5. Conclude `bⱼ = LHS / φⱼ(cⱼ) > 0`.

Estimated 150–200 LOC. The hardest sub-step is likely step 4 — proving
`Pₙ* /ₘ (X - C cⱼ)).eval cⱼ ≠ 0`. Mathlib hook candidates:
`Polynomial.eval_divByMonic_X_sub_C`,
`Polynomial.derivative_root_simple_ne_zero`, or analogous.

**Cycle 306: Phase B.3** — uniqueness of weights. ~50 LOC. Two
quadrature rules `b, b'` both exact on degree `< n` polynomials agree
on each Lagrange basis polynomial `Lⱼ` (since `Lⱼ(cₖ) = δⱼₖ`), so
`bⱼ = b'ⱼ`. Standalone — depends only on Phase A.2, not B.1 or B.2.

After B.3, `lem:342B` row flips to `formalized`.

**LOC note**: file now 6418 LOC. Per strategy §F, evaluate extraction
to `Section342Quadrature.lean` after B.2 ships. If past 6500 LOC AND
compile time exceeds 90s on NVMe, plan extraction for cycle 306. Don't
preemptively extract.
