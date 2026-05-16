import OpenMath.Chapter3.Section312
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Butcher §321 — Order-condition predicates `B(η)`, `C(ξ)`, `D(ζ)`, `E(η, ζ)`

This file formalises the four families of *simplifying assumptions* on
a Runge–Kutta tableau introduced by Butcher in §321 (3rd ed., pp.
171–175). They are the prerequisite infrastructure for §342's
Gaussian-quadrature order-conditions equivalence (`thm:342C`,
`cor:342D`) and for §344's Radau / Lobatto methods (`thm:344A`).

These predicates do not correspond to a single extracted entity in
`extraction/formalization_data/entities/` — they are reusable
infrastructure cited inside the statements of `thm:342C`, `cor:342D`,
`thm:343*`, `thm:344A`, etc. The textbook formulas they realise are
quoted below verbatim from Butcher §321.

## Textbook statements (Butcher §321, pp. 171–174)

`B(η)` — quadrature condition (Butcher §321 p. 171):

> The first of these conditions will be denoted by `B(η)`, and
> simply states that the conditions
>     `∑ᵢ bᵢ cᵢ^{k-1} = 1/k` hold for `k = 1, 2, …, η`.

`C(ξ)` — interpolation / collocation condition (Butcher §321 p. 173,
equation (321b)):

>     `∑ⱼ aᵢⱼ cⱼ^{k-1} = cᵢ^k / k`,    `i = 1, 2, …, s`,
> hold for `k = 1, 2, …`. Assuming that these hold for `1 ≤ k ≤ ξ`,
> we denote this collection of conditions by `C(ξ)`.

`D(ζ)` — adjoint condition (Butcher §321 p. 173). The text
introduces it via Figure 321(ii) and Table 321(II); at order `k = 1`
the condition is `∑ᵢ bᵢ aᵢⱼ = bⱼ (1 - cⱼ)`. The general form
(matching the table's `bᵢ cᵢ^{k-1} aᵢⱼ` left-hand factor versus
`bⱼ`, `bⱼ cⱼ^k` right-hand factors) is

>     `∑ᵢ bᵢ cᵢ^{k-1} aᵢⱼ = (bⱼ / k) (1 - cⱼ^k)`,    `j = 1, …, s`,
>     `k = 1, …, ζ`.

`E(η, ζ)` — pair condition (Butcher §321 p. 174, equation (321c)):

>     `∑ᵢ ∑ⱼ bᵢ cᵢ^{k-1} aᵢⱼ cⱼ^{l-1} = 1 / (l (k + l))`,
>     `k = 1, …, η`,    `l = 1, …, ζ`.

## Faithfulness notes

* For each predicate, the *primary* mathematical meaning is the
  quadrature/interpolation/adjoint identity literally written by
  Butcher. We are NOT defining any of B/C/D/E as "what makes the
  method order η+ζ" — that would be definition smuggling. The
  bridge from these predicates to method order is `thm:342C` and
  cousins (planned for cycle 308+).
* `D(ζ)` is implicit in Butcher's prose at §321 p. 173: he states
  the `k = 1` form (`∑ᵢ bᵢ aᵢⱼ = bⱼ (1 - cⱼ)` after rearrangement
  of the three trees in Figure 321(ii)) and indicates the general
  pattern via the figure. The k-indexed form
  `∑ᵢ bᵢ cᵢ^{k-1} aᵢⱼ = (bⱼ/k)(1 - cⱼ^k)` is the standard
  generalisation used uniformly in §342 (Hairer–Wanner I.7.5
  agrees).
* `E(η, ζ)` literally restates the order condition for the trees
  `[τ^{k-1} [τ^{l-1}]]`, per Butcher's "this simply expresses the
  fact that the order condition `Φ(t) = 1/γ(t)` is satisfied for
  trees `t = [τ^{k-1} [τ^{l-1}]]`".

## Vacuous lower bounds (`SatisfiesB 0`, `SatisfiesC 0`, etc.)

Each predicate quantifies over `1 ≤ k ≤ η` (and analogously). At
`η = 0` the range is empty, so every method vacuously satisfies the
predicate. These vacuous lemmas are tagged `@[simp]` to streamline
downstream proofs and to provide a universal non-vacuity witness for
the four predicates — a genuine non-vacuous witness on a concrete
1-stage method follows below for `B(1)` and `C(1)`.
-/

namespace OpenMath.Chapter3.Section312.RKTableau

/-- Butcher §321 `B(η)` quadrature condition.

`B(η)` holds for the tableau `M` iff the weights `b` and abscissae
`c` reproduce the integrals `∫₀¹ x^{k-1} dx = 1/k` exactly for every
power `1 ≤ k ≤ η`:
`∑ᵢ bᵢ cᵢ^{k-1} = 1/k`. -/
def SatisfiesB {s : ℕ} (M : RKTableau s) (η : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ η →
    (∑ i : Fin s, M.b i * M.c i ^ (k - 1)) = 1 / (k : ℝ)

/-- Butcher §321 `C(ξ)` interpolation/collocation condition (Butcher
equation (321b)).

`C(ξ)` holds for the tableau `M` iff for every stage `i` and every
power `1 ≤ k ≤ ξ`:
`∑ⱼ aᵢⱼ cⱼ^{k-1} = cᵢ^k / k`. -/
def SatisfiesC {s : ℕ} (M : RKTableau s) (ξ : ℕ) : Prop :=
  ∀ i : Fin s, ∀ k : ℕ, 1 ≤ k → k ≤ ξ →
    (∑ j : Fin s, M.A i j * M.c j ^ (k - 1)) = M.c i ^ k / (k : ℝ)

/-- Butcher §321 `D(ζ)` adjoint condition.

`D(ζ)` holds for the tableau `M` iff for every stage `j` and every
power `1 ≤ k ≤ ζ`:
`∑ᵢ bᵢ cᵢ^{k-1} aᵢⱼ = (bⱼ / k) (1 - cⱼ^k)`.

The `k = 1` case
`∑ᵢ bᵢ aᵢⱼ = bⱼ (1 - cⱼ)`
is the form Butcher writes explicitly for §322's order-4 derivation. -/
def SatisfiesD {s : ℕ} (M : RKTableau s) (ζ : ℕ) : Prop :=
  ∀ j : Fin s, ∀ k : ℕ, 1 ≤ k → k ≤ ζ →
    (∑ i : Fin s, M.b i * M.c i ^ (k - 1) * M.A i j)
      = (M.b j / (k : ℝ)) * (1 - M.c j ^ k)

/-- Butcher §321 `E(η, ζ)` pair condition (Butcher equation (321c)).

`E(η, ζ)` holds for the tableau `M` iff for all `1 ≤ k ≤ η` and
`1 ≤ l ≤ ζ`:
`∑ᵢ ∑ⱼ bᵢ cᵢ^{k-1} aᵢⱼ cⱼ^{l-1} = 1 / (l (k + l))`.

This is the order condition for the trees `[τ^{k-1} [τ^{l-1}]]`. -/
def SatisfiesE {s : ℕ} (M : RKTableau s) (η ζ : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ η →
  ∀ l : ℕ, 1 ≤ l → l ≤ ζ →
    (∑ i : Fin s, ∑ j : Fin s,
        M.b i * M.c i ^ (k - 1) * M.A i j * M.c j ^ (l - 1))
      = 1 / ((l : ℝ) * ((k : ℝ) + (l : ℝ)))

/- ### Empty-case lemmas

At `η = 0` the range `1 ≤ k ≤ 0` is empty, so every tableau
satisfies `B(0)` (and analogously `C(0)`, `D(0)`, `E(0, 0)`). These
are tagged `@[simp]` so that downstream proofs can discharge the
trivial base case automatically. -/

@[simp] theorem satisfiesB_zero {s : ℕ} (M : RKTableau s) :
    M.SatisfiesB 0 := by
  intro k h1 hk
  omega

@[simp] theorem satisfiesC_zero {s : ℕ} (M : RKTableau s) :
    M.SatisfiesC 0 := by
  intro _ k h1 hk
  omega

@[simp] theorem satisfiesD_zero {s : ℕ} (M : RKTableau s) :
    M.SatisfiesD 0 := by
  intro _ k h1 hk
  omega

@[simp] theorem satisfiesE_zero_zero {s : ℕ} (M : RKTableau s) :
    M.SatisfiesE 0 0 := by
  intro k h1 hk _ _ _
  omega

/- ### Monotonicity in the parameter

If `B(η)` holds, then so does `B(η')` for any `η' ≤ η`; similarly
for `C`, `D`. These are immediate from the definitions and are
recorded for downstream API stability — the `thm:342C` proof rephrases
B(2s)/C(s)/D(s) hypotheses at smaller indices. -/

theorem SatisfiesB.mono {s : ℕ} {M : RKTableau s} {η η' : ℕ}
    (h : M.SatisfiesB η) (hle : η' ≤ η) : M.SatisfiesB η' :=
  fun k h1 hk => h k h1 (hk.trans hle)

theorem SatisfiesC.mono {s : ℕ} {M : RKTableau s} {ξ ξ' : ℕ}
    (h : M.SatisfiesC ξ) (hle : ξ' ≤ ξ) : M.SatisfiesC ξ' :=
  fun i k h1 hk => h i k h1 (hk.trans hle)

theorem SatisfiesD.mono {s : ℕ} {M : RKTableau s} {ζ ζ' : ℕ}
    (h : M.SatisfiesD ζ) (hle : ζ' ≤ ζ) : M.SatisfiesD ζ' :=
  fun j k h1 hk => h j k h1 (hk.trans hle)

theorem SatisfiesE.mono {s : ℕ} {M : RKTableau s} {η η' ζ ζ' : ℕ}
    (h : M.SatisfiesE η ζ) (hη : η' ≤ η) (hζ : ζ' ≤ ζ) :
    M.SatisfiesE η' ζ' :=
  fun k h1 hk l hl1 hl => h k h1 (hk.trans hη) l hl1 (hl.trans hζ)

/-! ### Butcher §342 Theorem 342C, clause (342m) — `B(2s) ∧ C(s) ⇒ E(s, s)`

Butcher §342 (3rd ed., p. 238) states the seven-way equivalence
`thm:342C` between `G(2s)`, `B(2s)`, `C(s)`, `D(s)`, and `E(s, s)`.
Four of those clauses are *purely algebraic* in the B/C/D/E predicates
and require no elementary-differential / `G(2s)` machinery. Clause
(342m), shipped here, is the first such clause:

>     `B(2s) ∧ C(s) ⇒ E(s, s)`            (342m)

The proof is a two-step algebraic composition matching the cycle 312
specialisation `butcherGaussLegendreRK_satisfiesE`:

1. apply `C(s)` at exponent `l` per row `i` to reduce
   `∑ⱼ A i j · c j ^ (l - 1) = c i ^ l / l`;
2. factor `(1 / l)` out of the outer `i`-sum, combine the powers
   `c i ^ (k - 1) · c i ^ l = c i ^ (k + l - 1)`;
3. apply `B(2s)` at combined exponent `k + l` (legal since
   `1 ≤ k ≤ s` and `1 ≤ l ≤ s` give `1 ≤ k + l ≤ 2s`) to reduce
   the outer sum to `1 / (k + l)`;
4. close with `(1 / l) · (1 / (k + l)) = 1 / (l · (k + l))` via
   `field_simp`.

No `0 < s` hypothesis is required: at `s = 0`, the universally
quantified `∀ k, 1 ≤ k → k ≤ 0` is vacuous (closed by `omega`
inside the proof's `hkl_hi` step, which would derive `False`). -/
theorem satisfiesE_of_satisfiesB_satisfiesC {s : ℕ}
    (M : RKTableau s) (hB : M.SatisfiesB (2 * s))
    (hC : M.SatisfiesC s) :
    M.SatisfiesE s s := by
  intro k h1 hk l hl1 hl
  have hl_pos : 0 < (l : ℝ) := by exact_mod_cast hl1
  have hl_ne : (l : ℝ) ≠ 0 := ne_of_gt hl_pos
  -- Step 1: C(s) at exponent l, restated for downstream rewriting.
  have hCi : ∀ i : Fin s,
      (∑ j : Fin s, M.A i j * M.c j ^ (l - 1))
        = M.c i ^ l / (l : ℝ) :=
    fun i => hC i l hl1 hl
  -- Step 2: outer rewrite — factor i-only out of the inner j-sum,
  -- apply C(s), pull (1/l) out of the outer i-sum, combine powers.
  have h_outer :
      (∑ i : Fin s, ∑ j : Fin s,
        M.b i * M.c i ^ (k - 1) * M.A i j * M.c j ^ (l - 1))
      = (1 / (l : ℝ)) *
        ∑ i : Fin s, M.b i * M.c i ^ ((k + l) - 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (∑ j : Fin s,
              M.b i * M.c i ^ (k - 1) * M.A i j * M.c j ^ (l - 1))
            = M.b i * M.c i ^ (k - 1) *
              (∑ j : Fin s, M.A i j * M.c j ^ (l - 1)) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring]
    rw [hCi i]
    have hexp : (k - 1) + l = (k + l) - 1 := by omega
    rw [show M.c i ^ ((k + l) - 1)
          = M.c i ^ ((k - 1) + l) by rw [hexp]]
    rw [pow_add]
    field_simp
  rw [h_outer]
  -- Step 3: B(2s) at exponent k + l.
  have hkl_lo : 1 ≤ k + l := by omega
  have hkl_hi : k + l ≤ 2 * s := by omega
  have hB_eval :
      (∑ i : Fin s, M.b i * M.c i ^ ((k + l) - 1))
        = 1 / ((k + l : ℕ) : ℝ) :=
    hB (k + l) hkl_lo hkl_hi
  rw [hB_eval]
  -- Step 4: arithmetic closure (1/l) · (1/(k+l)) = 1 / (l · (k+l)).
  push_cast
  field_simp

/-! ### Butcher §342 Theorem 342C, clause (342o) — `B(2s) ∧ D(s) ⇒ E(s, s)`

Clause (342o) of the seven-way `thm:342C` equivalence (Butcher §342,
3rd ed., p. 238):

>     `B(2s) ∧ D(s) ⇒ E(s, s)`            (342o)

This is the partner of (342m) above: same conclusion `E(s, s)`,
same `B(2s)` half of the hypothesis, but routed through the adjoint
condition `D(s)` rather than the collocation condition `C(s)`. Like
(342m), the proof is purely algebraic in the §321 B/C/D/E predicates
and requires no elementary-differential infrastructure.

Proof recipe:

1. Sum-swap `∑ᵢ ∑ⱼ` → `∑ⱼ ∑ᵢ` via `Finset.sum_comm`.
2. Factor `c_j ^ (l - 1)` out of the inner `i`-sum (per column `j`).
3. Apply `D(s)` at exponent `k` per column `j` to reduce
   `∑ᵢ bᵢ cᵢ^{k-1} aᵢⱼ = (bⱼ / k)(1 - cⱼ^k)`.
4. Distribute `(1/k)` and split via `1 - cⱼ^k` to expose two `B(2s)`
   shapes: `bⱼ cⱼ^{l-1}` and `bⱼ cⱼ^{(k+l)-1}`.
5. Apply `B(2s)` at exponents `l` (legal: `1 ≤ l ≤ s ≤ 2s`) and
   `k + l` (legal: `1 ≤ k + l ≤ 2s`).
6. Close via `(1/k)(1/l - 1/(k+l)) = 1/(l(k+l))` with
   `field_simp + ring`.

No `0 < s` hypothesis is required: at `s = 0`, the universally
quantified `∀ k, 1 ≤ k → k ≤ 0` is vacuous. -/
theorem satisfiesE_of_satisfiesB_satisfiesD {s : ℕ}
    (M : RKTableau s) (hB : M.SatisfiesB (2 * s))
    (hD : M.SatisfiesD s) :
    M.SatisfiesE s s := by
  intro k h1 hk l hl1 hl
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast h1
  have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
  have hl_pos : 0 < (l : ℝ) := by exact_mod_cast hl1
  have hl_ne : (l : ℝ) ≠ 0 := ne_of_gt hl_pos
  -- Step 1: D(s) at exponent k, per column j.
  have hDj : ∀ j : Fin s,
      (∑ i : Fin s, M.b i * M.c i ^ (k - 1) * M.A i j)
        = (M.b j / (k : ℝ)) * (1 - M.c j ^ k) :=
    fun j => hD j k h1 hk
  -- Step 2: outer rewrite — sum-swap, factor c_j^(l-1) out per
  -- column, apply D(s), expand the (1 - c_j^k) split, distribute
  -- (1/k), and re-pack via `Finset.sum_sub_distrib`.
  have h_outer :
      (∑ i : Fin s, ∑ j : Fin s,
        M.b i * M.c i ^ (k - 1) * M.A i j * M.c j ^ (l - 1))
      = (1 / (k : ℝ)) *
        ((∑ j : Fin s, M.b j * M.c j ^ (l - 1))
          - ∑ j : Fin s, M.b j * M.c j ^ ((k + l) - 1)) := by
    rw [Finset.sum_comm]
    rw [show (∑ j : Fin s, ∑ i : Fin s,
              M.b i * M.c i ^ (k - 1) * M.A i j * M.c j ^ (l - 1))
            = ∑ j : Fin s, M.c j ^ (l - 1) *
              (∑ i : Fin s, M.b i * M.c i ^ (k - 1) * M.A i j) by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring]
    rw [show (∑ j : Fin s, M.c j ^ (l - 1) *
              (∑ i : Fin s, M.b i * M.c i ^ (k - 1) * M.A i j))
            = ∑ j : Fin s, M.c j ^ (l - 1) *
              ((M.b j / (k : ℝ)) * (1 - M.c j ^ k)) by
        apply Finset.sum_congr rfl
        intro j _
        rw [hDj j]]
    rw [show (∑ j : Fin s, M.c j ^ (l - 1) *
              ((M.b j / (k : ℝ)) * (1 - M.c j ^ k)))
            = (1 / (k : ℝ)) * ∑ j : Fin s,
              (M.b j * M.c j ^ (l - 1)
                - M.b j * M.c j ^ ((k + l) - 1)) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        have hexp : (l - 1) + k = (k + l) - 1 := by omega
        rw [show M.c j ^ ((k + l) - 1)
              = M.c j ^ ((l - 1) + k) by rw [hexp]]
        rw [pow_add]
        field_simp]
    rw [Finset.sum_sub_distrib]
  rw [h_outer]
  -- Step 3: B(2s) at exponents l and k + l.
  have hl_hi : l ≤ 2 * s := by omega
  have hkl_lo : 1 ≤ k + l := by omega
  have hkl_hi : k + l ≤ 2 * s := by omega
  have hB_l : (∑ j : Fin s, M.b j * M.c j ^ (l - 1))
                = 1 / ((l : ℕ) : ℝ) :=
    hB l hl1 hl_hi
  have hB_kl :
      (∑ j : Fin s, M.b j * M.c j ^ ((k + l) - 1))
        = 1 / ((k + l : ℕ) : ℝ) :=
    hB (k + l) hkl_lo hkl_hi
  rw [hB_l, hB_kl]
  -- Step 4: arithmetic closure (1/k)(1/l - 1/(k+l)) = 1/(l(k+l)).
  push_cast
  have hkl_real_ne : (k : ℝ) + (l : ℝ) ≠ 0 := by positivity
  field_simp
  ring

end OpenMath.Chapter3.Section312.RKTableau

namespace OpenMath.Chapter3.Section321

open OpenMath.Chapter3.Section312

/- ### Non-vacuity witnesses on `explicitEuler`

The 1-stage explicit Euler tableau (`A = 0`, `b = 1`, `c = 0`)
satisfies the lowest non-trivial instance of `B` and `C`:

* `B(1)`: `∑ᵢ bᵢ cᵢ^0 = b₀ · c₀^0 = 1 · 0^0 = 1` (using `(0 : ℝ)^0 = 1`
  in Mathlib's `Monoid.npow_zero`). RHS = `1/1 = 1`. ✓
* `C(1)`: for `i = 0`, `∑ⱼ A 0 j · cⱼ^0 = 0 · 0^0 = 0`. RHS =
  `c₀^1 / 1 = 0`. ✓

Note: `D(1)` and `E(1,1)` *fail* on explicit Euler — see the strategy
file for cycle 306, §C.2. The substantive non-vacuity witnesses for
`D(1)` / `E(1,1)` are the implicit-midpoint (Gauss–Legendre 1-stage)
method, deferred to cycle 307. The vacuous `D(0)`, `E(0, 0)` examples
below confirm that the predicates are non-empty as `Prop`-valued
predicates. -/

example : RKTableau.explicitEuler.SatisfiesB 1 := by
  intro k h1 hk
  interval_cases k
  simp [RKTableau.explicitEuler]

example : RKTableau.explicitEuler.SatisfiesC 1 := by
  intro i k h1 hk
  interval_cases k
  simp [RKTableau.explicitEuler]

example : RKTableau.explicitEuler.SatisfiesD 0 :=
  RKTableau.satisfiesD_zero _

example : RKTableau.explicitEuler.SatisfiesE 0 0 :=
  RKTableau.satisfiesE_zero_zero _

/- ### Substantive non-vacuity witness — the 1-stage Gauss–Legendre /
implicit midpoint method

The implicit-midpoint method has tableau `c = 1/2`, `b = 1`,
`A = 1/2`. We verify it satisfies `B(2)`, `C(1)`, `D(1)`, `E(1, 1)`
— the order conditions for an order-2 method.

* `B(1)`: `1 · (1/2)^0 = 1 = 1/1`. ✓
* `B(2)`: `1 · (1/2)^1 = 1/2 = 1/2`. ✓
* `C(1)`: `(1/2) · (1/2)^0 = 1/2 = (1/2)^1 / 1`. ✓
* `D(1)`: `1 · (1/2)^0 · (1/2) = 1/2 = (1/1) · (1 - 1/2)`. ✓
* `E(1, 1)`: `1 · (1/2)^0 · (1/2) · (1/2)^0 = 1/2 = 1 / (1 · (1+1))`. ✓
-/

/-- The 1-stage implicit-midpoint / Gauss–Legendre method as an
`RKTableau 1`. Marked `noncomputable` because `1/2 : ℝ` uses
`Real.instDivInvMonoid`. -/
noncomputable def gaussLegendre1Stage : RKTableau 1 where
  A := fun _ _ => 1 / 2
  b := fun _ => 1
  c := fun _ => 1 / 2

example : gaussLegendre1Stage.SatisfiesB 2 := by
  intro k h1 hk
  interval_cases k
  · simp [gaussLegendre1Stage]
  · simp [gaussLegendre1Stage]

example : gaussLegendre1Stage.SatisfiesC 1 := by
  intro i k h1 hk
  interval_cases k
  simp [gaussLegendre1Stage]

example : gaussLegendre1Stage.SatisfiesD 1 := by
  intro j k h1 hk
  interval_cases k
  simp [gaussLegendre1Stage]
  norm_num

example : gaussLegendre1Stage.SatisfiesE 1 1 := by
  intro k h1 hk l hl1 hl
  interval_cases k
  interval_cases l
  simp [gaussLegendre1Stage]
  norm_num

/-- *Non-vacuity for the abstract (342m) clause via `gaussLegendre1Stage`.*
The implicit-midpoint tableau satisfies `B(2)` and `C(1)` (existing
witnesses immediately above), so the abstract bridge
`RKTableau.satisfiesE_of_satisfiesB_satisfiesC` yields `E(1, 1)`.
This is the *abstract-route* counterpart to the hand-built
`gaussLegendre1Stage.SatisfiesE 1 1` example above and confirms the
new theorem (342m) is non-vacuous at the smallest stage count. -/
example : gaussLegendre1Stage.SatisfiesE 1 1 :=
  gaussLegendre1Stage.satisfiesE_of_satisfiesB_satisfiesC
    (hB := by
      intro k h1 hk
      interval_cases k
      · simp [gaussLegendre1Stage]
      · simp [gaussLegendre1Stage])
    (hC := by
      intro i k h1 hk
      interval_cases k
      simp [gaussLegendre1Stage])

/-- *Non-vacuity for the abstract (342o) clause via `gaussLegendre1Stage`.*
The implicit-midpoint tableau satisfies `B(2)` and `D(1)` (existing
witnesses above), so the abstract bridge
`RKTableau.satisfiesE_of_satisfiesB_satisfiesD` yields `E(1, 1)`.
This is the *abstract-route* counterpart to the hand-built
`gaussLegendre1Stage.SatisfiesE 1 1` example above and confirms the
new theorem (342o) is non-vacuous at the smallest stage count. -/
example : gaussLegendre1Stage.SatisfiesE 1 1 :=
  gaussLegendre1Stage.satisfiesE_of_satisfiesB_satisfiesD
    (hB := by
      intro k h1 hk
      interval_cases k
      · simp [gaussLegendre1Stage]
      · simp [gaussLegendre1Stage])
    (hD := by
      intro j k h1 hk
      interval_cases k
      simp [gaussLegendre1Stage]
      norm_num)

end OpenMath.Chapter3.Section321
