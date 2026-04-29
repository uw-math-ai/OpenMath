import Mathlib

/-!
# Butcher §404 — Preconsistency and consistency of linear multistep methods

This file opens Chapter 4 of the formalization. It introduces the
`LinearMultistepMethod` structure (with the textbook normalisation
`α₀ = -1`), the `IsPreconsistent` predicate (Butcher equation (404a),
Definition 404A), and the `IsConsistent` predicate (combining (404a)
with the consistency equation (404b), Definition 404B).

## Textbook statements (quoted from `entities/def_404A.json` and `entities/def_404B.json`)

> A linear multistep method satisfying (404a) is said to be
> 'preconsistent'.
>
> A linear multistep method satisfying (404a) and (404b) is said to be
> 'consistent'.

with the section-context equations

> (404a)  `1 = α₁ + α₂ + … + α_k`
> (404b)  `α₁ + 2α₂ + … + kα_k = β₀ + β₁ + … + β_k`.

The recurrence (Butcher §404, p. 341, equation defining the method
itself) is

  Σ_{i=0}^{k} α_i · y_{n-i} = h · Σ_{i=0}^{k} β_i · f(x_{n-i}, y_{n-i})

with `α₀ = -1`. We capture only the coefficient data and the
preconsistency predicate here; the integration-by-recurrence operator
will be added when downstream entities (e.g. `def:402A`, `def:406A`)
need it.
-/

namespace OpenMath.Chapter4.Section404

/-- A `k`-step linear multistep method (Butcher §404, p. 341).

The coefficients `α : Fin (k+1) → ℝ` and `β : Fin (k+1) → ℝ` define the
recurrence

  `Σᵢ αᵢ · y_{n-i} = h · Σᵢ βᵢ · f(x_{n-i}, y_{n-i})`,

with the textbook leading-coefficient normalisation `α 0 = -1`.

`α_zero` is a *hypothesis* (the textbook normalisation convention), not
a derived fact: every concrete LMM must supply it. -/
structure LinearMultistepMethod (k : ℕ) where
  α : Fin (k + 1) → ℝ
  β : Fin (k + 1) → ℝ
  α_zero : α 0 = -1

/-- Butcher (404a): a linear multistep method is *preconsistent* if

  `1 = α₁ + α₂ + … + α_k`.

The sum runs from `i = 1` to `i = k`; we encode this by iterating over
`Fin k` and using `i.succ : Fin (k+1)` to skip the `α 0` slot.

This is Butcher's definition of preconsistency verbatim — equation
(404a) is the *defining* condition (the textbook says "a linear
multistep method satisfying (404a) is said to be preconsistent"), so
the predicate matches the textbook one-to-one. -/
def LinearMultistepMethod.IsPreconsistent {k : ℕ}
    (M : LinearMultistepMethod k) : Prop :=
  1 = ∑ i : Fin k, M.α i.succ

/-! ### Non-vacuity witness — explicit Euler as a 1-step LMM

Explicit Euler is `y_n - y_{n-1} = h · f(x_{n-1}, y_{n-1})`, i.e.
`α 0 = -1, α 1 = 1, β 0 = 0, β 1 = 1`. The preconsistency condition
reduces to `1 = α 1 = 1`. -/

/-- Explicit Euler as a 1-step linear multistep method:
`y_n - y_{n-1} = h · f(x_{n-1}, y_{n-1})`. -/
def explicitEulerLMM : LinearMultistepMethod 1 where
  α := fun i => if i = 0 then -1 else 1
  β := fun i => if i = 0 then 0 else 1
  α_zero := by simp

/-- Explicit Euler is preconsistent. -/
theorem explicitEulerLMM_isPreconsistent :
    explicitEulerLMM.IsPreconsistent := by
  simp [LinearMultistepMethod.IsPreconsistent, explicitEulerLMM]

/-! ### Second witness — implicit Euler as a 1-step LMM

Implicit Euler is `y_n - y_{n-1} = h · f(x_n, y_n)`, i.e.
`α 0 = -1, α 1 = 1, β 0 = 1, β 1 = 0`. Same preconsistency proof
shape — provides evidence the predicate is meaningful for both
explicit and implicit methods. -/

/-- Implicit Euler as a 1-step linear multistep method:
`y_n - y_{n-1} = h · f(x_n, y_n)`. -/
def implicitEulerLMM : LinearMultistepMethod 1 where
  α := fun i => if i = 0 then -1 else 1
  β := fun i => if i = 0 then 1 else 0
  α_zero := by simp

/-- Implicit Euler is preconsistent. -/
theorem implicitEulerLMM_isPreconsistent :
    implicitEulerLMM.IsPreconsistent := by
  simp [LinearMultistepMethod.IsPreconsistent, implicitEulerLMM]

/-! ### Consistency (Definition 404B)

Butcher §404, p. 342: a linear multistep method is *consistent* if it
satisfies both (404a) (preconsistency) and (404b)

  `α₁ + 2α₂ + … + kα_k = β₀ + β₁ + … + β_k`. -/

/-- Butcher (404b): the equation
`α₁ + 2α₂ + … + kα_k = β₀ + β₁ + … + β_k`.

This is the second of the two consistency conditions. The α-sum runs
over `i = 1 .. k` with coefficient `i`; we encode the textbook subscript
via `((i : ℕ) + 1)` and select `M.α i.succ` to skip the `α 0` slot. The
β-sum runs over all of `Fin (k+1)` since β indexing starts at 0. -/
def LinearMultistepMethod.SatisfiesEq404b {k : ℕ}
    (M : LinearMultistepMethod k) : Prop :=
  (∑ i : Fin k, ((i : ℕ) + 1 : ℝ) * M.α i.succ) = ∑ i, M.β i

/-- Butcher Definition 404B: a linear multistep method is *consistent*
if it satisfies both the preconsistency condition (404a) and the
consistency condition (404b).

The textbook says "a linear multistep method satisfying (404a) and
(404b) is said to be 'consistent'", so we encode this as the
conjunction of the two conditions, faithful to the textbook one-to-one. -/
def LinearMultistepMethod.IsConsistent {k : ℕ}
    (M : LinearMultistepMethod k) : Prop :=
  M.IsPreconsistent ∧ M.SatisfiesEq404b

/-! ### Witnesses for consistency

Both Euler methods (k=1, α=(-1,1)) satisfy (404b):
- `explicitEulerLMM`: LHS = `1 · 1 = 1`, RHS = `0 + 1 = 1`. ✓
- `implicitEulerLMM`: LHS = `1 · 1 = 1`, RHS = `1 + 0 = 1`. ✓ -/

/-- Explicit Euler satisfies (404b). -/
theorem explicitEulerLMM_satisfiesEq404b :
    explicitEulerLMM.SatisfiesEq404b := by
  simp [LinearMultistepMethod.SatisfiesEq404b, explicitEulerLMM]

/-- Explicit Euler is consistent. -/
theorem explicitEulerLMM_isConsistent :
    explicitEulerLMM.IsConsistent :=
  ⟨explicitEulerLMM_isPreconsistent, explicitEulerLMM_satisfiesEq404b⟩

/-- Implicit Euler satisfies (404b). -/
theorem implicitEulerLMM_satisfiesEq404b :
    implicitEulerLMM.SatisfiesEq404b := by
  simp [LinearMultistepMethod.SatisfiesEq404b, implicitEulerLMM]

/-- Implicit Euler is consistent. -/
theorem implicitEulerLMM_isConsistent :
    implicitEulerLMM.IsConsistent :=
  ⟨implicitEulerLMM_isPreconsistent, implicitEulerLMM_satisfiesEq404b⟩

/-! ## §403 — Stability (def:403A)

Butcher §403, p. 341. The textbook defines stability as boundedness of
all solutions to the homogeneous recurrence (403a), which arises when
the linear multistep method is applied to the trivial IVP `f ≡ 0`. The
section also notes that this concept is variously known as
*zero-stability* or *stability in the sense of Dahlquist*.

We capture only the definition and two non-vacuity witnesses (both
Euler methods). Algebraic characterisations (root condition,
power-bounded companion matrix) are theorems (e.g. `thm:441C`), not the
definition; they will be added in later cycles. -/

/-- Butcher (403a): a sequence `y : ℕ → ℝ` is a *solution of the
homogeneous recurrence* of the linear multistep method `M` if for
every `m : ℕ`,

  `y (m + k) = α_1 · y_{m+k-1} + α_2 · y_{m+k-2} + ⋯ + α_k · y_m`.

This is equation (403a) — the difference equation that arises when the
method is applied to the trivial IVP `f ≡ 0`. The sum is indexed by
`i : Fin k`, with `i.succ : Fin (k+1)` selecting `α_{i.val + 1}` and
the offset `i.val + 1` running from 1 (giving `y_{m+k-1}`) to `k`
(giving `y_m`). -/
def LinearMultistepMethod.IsHomogeneousSolution {k : ℕ}
    (M : LinearMultistepMethod k) (y : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, y (m + k) = ∑ i : Fin k, M.α i.succ * y (m + k - (i.val + 1))

/-- Butcher Definition 403A (p. 341): a linear multistep method is
*stable* (also called *zero-stable* or *stable in the sense of
Dahlquist*) if every solution of the homogeneous recurrence (403a) is
bounded.

> "A linear multistep method [α, β] is 'stable' if the difference
> equation (403a) has only bounded solutions."

Boundedness is encoded as `∃ C, ∀ n, |y n| ≤ C`. -/
def LinearMultistepMethod.IsStable {k : ℕ}
    (M : LinearMultistepMethod k) : Prop :=
  ∀ y : ℕ → ℝ, M.IsHomogeneousSolution y → ∃ C, ∀ n, |y n| ≤ C

/-! ### Witnesses for stability

Both Euler methods have `k = 1`, `α 1 = 1`, so the homogeneous
recurrence collapses to `y (m + 1) = y m`, i.e. all solutions are
constant sequences and trivially bounded by `|y 0|`. -/

/-- Explicit Euler is Dahlquist-stable. -/
theorem explicitEulerLMM_isStable : explicitEulerLMM.IsStable := by
  intro y hy
  have hconst : ∀ n, y n = y 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        have hrec := hy n
        simp [explicitEulerLMM] at hrec
        linarith
  refine ⟨|y 0|, fun n => ?_⟩
  rw [hconst n]

/-- Implicit Euler is Dahlquist-stable. -/
theorem implicitEulerLMM_isStable : implicitEulerLMM.IsStable := by
  intro y hy
  have hconst : ∀ n, y n = y 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        have hrec := hy n
        simp [implicitEulerLMM] at hrec
        linarith
  refine ⟨|y 0|, fun n => ?_⟩
  rw [hconst n]

end OpenMath.Chapter4.Section404
