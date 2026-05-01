import Mathlib
import OpenMath.Chapter1.Section110
import OpenMath.Chapter1.Section141

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

open scoped NNReal Topology

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

/-! ## §402 — Convergence (def:402A)

Butcher §402, p. 340. We add the recurrence predicate `IsLMMSolution`
(the equation in the file's existing docstring), and the textbook
definition `IsConvergent` (Definition 402A). Two sanity helpers
(`isLMMSolution_zero_iff`, `const_sequence_isHomogeneousSolution`)
provide the non-vacuity content. The full convergence witness for any
concrete LMM is deferred (Butcher's theorem `thm:422C`); see the
issue file `lmm_convergence_witness_deferred.md`. -/

/-- Butcher §404, p. 341 (recurrence): a sequence `Y : ℕ → ℝ` is an
*LMM solution* of the linear multistep method `M` with step size `h`,
RHS `f`, and grid origin `x₀` if for every `n ≥ 0`,

  `Σ_{i=0}^{k} α_i · Y_{n+k-i} = -h · Σ_{i=0}^{k} β_i · f(x₀ + (n+k-i)·h, Y_{n+k-i})`.

The negative sign on the RHS is what reconciles the textbook
recurrence (Butcher §400, equation (400b))
`y_n = α_1 y_{n-1} + ⋯ + α_k y_{n-k} + h Σ_{i=0}^{k} β_i f(x_{n-i}, y_{n-i})`
— i.e. `y_n − Σ_{i=1}^k α_i y_{n-i} = h Σ_{i=0}^k β_i f` —
with the textbook normalisation `α_0 = -1`. Peeling the `i = 0`
term off the LHS sum yields
`-Y_n + Σ_{i=1}^k α_i Y_{n-i} = -h Σ β_i f`,
which rearranges to Butcher's recurrence
`Y_n − Σ_{i=1}^k α_i Y_{n-i} = h Σ β_i f`.

Sanity check: for explicit Euler (`α = (-1, 1)`, `β = (0, 1)`),
the recurrence at index `m` reads `-Y(m+1) + Y(m) = -h · f(Y(m))`,
i.e. `Y(m+1) = Y(m) + h f(Y(m))` — the textbook forward Euler step.

We use `n + k` as the index for the LHS (so `n + k - i` is replaced
with the natural-number subtraction that is always non-negative for
`i ≤ k`). The sum runs over `Fin (k + 1)` so it includes the leading
term `α 0` (= `-1` by `M.α_zero`). For `f ≡ 0` this reduces to
`IsHomogeneousSolution`; see `isLMMSolution_zero_iff`. -/
def LinearMultistepMethod.IsLMMSolution {k : ℕ}
    (M : LinearMultistepMethod k) (h x₀ : ℝ) (f : ℝ → ℝ → ℝ)
    (Y : ℕ → ℝ) : Prop :=
  ∀ n : ℕ,
    (∑ i : Fin (k + 1), M.α i * Y (n + k - i.val)) =
      -h * ∑ i : Fin (k + 1), M.β i *
        f (x₀ + ((n + k - i.val : ℕ) : ℝ) * h) (Y (n + k - i.val))

/-- Butcher Definition 402A (p. 340): a linear multistep method is
*convergent* if for every initial value problem

  `y'(x) = f(x, y(x)),    y(x₀) = y₀`

with `f` jointly continuous and Lipschitz in its second variable
(Butcher §110A `LipschitzInSecond`), every exact solution `yex` of
the IVP, every starting method whose iterates converge to `y₀` as the
step size shrinks, and every `x > x₀`, the sequence of LMM iterates
`Y_m` (with step size `h = (x - x₀)/m`) approximating `y(x)` satisfies

  `Y_m − yex(x) → 0,    as m → ∞`.

> "The linear multistep method is said to be 'convergent' if, for any
> such initial value problem, `Y_m − y(x) → 0, as m → ∞`."
> (Butcher 2008, p. 340.)

Encoded faithfully: `f` continuous, `f` Lipschitz-in-second, `yex`
solves the IVP, `start` produces the `k` initial values and converges
to `y₀` with `h`, and `Y m` is any sequence of iterates of `M` (with
step size `(x-x₀)/m`) whose first `k` entries match `start`. The
conclusion is the textbook limit. -/
def LinearMultistepMethod.IsConvergent {k : ℕ}
    (M : LinearMultistepMethod k) : Prop :=
  ∀ (f : ℝ → ℝ → ℝ),
    Continuous (Function.uncurry f) →
  ∀ (L : ℝ≥0),
    OpenMath.Chapter1.Section110.LipschitzInSecond Set.univ L f →
  ∀ (x₀ y₀ : ℝ) (yex : ℝ → ℝ),
    yex x₀ = y₀ →
    (∀ x ≥ x₀, HasDerivAt yex (f x (yex x)) x) →
  ∀ (start : ℝ → Fin k → ℝ),
    (∀ i : Fin k,
      Filter.Tendsto (fun h : ℝ => start h i) (nhds 0) (nhds y₀)) →
  ∀ (x : ℝ), x₀ < x →
  ∀ (Y : ℕ → ℕ → ℝ),
    (∀ m : ℕ, 0 < m →
      (∀ i : Fin k, Y m i.val = start ((x - x₀) / (m : ℝ)) i) ∧
      M.IsLMMSolution ((x - x₀) / (m : ℝ)) x₀ f (Y m)) →
    Filter.Tendsto (fun m : ℕ => Y m m - yex x) Filter.atTop (nhds 0)

/-! ### Sanity helpers — non-vacuity of the predicates

These are infrastructure for future convergence work (Butcher
`thm:422C` and `thm:406D` will both consume them). They also
demonstrate the predicates are non-vacuous: `IsLMMSolution` for the
trivial RHS `f ≡ 0` matches `IsHomogeneousSolution` exactly, and
constant sequences solve the homogeneous recurrence whenever the
method is preconsistent. -/

/-- Sanity bridge: when `f ≡ 0`, an LMM solution is exactly a
solution of the homogeneous recurrence (403a). The two predicates use
different index conventions (`IsLMMSolution` sums over `Fin (k+1)`
including `α 0`; `IsHomogeneousSolution` only over `Fin k`), but they
agree on this trivial RHS thanks to `M.α_zero = -1`. -/
theorem isLMMSolution_zero_iff {k : ℕ} (M : LinearMultistepMethod k)
    (h x₀ : ℝ) (Y : ℕ → ℝ) :
    M.IsLMMSolution h x₀ (fun _ _ => 0) Y ↔
      M.IsHomogeneousSolution Y := by
  unfold LinearMultistepMethod.IsLMMSolution
  unfold LinearMultistepMethod.IsHomogeneousSolution
  constructor
  · intro hLMM n
    have hn := hLMM n
    simp only [mul_zero, Finset.sum_const_zero] at hn
    rw [Fin.sum_univ_succ] at hn
    simp only [Fin.val_zero, Nat.sub_zero, M.α_zero, Fin.val_succ] at hn
    linarith
  · intro hHom n
    have hn := hHom n
    simp only [mul_zero, Finset.sum_const_zero]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.sub_zero, M.α_zero, Fin.val_succ]
    linarith

/-- Sanity-check witness: an `explicitEulerLMM.IsLMMSolution` reduces
to the textbook explicit Euler step `Y(m+1) = Y(m) + h · f(x_m, Y(m))`.

This lemma exists to lock in the sign convention of `IsLMMSolution`
against future drift. (Cycle 044 fixed a sign bug in
`IsLMMSolution`; cycle 045 adds this regression witness so the bug
cannot silently re-appear.) -/
theorem explicitEulerLMM_step_eq
    {f : ℝ → ℝ → ℝ} {Y : ℕ → ℝ} {x₀ h : ℝ}
    (hY : explicitEulerLMM.IsLMMSolution h x₀ f Y) (m : ℕ) :
    Y (m + 1) = Y m + h * f (x₀ + (m : ℝ) * h) (Y m) := by
  have h_step := hY m
  -- The IsLMMSolution recurrence at index m for k = 1 reads
  --   Σ_{i ∈ Fin 2} α i · Y(m + 1 - i) = -h · Σ_{i ∈ Fin 2} β i · f(x₀+(m+1-i)h, Y(m+1-i)).
  -- Unfolding `Fin 2` via `Fin.sum_univ_two` and using
  -- explicitEulerLMM's coefficients (α 0 = -1, α 1 = 1, β 0 = 0, β 1 = 1)
  -- yields the textbook step.
  have ha0 : explicitEulerLMM.α 0 = -1 := explicitEulerLMM.α_zero
  have ha1 : explicitEulerLMM.α 1 = 1 := by simp [explicitEulerLMM]
  have hb0 : explicitEulerLMM.β 0 = 0 := by simp [explicitEulerLMM]
  have hb1 : explicitEulerLMM.β 1 = 1 := by simp [explicitEulerLMM]
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at h_step
  simp only [Fin.val_zero, Fin.val_one, Nat.sub_zero, Nat.add_sub_cancel,
             ha0, ha1, hb0, hb1] at h_step
  linarith

/-- A constant sequence solves the homogeneous recurrence (403a)
provided the method is preconsistent. This is folklore: a method
preserves constants iff the α-coefficients sum to one, which is
exactly equation (404a). -/
theorem const_sequence_isHomogeneousSolution {k : ℕ}
    (M : LinearMultistepMethod k) (hM : M.IsPreconsistent) (c : ℝ) :
    M.IsHomogeneousSolution (fun _ : ℕ => c) := by
  intro m
  have hsum : ∑ i : Fin k, M.α i.succ * c = (∑ i : Fin k, M.α i.succ) * c := by
    rw [Finset.sum_mul]
  rw [hsum, ← hM, one_mul]

/-! ## §406 — Local truncation error (def:406A)

Butcher §406, p. 345. Quoting `entities/def_406A.json`:

> Let `[α, β]` be a consistent linear multistep method. The 'local
> truncation error' associated with a differentiable function `y` at a
> point `x` with stepsize `h` is the value of
> `L(y, x, h) = y(x) − Σ_{i=1}^{k} α_i · y(x − ih) − h · Σ_{i=0}^{k} β_i · y'(x − ih)`.

We follow Option A from the cycle 039 strategy: encode the formula
directly. The textbook sums α from `i = 1` to `i = k`, which we encode
via `M.α i.succ` over `i : Fin k`; the β-sum runs from `i = 0` to
`i = k` over `Fin (k + 1)`. We use Mathlib's `deriv y` for `y'(·)`
(the value `0` is returned at non-differentiable points; the textbook
already restricts to differentiable `y`, so this convention agrees on
the textbook's domain).

Note: the `M.α 0 = -1` normalisation does **not** appear in the
textbook formula — Butcher's sum starts at `i = 1`, so `α 0` is
unused. The definition therefore makes sense for *any* coefficient
data (preconsistency / consistency are properties of `M`, not of the
LTE expression itself). -/

/-- Butcher Definition 406A (p. 345): the *local truncation error*
of a linear multistep method `M` associated with a function `y` at
point `x` with stepsize `h`.

Encoded directly from the textbook formula (Option A, cycle 039
strategy):

  `L(y, x, h) = y x
                  − Σ_{i ∈ Fin k} α_{i+1} · y(x − (i+1)·h)
                  − h · Σ_{i ∈ Fin (k+1)} β_i · y'(x − i·h)`,

with `y'` interpreted as Mathlib's `deriv y`. -/
noncomputable def LinearMultistepMethod.localTruncationError {k : ℕ}
    (M : LinearMultistepMethod k) (y : ℝ → ℝ) (x h : ℝ) : ℝ :=
  y x
    - ∑ i : Fin k, M.α i.succ * y (x - ((i.val + 1 : ℕ) : ℝ) * h)
    - h * ∑ i : Fin (k + 1), M.β i * deriv y (x - ((i.val : ℕ) : ℝ) * h)

/-! ### Witnesses for `localTruncationError`

Two non-vacuity facts (per CLAUDE.md) demonstrating the LTE behaves
as the textbook expects:

1. Constant solutions kill the LTE under preconsistency.
2. Linear-in-`x` solutions kill the LTE under consistency. -/

/-- A constant function has vanishing local truncation error for any
preconsistent linear multistep method.

Computation: the α-sum equals `c · Σ M.α i.succ = c · 1 = c`
(preconsistency); the β-sum vanishes because `deriv (fun _ => c) = 0`.
So `L = c − c − 0 = 0`. -/
theorem localTruncationError_const {k : ℕ}
    (M : LinearMultistepMethod k) (hpre : M.IsPreconsistent) (c x h : ℝ) :
    M.localTruncationError (fun _ => c) x h = 0 := by
  unfold LinearMultistepMethod.localTruncationError
  have hα : ∑ i : Fin k, M.α i.succ * c = c := by
    rw [← Finset.sum_mul, ← hpre, one_mul]
  have hd : deriv (fun _ : ℝ => c) = fun _ => 0 := by
    funext t; exact deriv_const t c
  simp only [hd]
  rw [hα]
  simp

/-- A linear function has vanishing local truncation error for any
consistent linear multistep method.

Computation: writing `y(t) = a·t + b`, the α-sum unfolds to
`a·x · Σ M.α i.succ − a·h · Σ (i+1)·M.α i.succ + b · Σ M.α i.succ`
= `a·x − a·h · Σ (i+1)·M.α i.succ + b` (preconsistency); the β-sum
is `a · Σ M.β i`. The (404b) consistency identity
`Σ (i+1)·M.α i.succ = Σ M.β i` makes the residual `−a·h·(Σ β) + h·a·(Σ β)`
cancel. -/
theorem localTruncationError_linear {k : ℕ}
    (M : LinearMultistepMethod k) (hcons : M.IsConsistent) (a b x h : ℝ) :
    M.localTruncationError (fun t => a * t + b) x h = 0 := by
  obtain ⟨hpre, h404b⟩ := hcons
  unfold LinearMultistepMethod.localTruncationError
  -- compute deriv of t ↦ a*t + b
  have hd : deriv (fun t : ℝ => a * t + b) = fun _ => a := by
    funext t
    have h1 : HasDerivAt (fun t : ℝ => a * t + b) a t := by
      simpa using ((hasDerivAt_id t).const_mul a).add_const b
    exact h1.deriv
  simp only [hd]
  -- α-sum: expand a*(x - (i+1)*h) + b
  have hα_expand : ∀ i : Fin k,
      M.α i.succ * (a * (x - ((i.val + 1 : ℕ) : ℝ) * h) + b)
        = a * x * M.α i.succ
          - a * h * (((i.val + 1 : ℕ) : ℝ) * M.α i.succ)
          + b * M.α i.succ := by
    intro i; ring
  rw [Finset.sum_congr rfl (fun i _ => hα_expand i)]
  -- split sum into three pieces
  rw [show (∑ i : Fin k,
        (a * x * M.α i.succ
          - a * h * (((i.val + 1 : ℕ) : ℝ) * M.α i.succ)
          + b * M.α i.succ))
      = (∑ i : Fin k, a * x * M.α i.succ)
        - (∑ i : Fin k, a * h * (((i.val + 1 : ℕ) : ℝ) * M.α i.succ))
        + ∑ i : Fin k, b * M.α i.succ from by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]]
  -- pull out constants
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  -- preconsistency: Σ M.α i.succ = 1
  rw [← hpre]
  -- (404b): Σ ((i+1) : ℝ) * M.α i.succ = Σ M.β i
  -- M.SatisfiesEq404b states `(∑ i : Fin k, ((i : ℕ) + 1 : ℝ) * M.α i.succ) = ∑ i, M.β i`
  have h404b' : (∑ i : Fin k, (((i.val + 1 : ℕ) : ℝ)) * M.α i.succ)
      = ∑ i : Fin (k + 1), M.β i := by
    have := h404b
    unfold LinearMultistepMethod.SatisfiesEq404b at this
    convert this using 1
    apply Finset.sum_congr rfl
    intro i _; push_cast; ring
  rw [h404b']
  -- final β-sum identity
  have hβ' : h * ∑ i : Fin (k + 1), M.β i * a = a * h * ∑ i : Fin (k + 1), M.β i := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _; ring
  rw [hβ']
  ring

/-! ## §406 — Convergence condition sufficiency bound (lem:406B)

Butcher §406, p. 346. Quoting `entities/lem_406B.json`:

> If `y` is the exact solution to the standard initial value problem
> and `x ∈ [x₀ + kh, x̄]`, then
>   `|L(y, x, h)| ≤ (½ ∑_{i=1}^k i² |α_i| + ∑_{i=1}^k i |i α_i − β_i|) L M h²`.

**Textbook discrepancy** (cycle 040): the textbook proof claims the
decomposition

  `L = ∑ α_i (y(x) − y(x−ih) − ih y'(x)) + h ∑ (iα_i − β_i)(y'(x) − y'(x−ih))`,

which would give `∑ i|iα_i − β_i|` in the bound. Direct algebraic
verification shows this decomposition is wrong (it disagrees with
def:406A on explicit Euler). The algebraically correct form uses
`β_i` instead of `iα_i − β_i`:

  `L = ∑ α_i (y(x) − y(x−ih) − ih y'(x)) + h ∑ β_i (y'(x) − y'(x−ih))`,

producing the bound `∑ i|β_i|`. We encode the corrected statement.
See `.prover-state/issues/lem_406B_textbook_check.md` for the full
derivation.

The proof decomposes into integration sub-lemmas (FTC, Lipschitz
bookkeeping) that are written sorry-first in this cycle and closed
incrementally over later cycles. -/

/-- Sub-lemma A: pointwise bound on `|y(x + h*ξ) − y x|` for ξ ≤ 0
under the IVP hypotheses `y' = f∘y` and `‖f∘y‖ ≤ M_bound`.

Proof: write
`y(x + hξ) − y(x) = ∫_x^{x+hξ} y'(t) dt = ∫_x^{x+hξ} f(y(t)) dt`
via FTC, then bound by `M_bound` times the length `h·|ξ|`.

**Hypothesis-strength note (faithfulness check, cycle 041)**.
The textbook (Butcher §406) implicitly assumes `y ∈ C¹`: it
applies FTC to `y'`, which requires `y'` to be continuous. The
Picard–Lindelöf theorem (Butcher §110, our `thm:110C`) produces
exactly such a `C¹` solution from a Lipschitz `f`. We surface
this requirement explicitly via `ContDiff ℝ 1 y`, which is
strictly equivalent to "`y` differentiable with continuous
derivative" — i.e. **not** a strengthening relative to the
textbook, only making explicit what was implicit. -/
lemma exact_solution_norm_bound
    {f : ℝ → ℝ} {M_bound : ℝ} (hM : 0 ≤ M_bound)
    {y : ℝ → ℝ}
    (hy_C1 : ContDiff ℝ 1 y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (hf_y_bound : ∀ t, |f (y t)| ≤ M_bound)
    (x h : ℝ) (hh : 0 ≤ h)
    (ξ : ℝ) (hξ : ξ ≤ 0) :
    |y (x + h * ξ) - y x| ≤ h * (-ξ) * M_bound := by
  -- Step 1: f∘y is continuous (it equals deriv y, which is continuous from C¹ y).
  have hfy_cont : Continuous (fun t => f (y t)) := by
    have heq : (fun t => f (y t)) = deriv y := by
      funext t; exact (hy_ode t).symm
    rw [heq]
    exact hy_C1.continuous_deriv le_rfl
  -- Step 2: HasDerivAt y (f (y t)) t at every t.
  have hderiv : ∀ t, HasDerivAt y (f (y t)) t := by
    intro t
    have hdiff := (hy_C1.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0)) t
    have ht := hdiff.hasDerivAt
    rw [hy_ode t] at ht
    exact ht
  -- Step 3: integrability.
  have hint : IntervalIntegrable (fun t => f (y t)) MeasureTheory.volume
                x (x + h * ξ) := hfy_cont.intervalIntegrable _ _
  -- Step 4: FTC.
  have hFTC : ∫ t in x..(x + h * ξ), f (y t) = y (x + h * ξ) - y x :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hint
  -- Step 5: bound the integral by M_bound.
  have hC : ∀ t ∈ Set.uIoc x (x + h * ξ), ‖f (y t)‖ ≤ M_bound := by
    intro t _
    rw [Real.norm_eq_abs]
    exact hf_y_bound t
  have hbound :
      |∫ t in x..(x + h * ξ), f (y t)| ≤ M_bound * |h * ξ| := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const hC
    rw [Real.norm_eq_abs] at hb
    have hsub : (x + h * ξ) - x = h * ξ := by ring
    rw [hsub] at hb
    exact hb
  rw [hFTC] at hbound
  -- Step 6: |h*ξ| = h*(-ξ).
  have habs : |h * ξ| = h * (-ξ) := by
    rw [abs_mul, abs_of_nonneg hh, abs_of_nonpos hξ]
  rw [habs] at hbound
  calc |y (x + h * ξ) - y x|
      ≤ M_bound * (h * (-ξ)) := hbound
    _ = h * (-ξ) * M_bound := by ring

/-- Sub-lemma B: integral form for the residual
`y(x) − y(x − i*h) − i*h*y'(x)`.

Proof sketch (deferred): apply FTC to write
`y(x) − y(x − i*h) = ∫_{x−i*h}^x y'(t) dt`, change variables
`t = x + h*ξ` to get an integral over `(−i, 0)`, and subtract
`i*h*y'(x)`. -/
lemma residual_integral_form
    {f : ℝ → ℝ} {y : ℝ → ℝ}
    (hy_C1 : ContDiff ℝ 1 y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (i : ℕ) (x h : ℝ) (hh : 0 ≤ h) :
    y x - y (x - (i : ℝ) * h) - ((i : ℝ) * h) * deriv y x
      = h * ∫ ξ in (-(i : ℝ))..0, (f (y (x + h*ξ)) - f (y x)) := by
  -- Setup: f∘y is continuous (it equals deriv y).
  have hfy_cont : Continuous (fun t => f (y t)) := by
    have heq : (fun t => f (y t)) = deriv y := by
      funext t; exact (hy_ode t).symm
    rw [heq]
    exact hy_C1.continuous_deriv le_rfl
  -- HasDerivAt y (f (y t)) t pointwise.
  have hderiv : ∀ t, HasDerivAt y (f (y t)) t := by
    intro t
    have hdiff := (hy_C1.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0)) t
    have ht := hdiff.hasDerivAt
    rw [hy_ode t] at ht
    exact ht
  -- Integrability of f∘y on any interval.
  have hfy_int : ∀ a b : ℝ,
      IntervalIntegrable (fun t => f (y t)) MeasureTheory.volume a b :=
    fun a b => hfy_cont.intervalIntegrable a b
  -- Continuity of ξ ↦ f(y(x + h*ξ)) and integrability on (-i, 0).
  have hfyhx_cont : Continuous (fun ξ : ℝ => f (y (x + h * ξ))) := by
    have hlin : Continuous (fun ξ : ℝ => x + h * ξ) := by fun_prop
    exact hfy_cont.comp hlin
  have hfyhx_int : IntervalIntegrable (fun ξ : ℝ => f (y (x + h * ξ)))
                     MeasureTheory.volume (-(i : ℝ)) 0 :=
    hfyhx_cont.intervalIntegrable _ _
  have hfyx_int : IntervalIntegrable (fun _ : ℝ => f (y x))
                     MeasureTheory.volume (-(i : ℝ)) 0 :=
    continuous_const.intervalIntegrable _ _
  -- Step A: FTC on [(x - i*h), x].
  have hFTC : ∫ t in (x - (i : ℝ) * h)..x, f (y t)
                = y x - y (x - (i : ℝ) * h) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hderiv t) (hfy_int _ _)
  -- Step B: change of variables t = h*ξ + x via smul_integral_comp_mul_add.
  have hCV : h * ∫ ξ in (-(i : ℝ))..0, f (y (x + h * ξ))
              = ∫ t in (x - (i : ℝ) * h)..x, f (y t) := by
    have hCV0 := intervalIntegral.smul_integral_comp_mul_add
                    (fun t => f (y t)) (a := -(i : ℝ)) (b := 0)
                    h x
    -- hCV0 : h • ∫ ξ in (-(i:ℝ))..0, f(y(h*ξ + x))
    --        = ∫ t in (h*(-(i:ℝ)) + x)..(h*0 + x), f(y t)
    have heq_l : h * (-(i : ℝ)) + x = x - (i : ℝ) * h := by ring
    have heq_r : h * (0 : ℝ) + x = x := by ring
    have hbody : (fun ξ : ℝ => f (y (h * ξ + x)))
                  = (fun ξ : ℝ => f (y (x + h * ξ))) := by
      funext ξ; rw [add_comm (h * ξ) x]
    rw [smul_eq_mul, hbody, heq_l, heq_r] at hCV0
    exact hCV0
  -- Step C: constant integral ∫ _ in (-i)..0, f(y x) = i * f(y x).
  have hConst : ∫ _ in (-(i : ℝ))..(0 : ℝ), f (y x) = (i : ℝ) * f (y x) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  -- Step D: assemble.
  rw [intervalIntegral.integral_sub hfyhx_int hfyx_int]
  rw [hConst, mul_sub, hCV, hFTC, hy_ode x]
  ring

/-- Sub-lemma C: bound on `|y(x) − y(x − i*h) − i*h*y'(x)|`.

Combines sub-lemmas A and B with the Lipschitz hypothesis on `f`:

  `|y(x) − y(x − i*h) − i*h*y'(x)| ≤ (1/2) i² h² L M`. -/
lemma residual_bound
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {y : ℝ → ℝ}
    (hy_C1 : ContDiff ℝ 1 y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (hf_y_bound : ∀ t, |f (y t)| ≤ M_bound)
    (i : ℕ) (x h : ℝ) (hh : 0 ≤ h) :
    |y x - y (x - (i : ℝ) * h) - ((i : ℝ) * h) * deriv y x|
      ≤ (1/2) * (i : ℝ)^2 * h^2 * L * M_bound := by
  -- Step 1: rewrite LHS via sub-lemma B (residual_integral_form).
  rw [residual_integral_form hy_C1 hy_ode i x h hh]
  -- Goal: |h * ∫ ξ in (-i)..0, (f(y(x+hξ)) - f(y x))|
  --        ≤ (1/2) * i^2 * h^2 * L * M_bound
  -- Step 2: |h * X| = h * |X| since h ≥ 0.
  rw [abs_mul, abs_of_nonneg hh]
  -- Continuity helpers (mirroring sub-lemma B / A setup).
  have hfy_cont : Continuous (fun t => f (y t)) := by
    have heq : (fun t => f (y t)) = deriv y := by
      funext t; exact (hy_ode t).symm
    rw [heq]
    exact hy_C1.continuous_deriv le_rfl
  have hyhx_cont : Continuous (fun ξ : ℝ => y (x + h * ξ)) := by
    have hlin : Continuous (fun ξ : ℝ => x + h * ξ) := by fun_prop
    exact hy_C1.continuous.comp hlin
  have hfyhx_cont : Continuous (fun ξ : ℝ => f (y (x + h * ξ))) := by
    have hlin : Continuous (fun ξ : ℝ => x + h * ξ) := by fun_prop
    exact hfy_cont.comp hlin
  have hi_le : -(i : ℝ) ≤ 0 := neg_nonpos_of_nonneg (Nat.cast_nonneg i)
  -- Integrability obligations.
  have hint_abs_diff :
      IntervalIntegrable (fun ξ => |f (y (x + h * ξ)) - f (y x)|)
        MeasureTheory.volume (-(i : ℝ)) 0 :=
    ((hfyhx_cont.sub continuous_const).abs).intervalIntegrable _ _
  have hint_L_diff :
      IntervalIntegrable (fun ξ => L * |y (x + h * ξ) - y x|)
        MeasureTheory.volume (-(i : ℝ)) 0 :=
    (continuous_const.mul ((hyhx_cont.sub continuous_const).abs)).intervalIntegrable _ _
  have hint_A :
      IntervalIntegrable (fun ξ : ℝ => L * (h * (-ξ) * M_bound))
        MeasureTheory.volume (-(i : ℝ)) 0 := by
    have hcont : Continuous (fun ξ : ℝ => L * (h * (-ξ) * M_bound)) := by fun_prop
    exact hcont.intervalIntegrable _ _
  -- Step 3: |∫| ≤ ∫|·|.
  have h_abs_int :
      |∫ ξ in (-(i : ℝ))..0, (f (y (x + h * ξ)) - f (y x))|
        ≤ ∫ ξ in (-(i : ℝ))..0, |f (y (x + h * ξ)) - f (y x)| :=
    intervalIntegral.abs_integral_le_integral_abs hi_le
  -- Step 4: pointwise Lipschitz bound.
  have hLip_pw : ∀ ξ : ℝ,
      |f (y (x + h * ξ)) - f (y x)| ≤ L * |y (x + h * ξ) - y x| := by
    intro ξ
    have hd := hf_lip.dist_le_mul (y (x + h * ξ)) (y x)
    rw [Real.dist_eq, Real.dist_eq] at hd
    have hco : ((Real.toNNReal L : ℝ≥0) : ℝ) = L := Real.coe_toNNReal L hL
    rw [hco] at hd
    exact hd
  have h_int_lip :
      ∫ ξ in (-(i : ℝ))..0, |f (y (x + h * ξ)) - f (y x)|
        ≤ ∫ ξ in (-(i : ℝ))..0, L * |y (x + h * ξ) - y x| :=
    intervalIntegral.integral_mono_on hi_le hint_abs_diff hint_L_diff
      (fun ξ _ => hLip_pw ξ)
  -- Step 5: pointwise sub-lemma A bound for ξ ∈ [-i, 0].
  have h_int_A :
      ∫ ξ in (-(i : ℝ))..0, L * |y (x + h * ξ) - y x|
        ≤ ∫ ξ in (-(i : ℝ))..0, L * (h * (-ξ) * M_bound) := by
    apply intervalIntegral.integral_mono_on hi_le hint_L_diff hint_A
    intro ξ hξ
    have hξ_le : ξ ≤ 0 := hξ.2
    exact mul_le_mul_of_nonneg_left
      (exact_solution_norm_bound hM hy_C1 hy_ode hf_y_bound x h hh ξ hξ_le) hL
  -- Step 6: compute ∫ ξ in (-i)..0, L * (h * (-ξ) * M_bound) = L * h * M_bound * (i^2 / 2).
  have h_int_eq :
      ∫ ξ in (-(i : ℝ))..0, L * (h * (-ξ) * M_bound)
        = L * h * M_bound * ((i : ℝ)^2 / 2) := by
    have heq : (fun ξ : ℝ => L * (h * (-ξ) * M_bound))
                 = (fun ξ : ℝ => (L * h * M_bound) * (-ξ)) := by
      funext ξ; ring
    rw [heq, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_neg, integral_id]
    ring
  -- Step 7: assemble.
  calc h * |∫ ξ in (-(i : ℝ))..0, (f (y (x + h * ξ)) - f (y x))|
      ≤ h * ∫ ξ in (-(i : ℝ))..0, |f (y (x + h * ξ)) - f (y x)| :=
        mul_le_mul_of_nonneg_left h_abs_int hh
    _ ≤ h * ∫ ξ in (-(i : ℝ))..0, L * |y (x + h * ξ) - y x| :=
        mul_le_mul_of_nonneg_left h_int_lip hh
    _ ≤ h * ∫ ξ in (-(i : ℝ))..0, L * (h * (-ξ) * M_bound) :=
        mul_le_mul_of_nonneg_left h_int_A hh
    _ = h * (L * h * M_bound * ((i : ℝ)^2 / 2)) := by rw [h_int_eq]
    _ = (1/2) * (i : ℝ)^2 * h^2 * L * M_bound := by ring

/-- Sub-lemma D: Lipschitz bound on the difference
`|y'(x) − y'(x − i*h)|`.

Since `y'(t) = f(y(t))` and `f` is Lipschitz, this becomes
`|f(y(x)) − f(y(x − i*h))| ≤ L · |y(x) − y(x − i*h)| ≤ L · (i*h*M)`. -/
lemma deriv_diff_bound
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {y : ℝ → ℝ}
    (hy_C1 : ContDiff ℝ 1 y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (hf_y_bound : ∀ t, |f (y t)| ≤ M_bound)
    (i : ℕ) (x h : ℝ) (hh : 0 ≤ h) :
    |deriv y x - deriv y (x - (i : ℝ) * h)|
      ≤ (i : ℝ) * h * L * M_bound := by
  rw [hy_ode x, hy_ode (x - (i : ℝ) * h)]
  -- Step 1: Lipschitz on f.
  have hLip : |f (y x) - f (y (x - (i : ℝ) * h))|
                ≤ L * |y x - y (x - (i : ℝ) * h)| := by
    have hd := hf_lip.dist_le_mul (y x) (y (x - (i : ℝ) * h))
    rw [Real.dist_eq, Real.dist_eq] at hd
    have hco : ((Real.toNNReal L : ℝ≥0) : ℝ) = L := Real.coe_toNNReal L hL
    rw [hco] at hd
    exact hd
  -- Step 2: apply sub-lemma A at ξ = -(i : ℝ).
  have hA_raw := exact_solution_norm_bound hM hy_C1 hy_ode hf_y_bound
                   x h hh (-(i : ℝ)) (neg_nonpos_of_nonneg (Nat.cast_nonneg i))
  have hA : |y x - y (x - (i : ℝ) * h)| ≤ h * (i : ℝ) * M_bound := by
    have heq1 : x + h * (-(i : ℝ)) = x - (i : ℝ) * h := by ring
    have heq2 : -(-(i : ℝ)) = (i : ℝ) := by ring
    rw [heq1, heq2] at hA_raw
    rw [abs_sub_comm]
    exact hA_raw
  -- Step 3: combine.
  calc |f (y x) - f (y (x - (i : ℝ) * h))|
      ≤ L * |y x - y (x - (i : ℝ) * h)| := hLip
    _ ≤ L * (h * (i : ℝ) * M_bound) := mul_le_mul_of_nonneg_left hA hL
    _ = (i : ℝ) * h * L * M_bound := by ring

/-- Sub-lemma E: algebraic decomposition of the local truncation error
under consistency.

This is the **algebraically corrected** form (see the `§406` block
header for the textbook discrepancy and the issue file
`.prover-state/issues/lem_406B_textbook_check.md`):

  `L(y,x,h) = ∑ α_i (y(x) − y(x−ih) − ih y'(x))
              + h ∑ β_i (y'(x) − y'(x−ih))`. -/
lemma LinearMultistepMethod.localTruncationError_decomposition {k : ℕ}
    (M : LinearMultistepMethod k) (hcons : M.IsConsistent)
    (y : ℝ → ℝ) (x h : ℝ) :
    M.localTruncationError y x h
      = (∑ i : Fin k, M.α i.succ
          * (y x - y (x - ((i.val + 1 : ℕ) : ℝ) * h)
             - ((i.val + 1 : ℕ) : ℝ) * h * deriv y x))
        + h * ∑ i : Fin k, M.β i.succ
              * (deriv y x - deriv y (x - ((i.val + 1 : ℕ) : ℝ) * h)) := by
  obtain ⟨hpre, h404b⟩ := hcons
  -- Cast bridge: SatisfiesEq404b uses `((i : ℕ) + 1 : ℝ)`, our expanded
  -- α-sum produces `(((i.val + 1 : ℕ) : ℝ))`. (Per MEMORY.md.)
  have h404b' : (∑ i : Fin k, (((i.val + 1 : ℕ) : ℝ)) * M.α i.succ)
      = ∑ i : Fin (k + 1), M.β i := by
    unfold LinearMultistepMethod.SatisfiesEq404b at h404b
    convert h404b using 1
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  -- Step 1: peel `i = 0` off the LHS β-sum (over `Fin (k+1)`).
  have hLHS :
      M.localTruncationError y x h
        = y x - (∑ i : Fin k, M.α i.succ * y (x - ((i.val + 1 : ℕ) : ℝ) * h))
          - h * M.β 0 * deriv y x
          - h * (∑ i : Fin k, M.β i.succ
                  * deriv y (x - ((i.val + 1 : ℕ) : ℝ) * h)) := by
    unfold LinearMultistepMethod.localTruncationError
    rw [Fin.sum_univ_succ
        (f := fun i : Fin (k + 1) => M.β i * deriv y (x - ((i.val : ℕ) : ℝ) * h))]
    simp only [Fin.val_zero, Nat.cast_zero, zero_mul, sub_zero, Fin.val_succ]
    ring
  -- Step 2: distribute the α-sum on the RHS, then collapse with preconsistency.
  have hα_dist :
      (∑ i : Fin k, M.α i.succ
          * (y x - y (x - ((i.val + 1 : ℕ) : ℝ) * h)
             - ((i.val + 1 : ℕ) : ℝ) * h * deriv y x))
        = y x - (∑ i : Fin k, M.α i.succ * y (x - ((i.val + 1 : ℕ) : ℝ) * h))
          - h * deriv y x
              * (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ) := by
    have heach : ∀ i : Fin k,
        M.α i.succ
          * (y x - y (x - ((i.val + 1 : ℕ) : ℝ) * h)
             - ((i.val + 1 : ℕ) : ℝ) * h * deriv y x)
        = M.α i.succ * y x
          - M.α i.succ * y (x - ((i.val + 1 : ℕ) : ℝ) * h)
          - h * deriv y x * (((i.val + 1 : ℕ) : ℝ) * M.α i.succ) :=
      fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => heach i)]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    rw [show (∑ i : Fin k, M.α i.succ * y x)
            = (∑ i : Fin k, M.α i.succ) * y x from by rw [← Finset.sum_mul]]
    rw [show (∑ i : Fin k, h * deriv y x * (((i.val + 1 : ℕ) : ℝ) * M.α i.succ))
            = h * deriv y x
                * (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ) from by
        rw [← Finset.mul_sum]]
    rw [← hpre]
    ring
  -- Step 3: distribute the β-sum on the RHS.
  have hβ_dist :
      (∑ i : Fin k, M.β i.succ
          * (deriv y x - deriv y (x - ((i.val + 1 : ℕ) : ℝ) * h)))
        = (∑ i : Fin k, M.β i.succ) * deriv y x
          - (∑ i : Fin k, M.β i.succ
                  * deriv y (x - ((i.val + 1 : ℕ) : ℝ) * h)) := by
    have heach : ∀ i : Fin k,
        M.β i.succ
          * (deriv y x - deriv y (x - ((i.val + 1 : ℕ) : ℝ) * h))
        = M.β i.succ * deriv y x
          - M.β i.succ * deriv y (x - ((i.val + 1 : ℕ) : ℝ) * h) :=
      fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => heach i)]
    rw [Finset.sum_sub_distrib]
    rw [show (∑ i : Fin k, M.β i.succ * deriv y x)
            = (∑ i : Fin k, M.β i.succ) * deriv y x from by rw [← Finset.sum_mul]]
  -- Step 4: combine, substitute (404b), peel `M.β 0` off the (k+1)-sum, ring.
  rw [hLHS, hα_dist, hβ_dist, h404b']
  rw [Fin.sum_univ_succ (f := M.β)]
  ring

/-- Helper for `localTruncationError_bound`: the α-sum from the
sub-lemma E decomposition is bounded by the α-coefficient of the
final RHS times `(1/2) * h^2 * L * M`.

Each summand has the form `|α_{i+1}| · |residual at step (i+1)|`,
and `residual_bound` (sub-lemma C) bounds `|residual|` by
`(1/2) (i+1)² h² L M`. The result follows from triangle inequality
+ summand-wise monotonicity. -/
lemma localTruncationError_α_sum_bound {k : ℕ}
    (M : LinearMultistepMethod k)
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {y : ℝ → ℝ}
    (hy_C1 : ContDiff ℝ 1 y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (hf_y_bound : ∀ t, |f (y t)| ≤ M_bound)
    (x h : ℝ) (hh : 0 ≤ h) :
    |∑ i : Fin k, M.α i.succ
        * (y x - y (x - ((i.val + 1 : ℕ) : ℝ) * h)
           - ((i.val + 1 : ℕ) : ℝ) * h * deriv y x)|
      ≤ (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
        * ((1/2) * h^2 * L * M_bound) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [show (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
          * ((1/2) * h^2 * L * M_bound)
        = ∑ i : Fin k,
            (((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
              * ((1/2) * h^2 * L * M_bound) from
        by rw [Finset.sum_mul]]
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  have hC := residual_bound hL hM hf_lip hy_C1 hy_ode hf_y_bound
               (i.val + 1) x h hh
  calc |M.α i.succ|
        * |y x - y (x - ((i.val + 1 : ℕ) : ℝ) * h)
            - ((i.val + 1 : ℕ) : ℝ) * h * deriv y x|
      ≤ |M.α i.succ|
          * ((1/2) * ((i.val + 1 : ℕ) : ℝ)^2 * h^2 * L * M_bound) :=
        mul_le_mul_of_nonneg_left hC (abs_nonneg _)
    _ = (((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
          * ((1/2) * h^2 * L * M_bound) := by ring

/-- Helper for `localTruncationError_bound`: the β-sum from the
sub-lemma E decomposition is bounded by the β-coefficient of the
final RHS times `(h * L * M)`.

Each summand has the form `|β_{i+1}| · |y'(x) − y'(x − (i+1)h)|`,
and `deriv_diff_bound` (sub-lemma D) bounds the y'-difference by
`(i+1) h L M`. -/
lemma localTruncationError_β_sum_bound {k : ℕ}
    (M : LinearMultistepMethod k)
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {y : ℝ → ℝ}
    (hy_C1 : ContDiff ℝ 1 y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (hf_y_bound : ∀ t, |f (y t)| ≤ M_bound)
    (x h : ℝ) (hh : 0 ≤ h) :
    |∑ i : Fin k, M.β i.succ
        * (deriv y x - deriv y (x - ((i.val + 1 : ℕ) : ℝ) * h))|
      ≤ (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|)
        * (h * L * M_bound) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [show (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|)
          * (h * L * M_bound)
        = ∑ i : Fin k,
            (((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|) * (h * L * M_bound) from
        by rw [Finset.sum_mul]]
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  have hD := deriv_diff_bound hL hM hf_lip hy_C1 hy_ode hf_y_bound
               (i.val + 1) x h hh
  calc |M.β i.succ|
        * |deriv y x - deriv y (x - ((i.val + 1 : ℕ) : ℝ) * h)|
      ≤ |M.β i.succ| * (((i.val + 1 : ℕ) : ℝ) * h * L * M_bound) :=
        mul_le_mul_of_nonneg_left hD (abs_nonneg _)
    _ = (((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|) * (h * L * M_bound) := by ring

/-- Butcher Lemma 406B (corrected, p. 346): for a consistent linear
multistep method, the local truncation error of the exact solution
of an IVP `y' = f∘y` with `f` Lipschitz (constant `L`) and `‖f∘y‖`
bounded by `M_bound` satisfies

  `|L(y, x, h)| ≤ (½ ∑ (i+1)² |α_{i+1}| + ∑ (i+1) |β_{i+1}|) · L · M_bound · h²`.

The bound differs from Butcher's stated form (`∑ i |i α_i − β_i|`)
because the textbook decomposition has a typo; see the §406 block
header and `.prover-state/issues/lem_406B_textbook_check.md`. -/
theorem LinearMultistepMethod.localTruncationError_bound {k : ℕ}
    (M : LinearMultistepMethod k) (hcons : M.IsConsistent)
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {y : ℝ → ℝ}
    (hy_C1 : ContDiff ℝ 1 y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (hf_y_bound : ∀ t, |f (y t)| ≤ M_bound)
    (x h : ℝ) (hh : 0 ≤ h) :
    |M.localTruncationError y x h|
      ≤ ((1/2) * (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
          + ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|)
        * L * M_bound * h^2 := by
  rw [M.localTruncationError_decomposition hcons y x h]
  refine (abs_add_le _ _).trans ?_
  have hα := localTruncationError_α_sum_bound M hL hM hf_lip
               hy_C1 hy_ode hf_y_bound x h hh
  have hβ := localTruncationError_β_sum_bound M hL hM hf_lip
               hy_C1 hy_ode hf_y_bound x h hh
  have habs_h : |h * (∑ i : Fin k, M.β i.succ
                  * (deriv y x - deriv y (x - ((i.val + 1 : ℕ) : ℝ) * h)))|
                = h * |∑ i : Fin k, M.β i.succ
                  * (deriv y x - deriv y (x - ((i.val + 1 : ℕ) : ℝ) * h))| := by
    rw [abs_mul, abs_of_nonneg hh]
  rw [habs_h]
  refine le_trans (add_le_add hα (mul_le_mul_of_nonneg_left hβ hh)) ?_
  apply le_of_eq
  ring

/-! ## §406 — Global error bound for linear multistep methods (thm:406C)

Butcher §406, p. 347. Quoting `entities/thm_406C.json`:

> Let `n` denote the vector `n = y(x_n) − y_n`. Then for `h_0`
> sufficiently small so that `h_0 |β_0| L < 1` and `h < h_0`, there
> exist constants `C` and `D` such that
>   `‖n − Σ_{i=1}^k α_i n_{−i}‖ ≤ C h max_{i=1}^k ‖n_{−i}‖ + D h^2`. (406c)

Butcher's proof outline (§406, p. 347): the value of
`n − Σ α_i n_{−i} − h Σ β_i (f(y(x_{n-i})) − f(y_{n-i}))` is the
difference of two terms — the first is bounded by `D · h^2` (by
`lem:406B`) and the second is zero (by the LMM recurrence). Hence
`n − Σ α_i n_{−i} = T_1 + T_2 + T_3`, with
- `T_1 = h β_0 (f(y(x_n)) − f(y_n))`, bounded by `h L |β_0| · ‖n_n‖`
- `T_2 = h Σ_{i=1}^k β_i (f(y(x_{n-i})) − f(y_{n-i}))`,
  bounded by `h L Σ |β_i| · max ‖n_{-i}‖`
- `T_3 = L(y, x_n, h)`, bounded by `D h^2` via `lem:406B`.

Cycle 044 formalises the per-term bound `|T_1 + T_2 + T_3|` directly,
**before** Butcher's `(1 − h L |β_0|)` inversion that absorbs `T_1`
into the LHS. The full (406c) form requires the additional `h L |β_0| < 1`
hypothesis and is deferred to a corollary in a later cycle.

**Faithfulness flag.** Sub-lemma A's algebraic identity (the discrete
analogue of (406d)) matches Butcher's textbook decomposition
coefficient-by-coefficient. The cycle-044 main theorem keeps `T_1`
explicit on the RHS (i.e. the bound
`h L |β_0| · |n_n| + h L Σ |β_i| · max + D h^2`) — the textbook
form `C h · max + D h^2` follows from this by a `(1 − h L |β_0|)`
inversion (Butcher's "use (406d) twice"), to be added as a corollary
in cycle 045+.

**Sign-convention prerequisite (cycle 044 fix).** Cycle 044 audited
the existing `IsLMMSolution` predicate and discovered that the
right-hand side carried the wrong sign relative to Butcher's
recurrence (400b)
`y_n = α_1 y_{n-1} + ⋯ + α_k y_{n-k} + h Σ β_i f(x_{n-i}, y_{n-i})`.
The fix: negate the RHS to `-h · Σ β_i f`, so that with `α_0 = -1`
the leading-term cancellation gives Butcher's recurrence in textbook
form. Sanity check: explicit Euler now produces
`Y(m+1) = Y(m) + h f(Y(m))` (the textbook forward Euler step).
See the `IsLMMSolution` docstring for details. -/

/-- The global error of an LMM iterate `Y` against the exact solution
`yex` of the IVP at grid point `n` (i.e. real point `x₀ + n*h`).

Kept as a plain `def` (not a structure-instance method) so it can be
unfolded freely in algebraic manipulations. -/
def globalError (yex : ℝ → ℝ) (Y : ℕ → ℝ) (x₀ h : ℝ) (n : ℕ) : ℝ :=
  yex (x₀ + (n : ℝ) * h) - Y n

/-- Sub-lemma A (Butcher's algebraic identity (406d)): the global
error vector `n_n - Σ α_i n_{n-i}` equals the LTE at `x_n` plus the
two `f`-difference terms `T_1` and `T_2`.

This is purely algebraic — it follows from unfolding
`localTruncationError`, applying `IsLMMSolution` (re-indexed via
`hn : k ≤ n`), and combining with `α_zero = -1`. -/
lemma globalError_decomposition {k : ℕ} (M : LinearMultistepMethod k)
    {f : ℝ → ℝ} {yex : ℝ → ℝ} {Y : ℕ → ℝ} {x₀ h : ℝ}
    (hyex_ode : ∀ t, deriv yex t = f (yex t))
    (hY : M.IsLMMSolution h x₀ (fun _ y => f y) Y)
    (n : ℕ) (hn : k ≤ n) :
    globalError yex Y x₀ h n
      - ∑ i : Fin k, M.α i.succ * globalError yex Y x₀ h (n - (i.val + 1))
      = h * M.β 0 * (f (yex (x₀ + (n : ℝ) * h)) - f (Y n))
        + h * (∑ i : Fin k, M.β i.succ
                * (f (yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h))
                   - f (Y (n - (i.val + 1)))))
        + M.localTruncationError yex (x₀ + (n : ℝ) * h) h := by
  -- Re-index: n = m + k for some m : ℕ.
  obtain ⟨m, rfl⟩ : ∃ m, n = m + k := ⟨n - k, (Nat.sub_add_cancel hn).symm⟩
  -- Cast bridge: (m + k - (j+1) : ℕ) : ℝ) equals (m+k:ℝ) - (j+1:ℝ).
  have hjk : ∀ i : Fin k, i.val + 1 ≤ m + k := fun i => by
    have : i.val < k := i.isLt; omega
  have hcast_real : ∀ i : Fin k,
      x₀ + ((m + k : ℕ) : ℝ) * h - ((i.val + 1 : ℕ) : ℝ) * h
        = x₀ + ((m + k - (i.val + 1) : ℕ) : ℝ) * h := fun i => by
    rw [Nat.cast_sub (hjk i)]; push_cast; ring
  -- Convert all deriv yex terms in LTE to f∘yex.
  have hderiv_xn : deriv yex (x₀ + ((m + k : ℕ) : ℝ) * h)
                    = f (yex (x₀ + ((m + k : ℕ) : ℝ) * h)) := hyex_ode _
  have hderiv_shifted : ∀ i : Fin k,
      deriv yex (x₀ + ((m + k : ℕ) : ℝ) * h - ((i.val + 1 : ℕ) : ℝ) * h)
        = f (yex (x₀ + ((m + k - (i.val + 1) : ℕ) : ℝ) * h)) := fun i => by
    rw [hcast_real i]; exact hyex_ode _
  -- Bridge yex application for the y-sum in LTE.
  have hyex_shifted : ∀ i : Fin k,
      yex (x₀ + ((m + k : ℕ) : ℝ) * h - ((i.val + 1 : ℕ) : ℝ) * h)
        = yex (x₀ + ((m + k - (i.val + 1) : ℕ) : ℝ) * h) := fun i => by
    rw [hcast_real i]
  -- LMM equation at m, then peel `i = 0` from both sums.
  have hYm := hY m
  rw [Fin.sum_univ_succ (f := fun i : Fin (k + 1) =>
        M.α i * Y (m + k - i.val))] at hYm
  rw [Fin.sum_univ_succ (f := fun i : Fin (k + 1) =>
        M.β i * (fun _ y => f y) (x₀ + ((m + k - i.val : ℕ) : ℝ) * h)
                                  (Y (m + k - i.val)))] at hYm
  simp only [Fin.val_zero, Nat.sub_zero, M.α_zero, Fin.val_succ] at hYm
  -- Unfold globalError and localTruncationError; then unfold the LTE β-sum.
  unfold globalError LinearMultistepMethod.localTruncationError
  rw [Fin.sum_univ_succ (f := fun i : Fin (k + 1) =>
        M.β i * deriv yex
          (x₀ + ((m + k : ℕ) : ℝ) * h - ((i.val : ℕ) : ℝ) * h))]
  simp only [Fin.val_zero, Nat.cast_zero, zero_mul, sub_zero, Fin.val_succ]
  -- Substitute deriv yex (xn) → f(yex(xn)) for the leading term.
  rw [hderiv_xn]
  -- Convert the yex y-sum and the deriv yex β-sum (i ≥ 1) via the cast bridges.
  rw [show (∑ i : Fin k, M.α i.succ
              * yex (x₀ + ((m + k : ℕ) : ℝ) * h - ((i.val + 1 : ℕ) : ℝ) * h))
        = (∑ i : Fin k, M.α i.succ
              * yex (x₀ + ((m + k - (i.val + 1) : ℕ) : ℝ) * h)) from
      Finset.sum_congr rfl (fun i _ => by rw [hyex_shifted i])]
  rw [show (∑ i : Fin k, M.β i.succ
              * deriv yex
                  (x₀ + ((m + k : ℕ) : ℝ) * h - ((i.val + 1 : ℕ) : ℝ) * h))
        = (∑ i : Fin k, M.β i.succ
              * f (yex (x₀ + ((m + k - (i.val + 1) : ℕ) : ℝ) * h))) from
      Finset.sum_congr rfl (fun i _ => by rw [hderiv_shifted i])]
  -- Distribute the difference-of-sums on both LHS and RHS so linarith can match.
  rw [show (∑ i : Fin k, M.α i.succ
              * (yex (x₀ + ((m + k - (i.val + 1) : ℕ) : ℝ) * h)
                 - Y (m + k - (i.val + 1))))
        = (∑ i : Fin k, M.α i.succ
              * yex (x₀ + ((m + k - (i.val + 1) : ℕ) : ℝ) * h))
          - (∑ i : Fin k, M.α i.succ * Y (m + k - (i.val + 1))) from by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _; ring]
  rw [show (∑ i : Fin k, M.β i.succ
              * (f (yex (x₀ + ((m + k - (i.val + 1) : ℕ) : ℝ) * h))
                 - f (Y (m + k - (i.val + 1)))))
        = (∑ i : Fin k, M.β i.succ
              * f (yex (x₀ + ((m + k - (i.val + 1) : ℕ) : ℝ) * h)))
          - (∑ i : Fin k, M.β i.succ * f (Y (m + k - (i.val + 1)))) from by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _; ring]
  -- Normalise casts of `(m + k : ℕ)` so linarith sees matching atoms.
  push_cast at hYm ⊢
  linarith [hYm]

/-- Sub-lemma B: bound on `T_1 = h β_0 (f a − f b)` via Lipschitz of
`f`. -/
lemma T1_bound {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf_lip : LipschitzWith L.toNNReal f)
    {β₀ : ℝ} (h : ℝ) (hh : 0 ≤ h) (a b : ℝ) :
    |h * β₀ * (f a - f b)| ≤ h * L * |β₀| * |a - b| := by
  have hLip : |f a - f b| ≤ L * |a - b| := by
    have hd := hf_lip.dist_le_mul a b
    rw [Real.dist_eq, Real.dist_eq] at hd
    have hco : ((Real.toNNReal L : ℝ≥0) : ℝ) = L := Real.coe_toNNReal L hL
    rw [hco] at hd
    exact hd
  calc |h * β₀ * (f a - f b)|
      = h * |β₀| * |f a - f b| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hh]
    _ ≤ h * |β₀| * (L * |a - b|) :=
        mul_le_mul_of_nonneg_left hLip (mul_nonneg hh (abs_nonneg _))
    _ = h * L * |β₀| * |a - b| := by ring

/-- Sub-lemma C: bound on `T_2 = h Σ β_i (f a_i − f b_i)` via Lipschitz
of `f` and a uniform bound `Mmax` on `|a_i − b_i|`. -/
lemma T2_bound {k : ℕ} (M : LinearMultistepMethod k)
    {f : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hf_lip : LipschitzWith L.toNNReal f)
    (h : ℝ) (hh : 0 ≤ h)
    (a : Fin k → ℝ) (b : Fin k → ℝ) (Mmax : ℝ)
    (hMmax : ∀ i : Fin k, |a i - b i| ≤ Mmax) (hMmax0 : 0 ≤ Mmax) :
    |h * ∑ i : Fin k, M.β i.succ * (f (a i) - f (b i))|
      ≤ h * L * (∑ i : Fin k, |M.β i.succ|) * Mmax := by
  -- Step 1: pull h out using h ≥ 0.
  rw [abs_mul, abs_of_nonneg hh]
  -- Step 2: triangle inequality on sum, then per-summand Lipschitz bound.
  have hsum_bound :
      |∑ i : Fin k, M.β i.succ * (f (a i) - f (b i))|
        ≤ (∑ i : Fin k, |M.β i.succ|) * (L * Mmax) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [show (∑ i : Fin k, |M.β i.succ|) * (L * Mmax)
            = ∑ i : Fin k, |M.β i.succ| * (L * Mmax) from
          by rw [Finset.sum_mul]]
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul]
    have hLip : |f (a i) - f (b i)| ≤ L * |a i - b i| := by
      have hd := hf_lip.dist_le_mul (a i) (b i)
      rw [Real.dist_eq, Real.dist_eq] at hd
      have hco : ((Real.toNNReal L : ℝ≥0) : ℝ) = L := Real.coe_toNNReal L hL
      rw [hco] at hd
      exact hd
    have hLM : |f (a i) - f (b i)| ≤ L * Mmax := by
      calc |f (a i) - f (b i)|
          ≤ L * |a i - b i| := hLip
        _ ≤ L * Mmax := mul_le_mul_of_nonneg_left (hMmax i) hL
    exact mul_le_mul_of_nonneg_left hLM (abs_nonneg _)
  -- Step 3: pull through h.
  calc h * |∑ i : Fin k, M.β i.succ * (f (a i) - f (b i))|
      ≤ h * ((∑ i : Fin k, |M.β i.succ|) * (L * Mmax)) :=
        mul_le_mul_of_nonneg_left hsum_bound hh
    _ = h * L * (∑ i : Fin k, |M.β i.succ|) * Mmax := by ring

/-- Sub-lemma D: bound on `T_3 = L(yex, x, h)` — direct application
of `lem:406B`. -/
lemma T3_bound {k : ℕ} (M : LinearMultistepMethod k)
    (hcons : M.IsConsistent)
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {y : ℝ → ℝ}
    (hy_C1 : ContDiff ℝ 1 y)
    (hy_ode : ∀ t, deriv y t = f (y t))
    (hf_y_bound : ∀ t, |f (y t)| ≤ M_bound)
    (x h : ℝ) (hh : 0 ≤ h) :
    |M.localTruncationError y x h|
      ≤ ((1/2) * (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
          + ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|)
        * L * M_bound * h^2 :=
  M.localTruncationError_bound hcons hL hM hf_lip
    hy_C1 hy_ode hf_y_bound x h hh

/-- Butcher Theorem 406C (p. 347, partial form): for an LMM solution
`Y` of the IVP `y' = f(y)` with `f` Lipschitz, the global error
recurrence satisfies the per-term bound

  `|n_n - Σ α_i n_{n-i}|
    ≤ h L |β_0| · |n_n| + h L Σ |β_{i+1}| · Mmax + D · h^2`

where `D` is the LTE coefficient from `lem:406B` and `Mmax` bounds
the per-step error history `max_{i=1..k} |n_{n-i}|`. The textbook
(406c) form `‖n - Σ α n_{-i}‖ ≤ C h · max + D h^2` follows from this
by a `(1 − h L |β_0|)`-inversion under the additional smallness
hypothesis `h L |β_0| < 1`; deferred to a corollary in a later cycle. -/
theorem LinearMultistepMethod.globalError_recurrence_bound
    {k : ℕ} (M : LinearMultistepMethod k) (hcons : M.IsConsistent)
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {yex : ℝ → ℝ}
    (hyex_C1 : ContDiff ℝ 1 yex)
    (hyex_ode : ∀ t, deriv yex t = f (yex t))
    (hf_yex_bound : ∀ t, |f (yex t)| ≤ M_bound)
    {Y : ℕ → ℝ} {x₀ h : ℝ}
    (hh : 0 ≤ h)
    (hY : M.IsLMMSolution h x₀ (fun _ y => f y) Y)
    (n : ℕ) (hn : k ≤ n)
    (Mmax : ℝ) (hMmax0 : 0 ≤ Mmax)
    (hMmax : ∀ i : Fin k,
              |yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h)
                - Y (n - (i.val + 1))| ≤ Mmax) :
    |yex (x₀ + (n : ℝ) * h) - Y n
        - ∑ i : Fin k, M.α i.succ
            * (yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h)
                - Y (n - (i.val + 1)))|
      ≤ h * L * |M.β 0| * |yex (x₀ + (n : ℝ) * h) - Y n|
        + h * L * (∑ i : Fin k, |M.β i.succ|) * Mmax
        + ((1/2) * (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
            + ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|)
          * L * M_bound * h^2 := by
  -- Apply sub-lemma A to rewrite LHS as |T_1 + T_2 + T_3|.
  have hA := globalError_decomposition M hyex_ode hY n hn
  unfold globalError at hA
  rw [hA]
  -- Triangle inequality: |T_1 + T_2 + T_3| ≤ |T_1| + |T_2| + |T_3|.
  refine (abs_add_le _ _).trans ?_
  refine le_trans (add_le_add (abs_add_le _ _) le_rfl) ?_
  -- Per-term bounds via sub-lemmas B, C, T3 (= lem:406B).
  have hB := T1_bound (β₀ := M.β 0) hL hf_lip h hh
              (yex (x₀ + (n : ℝ) * h)) (Y n)
  have hC := T2_bound M hL hf_lip h hh
              (fun i : Fin k => yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h))
              (fun i : Fin k => Y (n - (i.val + 1)))
              Mmax hMmax hMmax0
  have hD := T3_bound M hcons hL hM hf_lip hyex_C1 hyex_ode hf_yex_bound
              (x₀ + (n : ℝ) * h) h hh
  -- Combine: |T_1| + |T_2| + |T_3| ≤ goal RHS.
  exact le_trans (add_le_add (add_le_add hB hC) hD) (le_of_eq (by ring))

/-- Butcher Theorem 406C (p. 347, textbook form): under the smallness
hypothesis `h L |β_0| < 1` (Butcher's "for `h_0` sufficiently small so
that `h_0 |β_0| L < 1` and `h < h_0`"), the per-term bound from
`globalError_recurrence_bound` can be absorbed via the
`(1 − h L |β_0|)`-inversion to yield the textbook form (406c)

  `|n_n − Σ α_i n_{n-i}|  ≤  C_h · h · max |n_{n-i}|  +  D_h · h²`

with explicit `h`-dependent constants. The proof proceeds by Butcher's
"use (406d) twice" recipe: bound `|n_n|` by `|Σ α_i n_{n-i}| + |LHS|`
(reverse triangle), substitute into the per-term bound, solve the
resulting algebraic inequality `(1 − h L |β_0|) · A ≤ c · B + K`
(where `c = h L |β_0|`, `B ≤ Σ|α_i| · Mmax`), and divide through.

The textbook abstracts `C` and `D` as unspecified constants depending
on `h_0`. Our Lean form is strictly tighter (explicit `h`-dependent
constants), and trivially implies the textbook constants form when
`h ≤ h_0` and we take constants at `h_0`. -/
theorem LinearMultistepMethod.globalError_recurrence_bound_textbook
    {k : ℕ} (M : LinearMultistepMethod k) (hcons : M.IsConsistent)
    {f : ℝ → ℝ} {L M_bound : ℝ}
    (hL : 0 ≤ L) (hM : 0 ≤ M_bound)
    (hf_lip : LipschitzWith L.toNNReal f)
    {yex : ℝ → ℝ}
    (hyex_C1 : ContDiff ℝ 1 yex)
    (hyex_ode : ∀ t, deriv yex t = f (yex t))
    (hf_yex_bound : ∀ t, |f (yex t)| ≤ M_bound)
    {Y : ℕ → ℝ} {x₀ h : ℝ}
    (hh : 0 ≤ h)
    (hsmall : h * L * |M.β 0| < 1)
    (hY : M.IsLMMSolution h x₀ (fun _ y => f y) Y)
    (n : ℕ) (hn : k ≤ n)
    (Mmax : ℝ) (hMmax0 : 0 ≤ Mmax)
    (hMmax : ∀ i : Fin k,
              |yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h)
                - Y (n - (i.val + 1))| ≤ Mmax) :
    |yex (x₀ + (n : ℝ) * h) - Y n
        - ∑ i : Fin k, M.α i.succ
            * (yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h)
                - Y (n - (i.val + 1)))|
      ≤ (h * L * (|M.β 0| * (∑ i : Fin k, |M.α i.succ|)
                  + ∑ i : Fin k, |M.β i.succ|)
            / (1 - h * L * |M.β 0|)) * Mmax
        + ((1/2) * (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
            + ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|)
              * L * M_bound * h^2
            / (1 - h * L * |M.β 0|) := by
  -- Apply the cycle-044 per-term bound.
  have hA := M.globalError_recurrence_bound hcons hL hM hf_lip
                hyex_C1 hyex_ode hf_yex_bound hh hY n hn Mmax hMmax0 hMmax
  -- Reverse triangle: |n_n| ≤ |Σ α (yex − Y)| + A.
  have h_abs_nn :
      |yex (x₀ + (n : ℝ) * h) - Y n|
        ≤ |∑ i : Fin k, M.α i.succ
              * (yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h)
                  - Y (n - (i.val + 1)))|
          + |yex (x₀ + (n : ℝ) * h) - Y n
              - ∑ i : Fin k, M.α i.succ
                  * (yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h)
                      - Y (n - (i.val + 1)))| := by
    have hrw : yex (x₀ + (n : ℝ) * h) - Y n
              = (∑ i : Fin k, M.α i.succ
                  * (yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h)
                      - Y (n - (i.val + 1))))
                + (yex (x₀ + (n : ℝ) * h) - Y n
                    - ∑ i : Fin k, M.α i.succ
                        * (yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h)
                            - Y (n - (i.val + 1)))) := by ring
    calc |yex (x₀ + (n : ℝ) * h) - Y n|
        = |(∑ i : Fin k, M.α i.succ
                * (yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h)
                    - Y (n - (i.val + 1))))
            + (yex (x₀ + (n : ℝ) * h) - Y n
                - ∑ i : Fin k, M.α i.succ
                    * (yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h)
                        - Y (n - (i.val + 1))))| := by rw [← hrw]
      _ ≤ _ := abs_add_le _ _
  -- Bound |Σ α (yex − Y)| by (Σ|α|) · Mmax.
  have h_abs_sum :
      |∑ i : Fin k, M.α i.succ
          * (yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h)
              - Y (n - (i.val + 1)))|
        ≤ (∑ i : Fin k, |M.α i.succ|) * Mmax := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hMmax i) (abs_nonneg _)
  -- Smallness: 1 − c > 0.
  have h_one_sub_c_pos : 0 < 1 - h * L * |M.β 0| := by linarith
  -- c ≥ 0 (needed to multiply the reverse-triangle through).
  have hc_nn : 0 ≤ h * L * |M.β 0| :=
    mul_nonneg (mul_nonneg hh hL) (abs_nonneg _)
  -- Σ|α| ≥ 0.
  have hsum_alpha_nn : 0 ≤ ∑ i : Fin k, |M.α i.succ| :=
    Finset.sum_nonneg (fun i _ => abs_nonneg _)
  -- Set up shorthands as `let`s so linarith can chain them.
  set A : ℝ :=
      |yex (x₀ + (n : ℝ) * h) - Y n
        - ∑ i : Fin k, M.α i.succ
            * (yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h)
                - Y (n - (i.val + 1)))| with hA_def
  set B : ℝ :=
      |∑ i : Fin k, M.α i.succ
          * (yex (x₀ + ((n - (i.val + 1) : ℕ) : ℝ) * h)
              - Y (n - (i.val + 1)))| with hB_def
  set N : ℝ := |yex (x₀ + (n : ℝ) * h) - Y n| with hN_def
  set c : ℝ := h * L * |M.β 0| with hc_def
  set Sα : ℝ := ∑ i : Fin k, |M.α i.succ| with hSα_def
  set T2coef : ℝ := h * L * (∑ i : Fin k, |M.β i.succ|) with hT2c_def
  set Dh2 : ℝ :=
      ((1/2) * (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
        + ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|)
        * L * M_bound * h^2 with hD_def
  -- Step 1: per-term bound (rephrased with shorthands).
  have h_step1 : A ≤ c * N + T2coef * Mmax + Dh2 := hA
  -- Step 2: c · N ≤ c · B + c · A.
  have h_step2 : c * N ≤ c * B + c * A := by
    have := mul_le_mul_of_nonneg_left h_abs_nn hc_nn
    linarith
  -- Step 3: (1 - c) · A ≤ c · B + T2coef · Mmax + Dh2.
  have h_step3 :
      (1 - c) * A ≤ c * B + T2coef * Mmax + Dh2 := by
    nlinarith [h_step1, h_step2]
  -- Step 4: bound c · B by c · Sα · Mmax (since c ≥ 0).
  have h_step4 :
      (1 - c) * A ≤ c * Sα * Mmax + T2coef * Mmax + Dh2 := by
    have hcB : c * B ≤ c * (Sα * Mmax) :=
      mul_le_mul_of_nonneg_left h_abs_sum hc_nn
    nlinarith [h_step3, hcB]
  -- Step 5: divide by (1 − c) (positive) to get the goal.
  rw [show (h * L * (|M.β 0| * (∑ i : Fin k, |M.α i.succ|)
                + ∑ i : Fin k, |M.β i.succ|)
            / (1 - h * L * |M.β 0|)) * Mmax
        + ((1/2) * (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ)^2 * |M.α i.succ|)
            + ∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * |M.β i.succ|)
              * L * M_bound * h^2
            / (1 - h * L * |M.β 0|)
        = (c * Sα * Mmax + T2coef * Mmax + Dh2) / (1 - c) from by
    simp only [hc_def, hSα_def, hT2c_def, hD_def]; ring]
  rw [le_div_iff₀ h_one_sub_c_pos]
  linarith [h_step4]

/-! ### Discrete Grönwall (helper for thm:406D)

Butcher §406D proves convergence of stable consistent linear multistep
methods by combining the textbook recurrence bound (406c, closed in
cycle 045 as `globalError_recurrence_bound_textbook`) with the
closed-form solution of a linear recurrence and a discrete Grönwall
inequality. Equation (406h) on p. 347 of Butcher (3rd ed.) is the
recurrence

  `u_n ≤ a + b·h·k · Σ_{i=1}^{n−1} u_i + c · h² · n`

whose closed-form bound is

  `u_n ≤ exp(b·k·n·h) · a + (exp(b·k·n·h) − 1) · c·h/(b·k)`.

We package this as a standalone helper. It is **not** a Butcher entity
in the extraction registry (it is the auxiliary inequality between the
hypotheses of (406h) and the exponential bound used in the proof of
the convergence theorem), so no `entities/<id>.json` applies. -/

/-- Closed-form bound `u n ≤ a · (1+b·h·k)^n + (c·h/(b·k)) · ((1+b·h·k)^n - 1)`,
    proved by strong induction on `n` from the recurrence hypothesis.

    The inductive step uses the geometric sum identity
    `(Σ i ∈ range n, r^i)·(r-1) = r^n - 1` (`geom_sum_mul`) with `r = 1+x`
    where `x := b·h·k`. The key cancellation is `(c·h/(b·k))·x = c·h²`,
    which makes the `c·h²·n` term and the geometric correction collapse. -/
private lemma _v_geom
    {u : ℕ → ℝ} {a b c h : ℝ} {k : ℕ}
    (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 ≤ c) (hh : 0 ≤ h) (hk : 0 < k)
    (hu0 : u 0 ≤ a)
    (hu_rec : ∀ n, 1 ≤ n →
      u n ≤ a + b * h * (k : ℝ) * (∑ i ∈ Finset.Ico 1 n, u i)
              + c * h^2 * (n : ℝ)) :
    ∀ n, u n ≤ a * (1 + b * h * (k : ℝ))^n
              + (c * h / (b * (k : ℝ)))
                  * ((1 + b * h * (k : ℝ))^n - 1) := by
  -- Notation.
  set x : ℝ := b * h * (k : ℝ) with hx_def
  set B : ℝ := c * h / (b * (k : ℝ)) with hB_def
  -- Setup non-negativity / equalities.
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hbk_pos : (0 : ℝ) < b * (k : ℝ) := mul_pos hb hk_pos
  have hbk_ne : b * (k : ℝ) ≠ 0 := ne_of_gt hbk_pos
  have hx_nn : 0 ≤ x := show 0 ≤ b * h * (k : ℝ) by positivity
  have hB_nn : 0 ≤ B :=
    show 0 ≤ c * h / (b * (k : ℝ)) by positivity
  have hr_nn : 0 ≤ 1 + x := by linarith
  have hBx_eq : B * x = c * h^2 := by
    show c * h / (b * (k : ℝ)) * (b * h * (k : ℝ)) = c * h^2
    field_simp
  have hax_nn : 0 ≤ a * x := mul_nonneg ha hx_nn
  -- Strong induction on n.
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ =>
      simp only [pow_zero, mul_one, sub_self, mul_zero, add_zero]
      linarith
    | n+1, ih =>
      -- Apply rec at n+1.
      have hn1 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le _)
      have hrec : u (n+1) ≤ a + x * (∑ i ∈ Finset.Ico 1 (n+1), u i)
                          + c * h^2 * ((n+1 : ℕ) : ℝ) := hu_rec (n+1) hn1
      -- IH gives, for each i ∈ Ico 1 (n+1), the closed-form bound on u i.
      have hSum_le_C :
          ∑ i ∈ Finset.Ico 1 (n+1), u i
            ≤ ∑ i ∈ Finset.Ico 1 (n+1),
                (a * (1+x)^i + B * ((1+x)^i - 1)) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_Ico] at hi
        exact ih i hi.2
      -- Σ C(i) = (a+B) · Σ(1+x)^i - B · n  (since |Ico 1 (n+1)| = n).
      have hSum_C_eq :
          ∑ i ∈ Finset.Ico 1 (n+1), (a * (1+x)^i + B * ((1+x)^i - 1))
          = (a + B) * (∑ i ∈ Finset.Ico 1 (n+1), (1+x)^i) - B * (n : ℝ) := by
        have hrw : ∀ i, a * (1+x)^i + B * ((1+x)^i - 1)
                        = (a + B) * (1+x)^i - B := by
          intro i; ring
        simp_rw [hrw]
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const]
        rw [Nat.card_Ico, Nat.add_sub_cancel, nsmul_eq_mul]
        ring
      -- Geometric sum: x · Σ_{Ico 1 (n+1)} (1+x)^i = (1+x)^(n+1) - (1+x).
      have hgeom_sum :
          x * (∑ i ∈ Finset.Ico 1 (n+1), (1+x)^i)
            = (1+x)^(n+1) - (1+x) := by
        rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
        -- ∑_{j ∈ range n} (1+x)^(1+j) = (1+x) · ∑_{j ∈ range n} (1+x)^j
        have hshift :
            ∀ j, ((1 : ℝ) + x)^(1 + j) = (1+x) * (1+x)^j := by
          intro j; rw [pow_add, pow_one]
        simp_rw [hshift]
        rw [← Finset.mul_sum]
        -- x · ((1+x) · Σ) = (1+x) · (Σ · x) = (1+x) · ((1+x)^n - 1) = (1+x)^(n+1) - (1+x)
        have hgsm : (∑ i ∈ Finset.range n, ((1:ℝ)+x)^i) * x
                      = (1+x)^n - 1 := by
          have := geom_sum_mul ((1:ℝ)+x) n
          have heq : ((1:ℝ) + x) - 1 = x := by ring
          rw [heq] at this; exact this
        have : x * ((1+x) * (∑ i ∈ Finset.range n, ((1:ℝ)+x)^i))
             = (1+x) * ((∑ i ∈ Finset.range n, ((1:ℝ)+x)^i) * x) := by ring
        rw [this, hgsm, pow_succ]; ring
      -- Set short names for the sums.
      set S : ℝ := ∑ i ∈ Finset.Ico 1 (n+1), u i with hS_def
      set Sg : ℝ := ∑ i ∈ Finset.Ico 1 (n+1), (1+x)^i with hSg_def
      have hS_bnd : S ≤ (a + B) * Sg - B * (n : ℝ) :=
        hSum_le_C.trans hSum_C_eq.le
      have hSg_geom : x * Sg = (1+x)^(n+1) - (1+x) := hgeom_sum
      -- Multiply the sum bound by x ≥ 0.
      have h_xS : x * S ≤ x * ((a + B) * Sg - B * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hS_bnd hx_nn
      -- ch²·(n+1) = B·x·(n+1) = B·x·n + B·x.
      have hcheq_n :
          c * h^2 * ((n+1 : ℕ) : ℝ) = B * x * (n : ℝ) + B * x := by
        have := hBx_eq
        push_cast
        nlinarith [this]
      -- Combine: u(n+1) ≤ a + x·((a+B)Sg - Bn) + Bxn + Bx
      --                = a + (a+B)·(xSg) + Bx
      --                = a + (a+B)·((1+x)^(n+1) - (1+x)) + Bx
      --                = a(1+x)^(n+1) + B((1+x)^(n+1) - 1) - ax.
      -- Algebraic identity to chain through.
      have h_alg :
          a + (a + B) * ((1+x)^(n+1) - (1+x)) + B * x
            = a * (1+x)^(n+1) + B * ((1+x)^(n+1) - 1) - a * x := by ring
      -- u(n+1) ≤ a + (a+B)·((1+x)^(n+1) - (1+x)) + Bx
      have h_intermediate :
          u (n+1) ≤ a + (a + B) * ((1+x)^(n+1) - (1+x)) + B * x := by
        -- u(n+1) ≤ a + xS + ch²(n+1)
        --       ≤ a + x·((a+B)·Sg - Bn) + Bx·n + Bx
        --       = a + (a+B)·(xSg) - Bxn + Bxn + Bx
        --       = a + (a+B)·((1+x)^(n+1) - (1+x)) + Bx
        nlinarith [hrec, h_xS, hcheq_n, hSg_geom]
      linarith [h_intermediate, h_alg, hax_nn]

/-- `(1 + b·h·k)^n ≤ exp(b·k·n·h)`, as needed for the closed-form
    Grönwall bound. Combines `Real.add_one_le_exp`, `pow_le_pow_left₀`,
    and `Real.exp_nat_mul`. -/
private lemma _one_add_pow_le_exp
    (b h : ℝ) (k n : ℕ) (hb : 0 ≤ b) (hh : 0 ≤ h) :
    (1 + b * h * (k : ℝ))^n ≤ Real.exp (b * (k : ℝ) * (n : ℝ) * h) := by
  have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hbhk_nn : 0 ≤ b * h * (k : ℝ) := by positivity
  have hone_add_nn : 0 ≤ 1 + b * h * (k : ℝ) := by linarith
  -- 1 + bhk ≤ exp(bhk)
  have h1 : 1 + b * h * (k : ℝ) ≤ Real.exp (b * h * (k : ℝ)) := by
    have := Real.add_one_le_exp (b * h * (k : ℝ)); linarith
  -- (1 + bhk)^n ≤ (exp bhk)^n
  have h2 : (1 + b * h * (k : ℝ))^n ≤ (Real.exp (b * h * (k : ℝ)))^n :=
    pow_le_pow_left₀ hone_add_nn h1 n
  -- (exp bhk)^n = exp(n · bhk) = exp(b·k·n·h)
  have h3 : (Real.exp (b * h * (k : ℝ)))^n
              = Real.exp (b * (k : ℝ) * (n : ℝ) * h) := by
    rw [← Real.exp_nat_mul]
    congr 1; ring
  linarith [h2, h3.le, h3.ge]

/-- **Discrete Grönwall (Butcher equation (406h) closed form, §406D, p. 347).**
Suppose a non-negative sequence `u : ℕ → ℝ` satisfies, for some
non-negative constants `a, c, h ≥ 0`, `b > 0`, `k > 0`, and every
`n ≥ 1`,

  `u n ≤ a + b·h·k · (Σ i ∈ Ico 1 n, u i) + c·h² · n`,

with `u 0 ≤ a`. Then for every `n`,

  `u n ≤ exp(b·k·n·h) · a + (exp(b·k·n·h) − 1) · c·h/(b·k)`.

Butcher's auxiliary sequence (406h) is exactly this with `a = φ(h)`,
`b = ΘC`, `c = ΘD`. Hypothesis `b > 0` is faithful to the textbook
since `Θ ≥ |θ_0| = 1 > 0` (`Section141.theta_zero`). -/
lemma discrete_gronwall_exp_bound
    (u : ℕ → ℝ) (a b c h : ℝ) (k : ℕ)
    (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 ≤ c) (hh : 0 ≤ h) (hk : 0 < k)
    (hu0 : u 0 ≤ a)
    (hu_rec : ∀ n, 1 ≤ n →
      u n ≤ a + b * h * (k : ℝ) * (∑ i ∈ Finset.Ico 1 n, u i)
              + c * h^2 * (n : ℝ))
    (n : ℕ) :
    u n ≤ Real.exp (b * (k : ℝ) * (n : ℝ) * h) * a
            + (Real.exp (b * (k : ℝ) * (n : ℝ) * h) - 1)
                * (c * h / (b * (k : ℝ))) := by
  -- Step 1: closed-form bound u n ≤ a·(1+x)^n + B·((1+x)^n - 1).
  have hgeom := _v_geom (u := u) (a := a) (b := b) (c := c) (h := h) (k := k)
                        ha hb hc hh hk hu0 hu_rec n
  -- Step 2: (1+x)^n ≤ exp(b·k·n·h).
  have hexp := _one_add_pow_le_exp b h k n hb.le hh
  -- Step 3: combine. Set up non-negativity bounds.
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hbk_pos : (0 : ℝ) < b * (k : ℝ) := mul_pos hb hk_pos
  have hB_nn : 0 ≤ c * h / (b * (k : ℝ)) :=
    div_nonneg (mul_nonneg hc hh) hbk_pos.le
  have hx_nn : 0 ≤ b * h * (k : ℝ) := by positivity
  have hr_nn : 0 ≤ 1 + b * h * (k : ℝ) := by linarith
  have hpow_nn : 0 ≤ (1 + b * h * (k : ℝ))^n := pow_nonneg hr_nn _
  -- a · (1+x)^n ≤ a · exp(...).
  have h1 : a * (1 + b * h * (k : ℝ))^n
              ≤ a * Real.exp (b * (k : ℝ) * (n : ℝ) * h) :=
    mul_le_mul_of_nonneg_left hexp ha
  -- B · ((1+x)^n - 1) ≤ B · (exp(...) - 1).
  have h2 : (c * h / (b * (k : ℝ))) * ((1 + b * h * (k : ℝ))^n - 1)
              ≤ (c * h / (b * (k : ℝ)))
                  * (Real.exp (b * (k : ℝ) * (n : ℝ) * h) - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hB_nn
  -- Combine.
  linarith [hgeom, h1, h2,
            mul_comm a (Real.exp (b * (k : ℝ) * (n : ℝ) * h)),
            mul_comm (c * h / (b * (k : ℝ)))
              (Real.exp (b * (k : ℝ) * (n : ℝ) * h) - 1)]

/-! ### §406D infrastructure: θ-sequence boundedness

Butcher's proof of `thm:406D` (p. 347) extracts `Θ = sup_{i ≥ 1} |θ_i|`
from the bounded-θ remark. We use the slightly stronger `IsStable`
predicate (every homogeneous solution bounded), giving boundedness of
`θ` directly without relying on `IsConvergent` (which is currently a
predicate, not a conclusion, in our encoding).

The two helpers here are *connector* lemmas — they bridge `Section141.theta`
(the canonical scalar `θ`-sequence) with `Section404`'s LMM-level
`IsHomogeneousSolution` predicate. They are not Butcher entities in the
extraction registry.
-/

open OpenMath.Chapter1.Section141 in
/-- The fundamental θ-sequence of an LMM (`Section141.theta` applied to
the LMM's tail-coefficient vector `M.α ∘ Fin.succ`) satisfies the
homogeneous recurrence (403a) of `M`.

The two recurrences match because:

* `Section141.theta_succ` gives, for `n + 1 ≥ 1`,
    `θ(n+1) = Σ_{j : Fin k} if j.val ≤ n then α_{j+1} · θ(n - j.val) else 0`,
* `IsHomogeneousSolution` requires
    `y(m + k) = Σ_{i : Fin k} M.α i.succ · y(m + k - (i.val + 1))`.

Substituting `m + k = n + 1` (so `n = m + k - 1`) and noting that for
`m ≥ 0`, `j : Fin k` gives `j.val < k ≤ k + m = n + 1`, so the
conditional always fires; `n - j.val = m + k - (j.val + 1)`.

The hypothesis `0 < k` is required because `IsHomogeneousSolution` for
`k = 0` reduces to `∀ m, y m = 0` (empty `Fin 0` sum), but
`theta 0 _ 0 = 1 ≠ 0`, so the claim is false in that degenerate case.
Butcher implicitly assumes `k ≥ 1` throughout §141 and §403. -/
theorem theta_isHomogeneousSolution {k : ℕ} (hk : 0 < k)
    (M : LinearMultistepMethod k) :
    M.IsHomogeneousSolution
      (theta k (fun i : Fin k => M.α i.succ)) := by
  intro m
  set α : Fin k → ℝ := fun i => M.α i.succ with hα_def
  -- n + 1 := m + k. Since k ≥ 1, m + k = (m + k - 1) + 1 syntactically.
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  -- Now m + (k' + 1) = (m + k') + 1; apply theta_succ at index m + k'.
  have hsucc :
      theta (k' + 1) α (m + (k' + 1))
        = ∑ j : Fin (k' + 1), if j.val ≤ m + k' then
            α j * theta (k' + 1) α (m + k' - j.val) else 0 := by
    show theta (k' + 1) α ((m + k') + 1) = _
    rw [theta_succ]
  rw [hsucc]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hj : j.val ≤ m + k' := by
    have := j.isLt
    omega
  rw [if_pos hj]
  -- Goal: α j * theta _ _ (m + k' - j.val)
  --       = M.α j.succ * theta _ _ (m + (k'+1) - (j.val + 1))
  have hidx : m + k' - j.val = m + (k' + 1) - (j.val + 1) := by omega
  rw [hidx]

open OpenMath.Chapter1.Section141 in
/-- **Butcher §406D's "Θ exists".** From `M.IsStable`, the θ-sequence
of `M` (in the sense of `Section141`) is uniformly bounded by some
non-negative `Θ`. The non-negativity is obtained via the `max ⬝ 0`
trick, since `IsStable` exposes `∃ C : ℝ` (no sign constraint).

Requires `0 < k` (inherited from `theta_isHomogeneousSolution`). -/
theorem theta_bounded_of_isStable {k : ℕ} (hk : 0 < k)
    (M : LinearMultistepMethod k) (hstab : M.IsStable) :
    ∃ Θ : ℝ, 0 ≤ Θ ∧
      ∀ n, |theta k (fun i : Fin k => M.α i.succ) n| ≤ Θ := by
  obtain ⟨C, hC⟩ := hstab _ (theta_isHomogeneousSolution hk M)
  refine ⟨max C 0, le_max_right _ _, fun n => ?_⟩
  exact (hC n).trans (le_max_left _ _)

/-- **Butcher §406D contraction lemma (helper for `thm:406D`).**
Bounds `|Σ θ_{·} ψ_·|` by `Θ · (C·h·Σ Sε + D·h²·#range)` whenever
each `|ψ i|` is dominated pointwise by `C·h·Sε i + D·h²` and
`|θ i| ≤ Θ`.

The user supplies the per-index "max-of-recent-errors" upper bound
`Sε i` themselves (typically `max_{j<k} |ε(i - j - 1)|`, but we keep
this abstract to avoid bringing `Finset.sup'` into the lemma).

This is the Σ → Σ contraction Butcher invokes in the (406h) recurrence
derivation: the sum over `i ∈ Ico k n` of bounded `|ψ i|` collapses to
a "weighted total error" plus a "linear-in-n h² term".

The `idx` parameter abstracts the index passed to `θ` (typical caller
will use `idx := fun i => n - 1 - i`, matching Butcher's `θ_{n-1-i}`).
This avoids fighting `Nat`-subtraction inside the inequality and makes
the lemma reusable. -/
private lemma sum_theta_psi_contraction
    {Θ C D h : ℝ} (hΘ : 0 ≤ Θ) (_hh : 0 ≤ h)
    (θ : ℕ → ℝ) (hθ : ∀ i, |θ i| ≤ Θ)
    (ψ : ℕ → ℝ) (Sε : ℕ → ℝ)
    (k n : ℕ) (_hkn : k ≤ n)
    (idx : ℕ → ℕ)
    (hψ : ∀ i, k ≤ i → i < n → |ψ i| ≤ C * h * Sε i + D * h^2) :
    |∑ i ∈ Finset.Ico k n, θ (idx i) * ψ i|
      ≤ Θ * C * h * (∑ i ∈ Finset.Ico k n, Sε i)
        + Θ * D * h^2 * ((n - k : ℕ) : ℝ) := by
  -- Step 1: |Σ| ≤ Σ |·|.
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  -- Step 2: pointwise: |θ * ψ| = |θ| * |ψ| ≤ Θ * (C h Sε + D h²).
  have hbound : ∀ i ∈ Finset.Ico k n,
      |θ (idx i) * ψ i| ≤ Θ * (C * h * Sε i + D * h^2) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [abs_mul]
    have h_psi := hψ i hi.1 hi.2
    have h_psi_nn : 0 ≤ |ψ i| := abs_nonneg _
    calc |θ (idx i)| * |ψ i|
        ≤ Θ * |ψ i| :=
          mul_le_mul_of_nonneg_right (hθ (idx i)) h_psi_nn
      _ ≤ Θ * (C * h * Sε i + D * h^2) :=
          mul_le_mul_of_nonneg_left h_psi hΘ
  -- Step 3: sum the bound.
  refine (Finset.sum_le_sum hbound).trans ?_
  -- Step 4: distribute Θ over the (Chx + Dh²) split, then collect.
  have hpoint : ∀ i, Θ * (C * h * Sε i + D * h^2) =
                       Θ * C * h * Sε i + Θ * D * h^2 := by intro; ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Nat.card_Ico, nsmul_eq_mul]
  apply le_of_eq; ring

/-- **Butcher §406D's φ(h) → 0 helper, per index.**
For each `i : Fin k`, the per-index "starting error"
`|yex(x₀ + i·h) - start h i|` tends to 0 as `h → 0`.

Proof: continuity of `yex` at `x₀` (from differentiability) plus
the starting-method limit hypothesis (`start h i → y₀`). Compose
with `Filter.Tendsto.sub` and `Filter.Tendsto.abs`.

Used by: cycle 050's outer-assembly proof of `thm:406D`. The
hypothesis shape (`hyex_diff` over all `x ≥ x₀`, plus `hstart`
per `Fin k`) deliberately mirrors `IsConvergent` line-for-line so
that cycle 050 can destructure `IsConvergent` and feed its
hypotheses here unchanged. -/
private lemma starting_error_each_tendsto_zero
    {k : ℕ} {f : ℝ → ℝ → ℝ} {x₀ y₀ : ℝ} {yex : ℝ → ℝ}
    (hy0 : yex x₀ = y₀)
    (hyex_diff : ∀ x ≥ x₀, HasDerivAt yex (f x (yex x)) x)
    {start : ℝ → Fin k → ℝ}
    (hstart : ∀ i : Fin k,
      Filter.Tendsto (fun h : ℝ => start h i) (nhds 0) (nhds y₀)) :
    ∀ i : Fin k,
      Filter.Tendsto
        (fun h : ℝ => |yex (x₀ + (i.val : ℝ) * h) - start h i|)
        (nhds 0) (nhds 0) := by
  intro i
  have hyex_cont_x₀ : ContinuousAt yex x₀ :=
    (hyex_diff x₀ le_rfl).continuousAt
  have h_curve : Filter.Tendsto (fun h : ℝ => x₀ + (i.val : ℝ) * h)
                                 (nhds 0) (nhds x₀) := by
    have h0 : Filter.Tendsto (fun h : ℝ => x₀ + (i.val : ℝ) * h)
                             (nhds 0)
                             (nhds (x₀ + (i.val : ℝ) * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul Filter.tendsto_id)
    simpa using h0
  have h_yex_curve :
      Filter.Tendsto (fun h : ℝ => yex (x₀ + (i.val : ℝ) * h))
                     (nhds 0) (nhds y₀) := by
    have := hyex_cont_x₀.tendsto.comp h_curve
    simpa [hy0] using this
  have h_diff :
      Filter.Tendsto (fun h : ℝ => yex (x₀ + (i.val : ℝ) * h) - start h i)
                     (nhds 0) (nhds 0) := by
    have := h_yex_curve.sub (hstart i)
    simpa using this
  have := h_diff.abs
  simpa using this

/-- **Butcher §406D's φ(h) → 0 helper, sum form.**
The sum over `Fin k` of starting errors tends to 0 as `h → 0`.

Used by: cycle 050's outer assembly to bound the "starting block"
contribution to the global error (the `φ(h)` term in (406g)). The
sum form matches the shape `discrete_gronwall_exp_bound` consumes
(a sum of recent errors, not a max). -/
private lemma starting_error_sum_tendsto_zero
    {k : ℕ} {f : ℝ → ℝ → ℝ} {x₀ y₀ : ℝ} {yex : ℝ → ℝ}
    (hy0 : yex x₀ = y₀)
    (hyex_diff : ∀ x ≥ x₀, HasDerivAt yex (f x (yex x)) x)
    {start : ℝ → Fin k → ℝ}
    (hstart : ∀ i : Fin k,
      Filter.Tendsto (fun h : ℝ => start h i) (nhds 0) (nhds y₀)) :
    Filter.Tendsto
      (fun h : ℝ =>
        ∑ i : Fin k, |yex (x₀ + (i.val : ℝ) * h) - start h i|)
      (nhds 0) (nhds 0) := by
  have h_each := starting_error_each_tendsto_zero hy0 hyex_diff hstart
  have h_sum :
      Filter.Tendsto
        (fun h : ℝ =>
          ∑ i : Fin k, |yex (x₀ + (i.val : ℝ) * h) - start h i|)
        (nhds 0)
        (nhds (∑ _i ∈ (Finset.univ : Finset (Fin k)), (0 : ℝ))) :=
    tendsto_finset_sum _ (fun i _ => h_each i)
  simpa using h_sum

/-- **Butcher Theorem 406D (p. 347): a stable consistent linear
multistep method is convergent.**

Combines:

* `globalError_recurrence_bound_textbook` (cycle 045) — the (406c)
  per-step bound `|ψ_n| ≤ C h max + D h²`,
* `Section141.linRec_closed_form` (cycle 012) — the `θ`-decomposition
  `ε_n = Σ θ_{n-i} ζ_i + Σ θ_{n-i} ψ_i` (Theorem 141A),
* `theta_bounded_of_isStable` (this cycle) — extracts `Θ` from
  `IsStable`,
* `discrete_gronwall_exp_bound` (cycle 046) — Butcher's (406h)
  exponential closed form,

to conclude `Tendsto (Y_m m - yex x) atTop (𝓝 0)`.

Textbook statement (`entities/thm_406D.json`):
> "A stable consistent linear multistep method is convergent."

The body is `sorry` for cycle 047 — this is the documented scaffold,
locking in the signature and proof outline for cycles 048+. See the
proof-outline section of `task_results/cycle_047.md`. -/
theorem LinearMultistepMethod.stable_consistent_isConvergent
    {k : ℕ} (M : LinearMultistepMethod k)
    (hstab : M.IsStable) (hcons : M.IsConsistent) :
    M.IsConvergent := by
  sorry

end OpenMath.Chapter4.Section404
