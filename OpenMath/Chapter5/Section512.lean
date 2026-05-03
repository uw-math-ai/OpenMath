import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.Basic
import OpenMath.Chapter5.Section510

/-!
# Butcher §512 — Definition of convergence for general linear methods (Definition 512A)

This file introduces the iteration recurrence `IsGLMSolution` and the
textbook predicate `IsConvergent` for general linear methods (GLMs).

## Textbook statement (quoted verbatim from `entities/def_512A.json`)

> A general linear method `(A, U, B, V)`, is *convergent* if for any
> initial value problem
>
>     y'(x) = f(y(x)),    y(x_0) = y_0,
>
> subject to the Lipschitz condition `‖f(y) − f(z)‖ ≤ L ‖y − z‖`,
> there exist a non-zero vector `u ∈ ℝ^r`, and a starting procedure
> `φ : (0, ∞) → ℝ^r`, such that for all `i = 1, 2, …, r`,
> `lim_{h→0} φ_i(h) = u_i y(x_0)`, and such that for any `x > x_0`,
> the sequence of vectors `y^{[n]}`, computed using `n` steps with
> stepsize `h = (x − x_0)/n` and using `y^{[0]} = φ(h)` in each case,
> converges to `u y(x)`.

## Encoding choices

* **Autonomous scalar `f : ℝ → ℝ`.** Butcher writes the IVP as
  `y'(x) = f(y(x))` (no time argument). We follow that literally,
  matching the parallel `def:402A` encoding for LMMs in
  `OpenMath/Chapter4/Section404.lean`. Vectorization to `ℝ^N` is a
  future generalization.
* **Per-step existential `Y` for the internal stages.** The stage
  vector at step `n+1` depends only on the input vector `y_seq n`,
  not on prior stages, so we existentially quantify `Y : Fin s → ℝ`
  inside the `∀ n` rather than over the whole iteration history. This
  parallels the encoding of `LinearMultistepMethod.IsLMMSolution`.
* **Double-indexed iterates `Y : ℕ → ℕ → Fin r → ℝ`.** Outer index
  is the discretization parameter `n` (number of steps; defines the
  stepsize `h_n = (x − x₀) / n`); inner index is the iteration step
  `0, 1, …, n`. This mirrors the LMM template.
* **No `is_convergent_strengthened` clauses.** We deliberately do
  *not* preemptively apply the cycle-068 LMM strengthenings (joint
  Lipschitz, global C¹, uniform `M_bound`). The downstream §513/§514/
  §515 helpers may eventually need these, but per the cycle 091
  strategy, we stay close to the textbook for the definition cycle
  and file an issue when a downstream proof actually fails.

## Non-vacuity

Two sanity helpers establish that `IsGLMSolution` is well-defined and
inhabitable:

* `isGLMSolution_zero_iff` — for `f ≡ 0`, the GLM iteration recurrence
  reduces to the homogeneous V-recurrence
  `y_seq (n+1) i = Σ_j V_{ij} · y_seq n j`.
* `zero_isGLMSolution_zero` — the constantly-zero sequence is a GLM
  iteration of any GLM at any stepsize for `f ≡ 0`.
* `zero_seq_homogeneous_V` — the constantly-zero sequence solves the
  homogeneous V-recurrence for any GLM.

A concrete `IsConvergent` witness for any specific GLM is deferred
to a future cycle that produces `thm:515D` (stability + consistency
⇒ convergence). See `.prover-state/issues/glm_convergence_witness_deferred.md`.
-/

namespace OpenMath.Chapter5.Section510

open Matrix
open scoped BigOperators

/-! ## §512 — Convergence (def:512A) -/

/-- Butcher §511 (recurrence): given an input vector `y_seq n : Fin r → ℝ`,
the GLM step computes internal stages `Y : Fin s → ℝ` and the next
input vector `y_seq (n+1) : Fin r → ℝ` via the equations

  `Y i        = Σ_j A_{ij} · h · f(Y j) + Σ_j U_{ij} · y_seq n j`
  `y_seq (n+1) i = Σ_j B_{ij} · h · f(Y j) + Σ_j V_{ij} · y_seq n j`.

We say `y_seq : ℕ → Fin r → ℝ` is a *GLM iteration* of `M` with
stepsize `h` and autonomous RHS `f` if at every step `n` such a stage
vector `Y` exists. The stage vector is per-step (not over the whole
history) because `Y` at step `n+1` depends only on `y_seq n`.

For `f ≡ 0` this reduces to the homogeneous V-recurrence; see
`isGLMSolution_zero_iff`. -/
def GeneralLinearMethod.IsGLMSolution {s r : ℕ}
    (M : GeneralLinearMethod s r) (h : ℝ) (f : ℝ → ℝ)
    (y_seq : ℕ → Fin r → ℝ) : Prop :=
  ∀ n : ℕ, ∃ Y : Fin s → ℝ,
    (∀ i, Y i = (∑ j, M.A i j * (h * f (Y j)))
                + (∑ j, M.U i j * y_seq n j))
    ∧ (∀ i, y_seq (n + 1) i = (∑ j, M.B i j * (h * f (Y j)))
                              + (∑ j, M.V i j * y_seq n j))

/-- **Definition 512A** (Butcher §512, p. 409) — A general linear
method `(A, U, B, V)` is *convergent* if for any initial value problem

  `y'(x) = f(y(x)),    y(x₀) = y₀`

with `f` Lipschitz, there exist a non-zero vector `u ∈ ℝ^r` and a
starting procedure `φ : ℝ → Fin r → ℝ` with
`lim_{h→0} φ_i(h) = u_i · y(x₀)`, such that for any `x > x₀`, the
sequence of vectors `y^{[n]}`, computed using `n` steps with stepsize
`h = (x − x₀)/n` and starting value `y^{[0]} = φ(h)`, converges to
`u · y(x)` (componentwise).

> "A general linear method `(A, U, B, V)`, is 'convergent' if for any
> initial value problem `y'(x) = f(y(x)), y(x₀) = y₀`, subject to the
> Lipschitz condition `‖f(y) − f(z)‖ ≤ L ‖y − z‖`, there exist a
> non-zero vector `u ∈ ℝ^r`, and a starting procedure
> `φ : (0, ∞) → ℝ^r`, such that for all `i = 1, 2, …, r`,
> `lim_{h→0} φ_i(h) = u_i y(x₀)`, and such that for any `x > x₀`, the
> sequence of vectors `y^{[n]}`, computed using `n` steps with
> stepsize `h = (x − x₀)/n` and using `y^{[0]} = φ(h)` in each case,
> converges to `u y(x)`."
> (Butcher 2008, p. 409.)

The double-indexed `Y : ℕ → ℕ → Fin r → ℝ` represents the family of
iterates: `Y n` is the iteration sequence with discretization
parameter `n` (so stepsize `h_n = (x − x₀)/n`); `Y n m` is the value
at step `m` within that sequence. The conclusion takes the diagonal
`Y n n` (i.e. the value at the final step `n` of the `n`-step run)
and asks for pointwise convergence to `u · y(x)`.

**Critical structural choices** (see file docstring): autonomous `f`,
existential `u` (a property of the method, like a preconsistency
vector), **universal `φ`** (the proof of `thm:513A` constructs its
own bad starting procedure to derive a contradiction, so the
worker must be able to direct φ — see cycle 092 strategy §A and the
LMM precedent at `OpenMath/Chapter4/Section404.lean:333–354`),
`u ≠ 0` per textbook, and **no preemptive strengthening** (joint
Lipschitz / C¹ / uniform M-bound) as in
`is_convergent_strengthened.md` for LMMs. If a future §515 proof
requires those, file a parallel issue at that point.

**Strengthening (cycle 098, faithfulness divergent)**: in addition
to the textbook output-side conclusion `Y n n → u · yex(x)`, this
formalisation requires the consumer to also exhibit an internal-stage
sequence `Y_int : ℕ → Fin s → ℝ` (the stage at the n-th micro-step
of the n-step run, satisfying the GLM stage equation
`Y_int n i = h • A f(Y_int n) + U *ᵥ Y n n`) and concludes that
`Y_int n → (fun _ => yex(x))` (all stage components tend to the
exact solution at the target time). This is needed to extract
`U · u' = 𝟙` for the `u' = u` bridge in `thm:514A`; see
`.prover-state/issues/glm_isconvergent_strengthened.md` and
`.prover-state/issues/u_prime_equals_u_bridge.md`. -/
def GeneralLinearMethod.IsConvergent {s r : ℕ}
    (M : GeneralLinearMethod s r) : Prop :=
  ∀ (f : ℝ → ℝ) (L : NNReal), LipschitzWith L f →
  ∀ (x₀ y₀ : ℝ) (yex : ℝ → ℝ),
    yex x₀ = y₀ →
    (∀ x, HasDerivAt yex (f (yex x)) x) →
  ∃ u : Fin r → ℝ, u ≠ 0 ∧
    ∀ φ : ℝ → Fin r → ℝ,
      (∀ i : Fin r, Filter.Tendsto (fun h : ℝ => φ h i)
                       (nhds 0) (nhds (u i * y₀))) →
    ∀ x : ℝ, x₀ < x →
    ∀ Y : ℕ → ℕ → Fin r → ℝ,
    ∀ Y_int : ℕ → Fin s → ℝ,
      (∀ n : ℕ, 0 < n →
        Y n 0 = φ ((x - x₀) / (n : ℝ)) ∧
        M.IsGLMSolution ((x - x₀) / (n : ℝ)) f (Y n) ∧
        (∀ i, Y_int n i = (∑ j, M.A i j * (((x - x₀) / (n : ℝ)) * f (Y_int n j)))
                          + (∑ j, M.U i j * Y n n j))) →
      Filter.Tendsto (fun n : ℕ => Y n n)
                     Filter.atTop (nhds (fun i => u i * yex x))
      ∧ Filter.Tendsto Y_int
                       Filter.atTop (nhds (fun _ => yex x))

/-! ### Sanity helpers — non-vacuity of `IsGLMSolution` -/

/-- For autonomous RHS `f ≡ 0`, the GLM iteration recurrence reduces
to the homogeneous V-recurrence
`y_seq (n+1) i = Σ_j V_{ij} · y_seq n j`. -/
theorem isGLMSolution_zero_iff {s r : ℕ}
    (M : GeneralLinearMethod s r) (h : ℝ) (y_seq : ℕ → Fin r → ℝ) :
    M.IsGLMSolution h (fun _ => 0) y_seq ↔
    ∀ n : ℕ, ∀ i : Fin r,
      y_seq (n + 1) i = ∑ j : Fin r, M.V i j * y_seq n j := by
  unfold GeneralLinearMethod.IsGLMSolution
  constructor
  · intro hSol n i
    obtain ⟨Y, _hStage, hOut⟩ := hSol n
    have h1 := hOut i
    -- Reduce the b-row term `Σ_j B_{ij} · (h · 0) = 0`.
    simp only [mul_zero, Finset.sum_const_zero, zero_add] at h1
    exact h1
  · intro hHom n
    -- Construct the stage Y = U · y_seq n.
    refine ⟨fun i => ∑ j, M.U i j * y_seq n j, ?_, ?_⟩
    · intro i
      simp only [mul_zero, Finset.sum_const_zero, zero_add]
    · intro i
      simp only [mul_zero, Finset.sum_const_zero, zero_add]
      exact hHom n i

/-- The constantly-zero sequence is a GLM iteration of any GLM at
any stepsize for the trivial autonomous RHS `f ≡ 0`. -/
theorem zero_isGLMSolution_zero {s r : ℕ}
    (M : GeneralLinearMethod s r) (h : ℝ) :
    M.IsGLMSolution h (fun _ => 0) (fun _ _ => 0) := by
  intro n
  refine ⟨fun _ => 0, ?_, ?_⟩
  · intro i; simp
  · intro i; simp

/-- The constantly-zero sequence solves the homogeneous V-recurrence
for any GLM. Useful infrastructure for §513/§514/§515 work. -/
theorem zero_seq_homogeneous_V {s r : ℕ}
    (M : GeneralLinearMethod s r) :
    ∀ n : ℕ, ∀ i : Fin r,
      ((fun (_ : ℕ) (_ : Fin r) => (0 : ℝ)) (n + 1)) i =
        ∑ j : Fin r, M.V i j * ((fun (_ : ℕ) (_ : Fin r) => (0 : ℝ)) n) j := by
  intro n i
  simp

end OpenMath.Chapter5.Section510
