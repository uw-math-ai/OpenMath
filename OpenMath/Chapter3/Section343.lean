import OpenMath.Chapter3.Section312

/-!
# Butcher §343 — Reflected (adjoint) Runge–Kutta methods

This file formalises Definition 343 (the *reflection* of a Runge–Kutta
method) and Theorem 343A (the reflection is an involution) from Butcher's
*Numerical Methods for Ordinary Differential Equations* (3rd ed., page
220–221).

## Textbook statement (Theorem 343A, quoted verbatim from `thm_343A.json`)

> The reflection of the reflection of a Runge–Kutta method is the
> original method.

## Reflection tableau (Butcher §343, page 220–221)

Given the tableau `(c, A, b)` for an `s`-stage Runge–Kutta method,
Butcher derives the reflection by

* subtracting (343c) from (343b) to express each stage value `Yᵢ` in
  terms of the result `yₙ` (rather than the input `yₙ₋₁`);
* rearranging (343c) to express `yₙ₋₁` in terms of `yₙ`;
* reversing all signs to recover a forward-pointing tableau.

The resulting tableau (page 220, last display) is

```
  (Σⱼ bⱼ) - cᵢ │ b₁ - aᵢ₁  b₂ - aᵢ₂  ⋯  bₛ - aᵢₛ
                ─────────────────────────────────
                 b₁  b₂  ⋯  bₛ
```

In our component-wise reformulation:

* `ĉᵢ = (Σⱼ bⱼ) - cᵢ`,
* `âᵢⱼ = bⱼ - aᵢⱼ`,
* `b̂ⱼ = bⱼ`.

## Faithfulness note

Butcher's `c` formula uses `Σⱼ bⱼ` (not `1`); under the consistency
condition `Σⱼ bⱼ = 1`, this reduces to `1 - cᵢ`, but def:343 does *not*
assume consistency. We therefore keep `(Σⱼ bⱼ) - cᵢ` in `reflection`
verbatim and do **not** silently substitute `1`.

The proof of Theorem 343A in Butcher's text is "easy to verify, which
we present without proof" (page 221). The argument is purely
arithmetic: each component cancels by `ring` over `ℝ` after one round
of definitional unfolding.
-/

namespace OpenMath.Chapter3.Section312

open OpenMath.Chapter3.Section310

namespace RKTableau

/-- Butcher §343 — the *reflection* of a Runge–Kutta method, also
known as the *adjoint method*.

Given the tableau `(A, b, c)`, the reflected tableau has

* `âᵢⱼ = bⱼ - aᵢⱼ`,
* `b̂ⱼ = bⱼ`,
* `ĉᵢ = (Σⱼ bⱼ) - cᵢ`.

See the file docstring for Butcher's derivation. -/
def reflection {s : ℕ} (M : RKTableau s) : RKTableau s where
  A i j := M.b j - M.A i j
  b j   := M.b j
  c i   := (∑ j : Fin s, M.b j) - M.c i

/-- Unfolding lemma for the `A` field of the reflection. -/
theorem reflection_A_apply {s : ℕ} (M : RKTableau s) (i j : Fin s) :
    M.reflection.A i j = M.b j - M.A i j := rfl

/-- Unfolding lemma for the `b` field of the reflection. -/
theorem reflection_b_apply {s : ℕ} (M : RKTableau s) (j : Fin s) :
    M.reflection.b j = M.b j := rfl

/-- Unfolding lemma for the `c` field of the reflection. -/
theorem reflection_c_apply {s : ℕ} (M : RKTableau s) (i : Fin s) :
    M.reflection.c i = (∑ j : Fin s, M.b j) - M.c i := rfl

/-- Butcher §343 Theorem 343A — *the reflection of the reflection of a
Runge–Kutta method is the original method.*

The proof is component-wise: each of the three fields collapses by
`ring` after one round of definitional unfolding. Butcher writes "it is
easy to verify the following result, which we present without proof"
(page 221). -/
theorem reflection_reflection {s : ℕ} (M : RKTableau s) :
    M.reflection.reflection = M := by
  obtain ⟨A, b, c⟩ := M
  refine RKTableau.mk.injEq .. |>.mpr ⟨?_, ?_, ?_⟩
  · funext i j
    show b j - (b j - A i j) = A i j
    ring
  · rfl
  · funext i
    show (∑ j : Fin s, b j) - ((∑ j : Fin s, b j) - c i) = c i
    ring

/- ### Concrete witnesses

CLAUDE.md requires "at least one concrete witness/instance in the same
cycle" for new definitions.

(b) `RKTableau.explicitEuler` is a 1-stage tableau already defined in
`Section312`. Its double reflection equals itself by
`reflection_reflection`. -/

example : explicitEuler.reflection.reflection = explicitEuler :=
  reflection_reflection explicitEuler

/- (a) The *implicit midpoint* method (a 1-stage method with `A = 1/2`,
`b = 1`, `c = 1/2`). It is a *symmetric* method — its reflection equals
itself, so it is a non-trivial fixed point of `reflection`. -/

/-- The implicit midpoint rule as a 1-stage Runge–Kutta tableau
(Butcher §371, page 240). Tableau: `A = (1/2)`, `b = (1)`, `c = (1/2)`.

Marked `noncomputable` because the entries use real-number division. -/
noncomputable def implicitMidpoint : RKTableau 1 where
  A := fun _ _ => (1/2 : ℝ)
  b := fun _ => 1
  c := fun _ => 1/2

/-- The implicit midpoint method is symmetric: its reflection equals
itself. This demonstrates that `reflection` has non-trivial fixed
points. -/
example : implicitMidpoint.reflection = implicitMidpoint := by
  refine RKTableau.mk.injEq .. |>.mpr ⟨?_, ?_, ?_⟩
  · funext i j
    show (1 : ℝ) - 1/2 = 1/2
    norm_num
  · rfl
  · funext i
    show (∑ _j : Fin 1, (1 : ℝ)) - 1/2 = 1/2
    simp; norm_num

end RKTableau

end OpenMath.Chapter3.Section312
