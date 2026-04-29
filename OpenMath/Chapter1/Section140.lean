import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Module.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Abel

/-!
# Butcher §140 — Linear difference equations

This file collects entities of subsection 140 of Butcher's
*Numerical Methods for Ordinary Differential Equations* (3rd ed.).

Butcher §140 introduces the standard linear inhomogeneous matrix
recurrence (eq. 140a)

  `X_n = A_n · X_{n-1} + φ_n`

with prescribed initial value `X_0`, and proves the closed-form
solution

  `X_n = (∏_{i=1}^n A_i) · X_0 + (∏_{i=2}^n A_i) · φ_1`
       `+ (∏_{i=3}^n A_i) · φ_2 + ⋯ + A_n · φ_{n-1} + φ_n`,

where Butcher's product convention is right-to-left:

  `∏_{i=m}^n A_i = A_n · A_{n-1} · ⋯ · A_{m+1} · A_m`.

We formalize this generically over a left module `V` of a (possibly
non-commutative) `Semiring R`. The matrix-valued case of Butcher
arises by taking `R := Matrix m m S` and `V := m → S` together with
the natural `Matrix.mulVec` action.

Contents:

* `transProd` — Butcher's right-to-left transition product
  `A_n · A_{n-1} · ⋯ · A_{k+1}` (empty product `1` when `k ≥ n`).
* `linDiffEqSolution` — the recurrence `X_{k+1} = A_{k+1} • X_k + φ_{k+1}`.
* `thm:140A` — `linDiffEqSolution_closed_form`, the closed-form
  solution of the recurrence.
-/

namespace OpenMath.Chapter1.Section140

open Finset

variable {R : Type*} [Semiring R]
  {V : Type*} [AddCommMonoid V] [Module R V]

/-- Butcher's right-to-left transition product

`transProd A k n = A_n · A_{n-1} · ⋯ · A_{k+1}`,

with `n - k` factors when `k ≤ n`, equal to `1` when `k ≥ n`.

This matches Butcher's convention `∏_{i=m}^n A_i = A_n A_{n-1} ⋯ A_m`
via `transProd A (m-1) n` (i.e. shift by one in the lower index). -/
noncomputable def transProd (A : ℕ → R) : ℕ → ℕ → R
  | _, 0     => 1
  | k, n + 1 => if k ≤ n then A (n + 1) * transProd A k n else 1

@[simp]
lemma transProd_zero (A : ℕ → R) (k : ℕ) : transProd A k 0 = 1 := rfl

lemma transProd_succ (A : ℕ → R) (k n : ℕ) :
    transProd A k (n + 1) = if k ≤ n then A (n + 1) * transProd A k n else 1 := rfl

lemma transProd_succ_of_le (A : ℕ → R) {k n : ℕ} (h : k ≤ n) :
    transProd A k (n + 1) = A (n + 1) * transProd A k n := by
  rw [transProd_succ, if_pos h]

@[simp]
lemma transProd_self (A : ℕ → R) (n : ℕ) : transProd A n n = 1 := by
  cases n with
  | zero => rfl
  | succ n => rw [transProd_succ, if_neg (by omega : ¬ n + 1 ≤ n)]

lemma transProd_of_lt (A : ℕ → R) {k n : ℕ} (h : n < k) : transProd A k n = 1 := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [transProd_succ, if_neg (by omega : ¬ k ≤ n)]

/-- The recurrence (140a): `X_{k+1} = A_{k+1} · X_k + φ_{k+1}`,
with `X_0 = X₀` prescribed.

Indexing follows Butcher: `A k` and `φ k` are the data used in step
`k - 1 ↦ k`. The solution at step `k` is `linDiffEqSolution A φ X₀ k`. -/
noncomputable def linDiffEqSolution
    (A : ℕ → R) (φ : ℕ → V) (X₀ : V) : ℕ → V
  | 0     => X₀
  | k + 1 => A (k + 1) • linDiffEqSolution A φ X₀ k + φ (k + 1)

@[simp]
lemma linDiffEqSolution_zero (A : ℕ → R) (φ : ℕ → V) (X₀ : V) :
    linDiffEqSolution A φ X₀ 0 = X₀ := rfl

lemma linDiffEqSolution_succ (A : ℕ → R) (φ : ℕ → V) (X₀ : V) (k : ℕ) :
    linDiffEqSolution A φ X₀ (k + 1)
      = A (k + 1) • linDiffEqSolution A φ X₀ k + φ (k + 1) := rfl

/-- Butcher §140, Theorem 140A — *closed-form solution to the linear
inhomogeneous recurrence (140a)*.

Verbatim textbook statement (Butcher 2008, p. 66):

> The problem (140a), with initial value `X_0` given, has the unique
> solution
>   `y_n = (∏_{i=1}^n A_i) X_0 + (∏_{i=2}^n A_i) φ_1`
>        `+ (∏_{i=3}^n A_i) φ_2 + ⋯ + A_n φ_{n-1} + φ_n`,
> where the product convention is `∏_{i=m}^n A_i = A_n ⋯ A_{m+1} A_m`.

In our generic-module formulation, the X₀ coefficient
`∏_{i=1}^n A_i = A_n · ⋯ · A_1` is `transProd A 0 n`, and the `φ j`
coefficient `∏_{i=j+1}^n A_i = A_n · ⋯ · A_{j+1}` is
`transProd A j n` (which collapses to `1` for `j = n`, recovering the
final `φ_n` term). -/
theorem linDiffEqSolution_closed_form
    (A : ℕ → R) (φ : ℕ → V) (X₀ : V) (n : ℕ) :
    linDiffEqSolution A φ X₀ n
      = transProd A 0 n • X₀
        + ∑ j ∈ Icc 1 n, transProd A j n • φ j := by
  induction n with
  | zero =>
    simp [linDiffEqSolution, transProd]
  | succ n ih =>
    rw [linDiffEqSolution_succ, ih]
    -- Distribute `A (n+1) •` over the IH.
    rw [smul_add, Finset.smul_sum]
    -- Combine `A(n+1) • (transProd A 0 n • X₀)` into `transProd A 0 (n+1) • X₀`.
    have hX₀ :
        A (n + 1) • (transProd A 0 n • X₀) = transProd A 0 (n + 1) • X₀ := by
      rw [smul_smul, ← transProd_succ_of_le A (Nat.zero_le _)]
    -- Combine each summand: `A(n+1) • (transProd A j n • φ j)
    --                        = transProd A j (n+1) • φ j` for `j ∈ Icc 1 n`.
    have hsum :
        (∑ j ∈ Icc 1 n, A (n + 1) • transProd A j n • φ j)
          = ∑ j ∈ Icc 1 n, transProd A j (n + 1) • φ j := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_Icc] at hj
      rw [smul_smul, ← transProd_succ_of_le A hj.2]
    -- The sum on `Icc 1 (n+1)` splits as `Icc 1 n` plus the term at `j = n+1`,
    -- where `transProd A (n+1) (n+1) = 1` so that term equals `φ (n+1)`.
    have hsplit :
        ∑ j ∈ Icc 1 (n + 1), transProd A j (n + 1) • φ j
          = (∑ j ∈ Icc 1 n, transProd A j (n + 1) • φ j) + φ (n + 1) := by
      rw [Finset.sum_Icc_succ_top (by omega : (1 : ℕ) ≤ n + 1)]
      rw [transProd_self, one_smul]
    rw [hX₀, hsum, hsplit]
    abel

end OpenMath.Chapter1.Section140
