# OpenMath Lean Codebase Audit Report

**Date:** 2026-04-20  
**Scope:** All `.lean` files under `OpenMath/`  
**Tools used:** `lean_verify`, `lean_file_outline`, `lean_diagnostic_messages`, source analysis  

---

## Summary

The build succeeds with zero errors. There are **no `sorry` keywords** in the compiled code — all 5 occurrences of the word "sorry" in the codebase appear inside comments, not as proof terms.

However, several significant issues were found:

| Severity | Count | Category |
|----------|-------|----------|
| Critical | 4 | Dishonest definitions / tautologies / vacuous proofs |
| Moderate | 3 | Misnamed or weakened theorems |
| Minor | 2 | Use of `native_decide` / `Classical.choice` |

---

## Critical Issues

### 1. `IsConvergent` is a dishonest definition — `dahlquist_equivalence` is vacuous

**File:** `DahlquistEquivalence.lean:758`

```lean
def IsConvergent (m : LMM s) : Prop :=
  m.IsConsistent ∧ m.HasStableRecurrence
```

**Problem:** Convergence of a linear multistep method is defined directly as the conjunction of its two algebraic characterizations (consistency + stable recurrence). The "Dahlquist Equivalence Theorem" that follows is then trivially true:

```lean
theorem dahlquist_equivalence (m : LMM s) :
    m.IsConvergent ↔ m.IsConsistent ∧ m.IsZeroStable := by
  simp only [IsConvergent]
  constructor
  · intro ⟨hc, hsr⟩; exact ⟨hc, zeroStable_of_stableRecurrence m hsr⟩
  · intro ⟨hc, hzs⟩; exact ⟨hc, stableRecurrence_of_zeroStable m hzs⟩
```

This proof does nothing except unfold the definition and apply `zeroStable_iff_stableRecurrence`. It does **not** prove that numerical solutions of the LMM converge to the exact ODE solution as `h → 0`.

**What the real theorem requires:** A proof that for any Lipschitz ODE `y' = f(t,y)` and any initial data converging to the exact initial condition as `h → 0`, the numerical solution `max_{0≤n≤N} |y_n - y(nh)| → 0`. This involves actual error propagation analysis (Gronwall bound on the accumulated local truncation error) and is entirely absent.

**Impact:** All downstream results — `forwardEuler_convergent`, `backwardEuler_convergent`, `bdf2_convergent`, ..., `bdf6_convergent` — inherit this vacuity. They prove the algebraic conditions are satisfied but say nothing about actual numerical convergence.

---

### 2. `aStable_poles_avoid_imagAxis` is a tautology

**File:** `OrderStars.lean:983–991`

```lean
theorem aStable_poles_avoid_imagAxis (data : OrderArrowCountData)
    (_h_pade : IsPadeApproxToExp data)
    (_h_355D : SatisfiesArrowCountInequality data)
    (h_exact : data.upArrowsAtPoles = data.denominatorDegree) :
    data.upArrowsAtPoles = data.denominatorDegree :=
  h_exact
```

**Problem:** The conclusion is literally identical to the last hypothesis. The proof is `h_exact`. The two unused hypotheses `_h_pade` and `_h_355D` are never used. This theorem says nothing.

**What it was supposed to prove:** That A-stability forces up-arrows from the order star to terminate at poles in the half-plane Re(z) < 0, not on the imaginary axis. This is a genuine topological result connecting A-stability to the pole locations and is entirely unproven.

---

### 3. `thm_355D` axiomatizes its own content

**File:** `OrderStars.lean:887–890`

```lean
structure IsRationalApproxToExp (data : OrderArrowCountData) : Prop where
  order_le : data.order ≤ data.numeratorDegree + data.denominatorDegree
  /-- Arrow trajectory completeness (355D content): the order arrows all
      terminate at zeros or poles ... This axiomatizes the topological argument
      pending full formalization. -/
  arrowTrajectoryComplete : data.order ≤ data.downArrowsAtZeros + data.upArrowsAtPoles

theorem thm_355D (data : OrderArrowCountData)
    (h_approx : IsRationalApproxToExp data) :
    SatisfiesArrowCountInequality data :=
  h_approx.arrowTrajectoryComplete
```

**Problem:** The entire topological content of Theorem 355D — that order arrows of a rational approximation to exp terminate at zeros or poles — is placed as a **hypothesis** inside `IsRationalApproxToExp`. The theorem `thm_355D` then just projects this hypothesis. This is mathematical sleight of hand: the hard part of the proof is hidden in the structure's constructor requirements.

The proof amounts to: "assuming 355D holds, 355D holds."

---

### 4. `IsAStablePadeApprox` bakes conclusions into hypotheses — `ehle_barrier` is weakened

**File:** `OrderStars.lean:935–947`

```lean
structure IsAStablePadeApprox (data : OrderArrowCountData) : Prop where
  pade : IsPadeApproxToExp data
  sector_bound_n : data.numeratorDegree ≤ data.denominatorDegree + data.downArrowsAtZeros
  sector_bound_d : data.denominatorDegree ≤ data.numeratorDegree + 2 + data.upArrowsAtPoles
  arrows_zero : data.downArrowsAtZeros = 0   -- ← should be DERIVED, not assumed
  arrows_poles : data.upArrowsAtPoles = 0    -- ← should be DERIVED, not assumed
```

**Problem:** The fields `arrows_zero` and `arrows_poles` state that the correction terms vanish. These are supposed to be **consequences** of A-stability combined with the order star theory (via theorem 355F: A-stability prevents order arrows from lying on the imaginary axis). Instead, they are input hypotheses of the structure.

The proof of `ehle_barrier` then trivially substitutes `0` for these terms:

```lean
theorem ehle_barrier (data : OrderArrowCountData) (h : IsAStablePadeApprox data) :
    data.numeratorDegree ≤ data.denominatorDegree ∧
    data.denominatorDegree ≤ data.numeratorDegree + 2 := by
  constructor
  · have hnd := h.sector_bound_n; rw [h.arrows_zero] at hnd; simpa using hnd
  · have hdn := h.sector_bound_d; rw [h.arrows_poles] at hdn; simpa using hdn
```

Anyone instantiating `IsAStablePadeApprox` must supply `arrows_zero` and `arrows_poles` as proof obligations, but the structure gives no indication of how to derive these from A-stability alone. The hard mathematical content (that A-stability + the order star topology forces these terms to zero) remains unproven.

---

## Moderate Issues

### 5. `euler_convergence_order1` is misnamed — it proves Gronwall algebra, not Euler convergence

**File:** `EulerConvergence.lean:35–51`

The theorem is documented as "**Theorem 213A (order of convergence). The Euler method is first-order convergent**" but its statement is:

```lean
theorem euler_convergence_order1 (L T M : ℝ) (hL : 0 ≤ L) (hT : 0 ≤ T) (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, 0 ≤ h →
    gronwallBound 0 L (M * h) T ≤ K * h
```

**Problem:** This proves only that the Gronwall bound function `gronwallBound(0, L, M·h, T)` is O(h) in h. There is no mention of the Euler method, no numerical steps `y_{n+1} = y_n + h·f(t_n, y_n)`, and no proof that the actual Euler approximation error is bounded by `gronwallBound`. The link from Euler steps → local truncation error → Gronwall bound → global error is entirely missing.

The existing `perturbation_bound` theorem in `PicardLindelof.lean` provides the Gronwall machinery, but the gap between that and actual Euler convergence is not bridged.

---

### 6. `dahlquist_second_barrier` requires a non-standard extra hypothesis

**File:** `MultistepMethods.lean:2311–2316`

```lean
theorem dahlquist_second_barrier {s : ℕ} (m : LMM s) (p : ℕ)
    (hp : m.HasOrder p) (ha : m.IsAStable) (hzs : m.IsZeroStable)
    (h_unit : ∀ ζ : ℂ, m.rhoC ζ = 0 → ‖ζ‖ = 1 → ζ = 1) : p ≤ 2
```

**Problem:** The hypothesis `h_unit` asserts that ζ = 1 is the **only** unit-circle root of ρ. The standard textbook statement of Dahlquist's second barrier (Iserles, Theorem 3.4) does not include this condition — it follows from zero-stability that unit-circle roots of ρ are simple, but it does not require them all to equal 1. Methods can have multiple unit-circle roots of ρ (e.g., Adams–Bashforth 2-step has root ρ(ξ) = ξ² - ξ, giving roots 0 and 1), and the standard barrier still applies.

The comment notes this was needed for the `continuousOn_Gtilde_closedBall` proof strategy (to avoid singularities of the G̃ function at other unit-circle roots), but does not justify it mathematically or verify it holds for all methods under consideration.

---

### 7. Theorem 355B (Ehle barrier via winding numbers) is entirely absent

**File:** `OrderStars.lean:216–231`

The comment reads:
> "The Ehle barrier constrains which Padé approximants to `eᶻ` can be A-stable. The full proof requires winding number theory (not yet formalized), so we state the result with sorry."

But there is **no theorem statement** — not even one with `sorry`. The comment promises a formalization that does not exist. The `ehle_barrier` theorem that does appear (Issue 4 above) takes the hard content as a hypothesis, so this gap remains unfilled.

---

## Minor Issues

### 8. `native_decide` used in proof-critical positions

**File:** `OrderConditions.lean` (22 occurrences), `RootedTree.lean` (examples only)

`native_decide` bypasses the Lean kernel and calls compiled native code to verify decidable propositions. While the facts being checked (e.g., that a specific rooted tree has order 5 or that a specific tree is in a list) are almost certainly correct, `native_decide` proofs cannot be checked by Lean's trusted kernel and could theoretically be unsound if the native compiler has bugs.

The `OrderConditions.lean` uses include proof-critical steps like:
```lean
have ht2 : tab.satisfiesTreeCondition t2 := h t2 (by native_decide)
```
These are verifying membership/decidability facts that could be checked by `decide` instead (though at the cost of compile time).

---

### 9. `Classical.choice` in `RootedTree.lean`

**File:** `RootedTree.lean:379, 507, 598, 885, 914, 992`

Used to extract witnesses from nonemptiness proofs for order-3, -4, and -5 bag witnesses. This is mathematically legitimate (Classical.choice is a standard Lean axiom) but means the selected witnesses are noncomputable. The axiom check (`lean_verify`) confirms these proofs use only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

---

## Correct Results (Notable)

The following theorems appear to be correctly and completely proved:

- **`PicardLindelof.exists_unique`** — genuine Picard-Lindelöf theorem using Mathlib's contraction mapping infrastructure
- **`theorem_212A`** — discrete Gronwall inequality (correctly stated and proved)
- **`SpectralBound.uniformly_bounded_iterates_of_spectral_bound`** — the spectral radius bound using Cayley-Hamilton and generalized eigenspaces; the proof is non-trivial and appears correct
- **`dahlquist_second_barrier`** — modulo the `h_unit` caveat (Issue 6), the complex-analytic argument via the minimum principle and the Dahlquist G̃-function is substantive and correctly assembled
- **`an_stable_implies_alg_stable`**, **`alg_stable_implies_bn_stable`**, **`bnStable_implies_anStable`** — the AN/BN/algebraic stability equivalence chain appears sound
- **`aStable_with_nonvanishing_iff`** — correctly characterizes A-stability via a polynomial criterion using Phragmén-Lindelöf

---

## Recommended Actions

| Priority | Action |
|----------|--------|
| High | Redefine `IsConvergent` to express actual numerical convergence, or rename it to `IsSatisfiesAlgebraicConditions` and clearly document it is not convergence |
| High | Remove `aStable_poles_avoid_imagAxis` or replace with a genuine proof/sorry |
| High | Replace `thm_355D` with a `sorry` theorem that makes the unprovedness explicit |
| High | Document `IsAStablePadeApprox` and `ehle_barrier` as partial formalizations |
| Medium | Rename `euler_convergence_order1` or extend it to actually bound the Euler method error |
| Medium | Add `sorry` to `dahlquist_second_barrier` for the `h_unit` hypothesis pending justification, or prove `h_unit` from zero-stability for general methods |
| Low | Replace `native_decide` in `OrderConditions.lean` with `decide` where feasible |
