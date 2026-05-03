# Issue: Cesàro inverse `(1/n) Σ V^k w → 0 ⇒ w ∈ range (I − V)`

## Blocker

The `thm:514A` proof (cycle 094 scaffold,
`OpenMath/Chapter5/Section514.lean::exists_inverse_of_cesaro_zero`)
requires the lemma:

> If `V : Matrix (Fin r) (Fin r) ℝ` is power-bounded and the Cesàro
> mean `(1/n) Σ_{k=0}^{n-1} V^k · w` tends to `0` as `n → ∞`, then
> there exists `v : Fin r → ℝ` such that `(I − V) v = w`.

This is the textbook (Butcher §514, p. 410) "Schur decomposition +
invert `(I − W)` block" step, written abstractly as a mean-ergodic
statement to avoid explicit Jordan/Schur infrastructure.

## Why this needs its own cycle (or two)

Two paths exist; both are non-trivial:

### Path A — Schur decomposition (per `jordan_canonical_form_missing.md`)

Build a Schur-style upper-triangular decomposition of `V` over ℝ
(or via complexification). Decompose `V = S^{-1} ⟨I, 0; 0, W⟩ S` with
`W` power-bounded and `1 ∉ σ(W)`. Invert `(I − W)`, lift back. Cost:
3–5 cycles per cycle-009 estimate.

### Path B — Mean ergodic theorem (finite-dim, real)

Use von Neumann's mean ergodic theorem in finite dim:
`(1/n) Σ T^k x → P x` where `P` projects onto `ker (I − T)` along
`closure (range (I − T))`. In finite dim, the range is closed, so
`(1/n) Σ T^k w → 0` ⇒ `w ⊥ ker (I − T*)` ⇒
`w ∈ (ker (I − T*))^⊥ = range (I − T)`.

Mathlib has the mean ergodic theorem for unitary operators
(`Mathlib.MeasureTheory.Ergodic`), but not for general power-bounded
operators on finite-dim Euclidean space without further assumptions.
A self-contained proof in finite dim is feasible, roughly:

1. Show `range (I − V)` is closed (finite dim).
2. Show `range (I − V) = (ker (I − V*))^⊥`.
3. Show `(1/n) Σ V^k · w → P w` where `P` is the projection onto
   `ker (I − V)`.
4. Combine.

Cost: 2–3 cycles, with the bulk of the work being the right-adjoint
+ projection plumbing.

## Recommendation

Path B for self-containment; Path A only if a Schur decomposition lands
in Mathlib first.

## Affected entities

* `thm:514A` (cycle 094 scaffold) — gated.
* `thm:515D` (stability + consistency ⇒ convergence, §515) — likely
  also benefits from this infrastructure on the consistency-extraction
  side.

## Cross-references

* `jordan_canonical_form_missing.md` — parent issue documenting the
  Schur/Jordan gap.
* `OpenMath/Chapter5/Section514.lean::exists_inverse_of_cesaro_zero` —
  the sorry to close.
