# Cycle 492 Results

## Worked on
Butcher §37 (Symplectic Runge–Kutta Methods) — created
`OpenMath/SymplecticRK.lean` from scratch.

## Approach
Direct one-shot implementation per the cycle 492 strategy: scaffold,
inline algebraic Cooper/Sanz–Serna proof of §370A, three §371 examples.
Did **not** submit an Aristotle batch — the algebraic core closed in a
single editing pass without scaffolding-stage sorries to delegate, so
the standard "sorry-first → batch → sleep 30 min" loop was skipped.

## Result
SUCCESS. `lake build OpenMath.SymplecticRK` is green; `rg sorry
OpenMath/SymplecticRK.lean` is empty; no `maxHeartbeats` overrides;
imports kept narrow (`OpenMath.RungeKutta`, `OpenMath.GaussLegendre3`,
`Mathlib.LinearAlgebra.Matrix.Symmetric`).

Closed:
- `ButcherTableau.symplecticDefect` — Cooper's M-matrix entries.
- `ButcherTableau.IsSymplectic` — predicate.
- `ButcherTableau.dotProduct_mulVec_symm` — bilinear-form symmetry
  lemma for symmetric matrices.
- `ButcherTableau.IsSymplectic.preserves_quadInv` — **§370A**
  (full Cooper 1987 / Sanz-Serna calculation, formulated with bare
  `Matrix.dotProduct` / `Matrix.mulVec` exactly per the strategy's
  warning to avoid `EuclideanSpace.inner` / `PiLp 2`).
- `rkGaussLegendre1` (= implicit midpoint) and
  `rkGaussLegendre1_consistent`, `rkGaussLegendre1_isSymplectic`.
- `rkGaussLegendre2_isSymplectic` (`Fin 2 × Fin 2` case-split + `nlinarith [sqrt3_sq']`).
- `rkGaussLegendre3_isSymplectic` (`Fin 3 × Fin 3` case-split + `nlinarith [sqrt15_sq']`).

§370A proof shape (load-bearing):
1. Establish bilinear-form properties of `B(u,v) = u ⬝ᵥ S *ᵥ v` —
   symmetry from `S.IsSymm`, distributivity over `+`, `•`, and `∑`.
2. Per stage: from `f Yᵢ ⬝ᵥ S *ᵥ Yᵢ + Yᵢ ⬝ᵥ S *ᵥ f Yᵢ = 0` and B-symmetry,
   conclude `B(f Yᵢ, Yᵢ) = 0` (`hF_diag`).
3. Substitute `y0 = Yᵢ − h ∑ⱼ Aᵢⱼ • f Yⱼ` to get
   `B(f Yᵢ, y0) = -h ∑ⱼ Aᵢⱼ B(f Yᵢ, f Yⱼ)` (`hB_f_y0`).
4. Expand `B(y0+Δ, y0+Δ) = B(y0,y0) + 2 B(Δ,y0) + B(Δ,Δ)` (`hExpand`).
5. Reindex the cross sum using `Finset.sum_comm` and B-symmetry
   (`hReindex`): `2 ∑ᵢⱼ bᵢ Aᵢⱼ B(fᵢ,fⱼ) = ∑ᵢⱼ (bᵢ Aᵢⱼ + bⱼ Aⱼᵢ) B(fᵢ,fⱼ)`.
6. `IsSymplectic` kills the residual `(bᵢ Aᵢⱼ + bⱼ Aⱼᵢ − bᵢ bⱼ)`
   coefficient at every entry; finish with `nlinarith [hReindex, hAC]`.

## Dead ends
- First draft used `Matrix.dotProduct` with the `Matrix.` namespace
  prefix; current Mathlib has the operator at root namespace
  (only the notation `⬝ᵥ` is exported under `open Matrix`). Fixed.
- A few `congr 1` attempts hit `AddCommMonoid ?m` typeclass-stuck
  errors when the function family was a metavariable. Replaced with
  explicitly named `Finset.mul_sum (s := …) (f := …) (a := …)` rewrites.
- The `Finset.mul_sum` argument is `a`, not `b`, in current Mathlib.

## Discovery
- For RK quadratic-invariant proofs in Lean 4 / Mathlib, the cleanest
  representation of the bilinear form `vᵀ S w` is `v ⬝ᵥ S *ᵥ w` with
  `set B := fun u v => u ⬝ᵥ S *ᵥ v` followed by hand-built lemmas for
  bilinearity. `EuclideanSpace.inner` / `PiLp 2` would have dragged in
  `RCLike` baggage that derails `ring` and `linear_combination`.
- For symmetric `S`, the key identity `v ⬝ᵥ S *ᵥ w = w ⬝ᵥ S *ᵥ v`
  unfolds quickly via `simp [dotProduct, Matrix.mulVec, Finset.mul_sum]`,
  `Finset.sum_comm`, and `IsSymm.apply` — no need to route through
  `Matrix.dotProduct_mulVec` / `Matrix.vecMul_transpose`.
- The §371 GL2 / GL3 cases reduce to `√3` / `√15` polynomial identities
  that `nlinarith [sqrt_sq]` handles fine via direct `fin_cases`
  enumeration; no need for a per-`(i,j)` private-helper split despite
  the cycle 442+ heartbeat-pressure pattern.

## Suggested next approach
- §37 is closed except for §372 (the trivial corollary that symplectic
  order conditions follow from `M = 0` plus standard order conditions)
  and §373 (informal experiments). Both are low priority.
- Next planner cycle should pivot to **Butcher §45 One-Leg Methods and
  G-stability** as flagged in the existing `plan.md` "If §37 is
  blocked" branch (now promoted to primary). Concretely, define the
  one-leg counterpart of an LMM (`OpenMath/OneLegMethods.lean`),
  the G-norm and G-stability predicate (`OpenMath/GStability.lean`),
  and prove the trapezoidal rule (`θ = 1/2`) is G-stable with `G = 1`.
- Stretch goal **not** taken this cycle: derive `IsSymplectic` for
  the general Gauss–Legendre family from `B(2s) ∧ C(s) ∧ D(s)` plus
  shifted-Legendre orthogonality. Worth a cycle once the §45 path
  starts paying down.
