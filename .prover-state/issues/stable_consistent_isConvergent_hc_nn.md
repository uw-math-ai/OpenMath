# Issue: `stable_consistent_isConvergent` requires `hc_nn_witness` hypothesis

## Faithfulness divergence

Butcher's Theorem 515D states (verbatim, `entities/thm_515D.json`):

> A general linear method that is stable and consistent is convergent.

Our Lean signature is

```lean
theorem GeneralLinearMethod.stable_consistent_isConvergent
    {s r : ℕ} (hs : 0 < s) (M : GeneralLinearMethod s r)
    (hStab : M.IsStable) (hCons : M.IsConsistent)
    (hc_nn_witness : ∀ u v : Fin r → ℝ,
        ((M.V *ᵥ u = u ∧ M.U *ᵥ u = (fun _ => 1)) ∧
          M.B *ᵥ (fun _ => 1) + M.V *ᵥ v = u + v) →
        ∀ i, 0 ≤ M.glmAbscissae v i) :
    M.IsConvergent
```

The extra hypothesis `hc_nn_witness` requires that for any `(u, v)`
witnessing consistency, the GLM abscissae `c := A·𝟙 + U·v` are
componentwise non-negative.

The textbook (Butcher §515) does **not** require this. Butcher's
analysis implicitly assumes well-behaved abscissae for the methods of
interest — Runge–Kutta-style GLMs with `c ∈ [0, 1]` — but
`IsConsistent` does not encode this constraint.

## Why our formalisation needs it

The §515D proof chain depends on `aux_515D_construct_ell_U_phi_A`
(`Section515.lean:1213`), which constructs `ell_U`, `phi_A` — the
solution vectors of the M-matrix linear systems

  `ell_U − h₀ L |A| ell_U = |U|·𝟙`,
  `phi_A − h₀ L |A| phi_A = ½ c² + |A|·|c|`

via inverse-positivity of `(I − h₀ L |A|)`. The conclusion uses

  `Matrix.EntrywiseNonneg.mulVec_nonneg`

to derive `0 ≤ ell_U`, `0 ≤ phi_A`. This requires the right-hand side
to be entrywise non-negative, which forces `c ≥ 0` (since `½ c²` is
fine but `c · c` could mix signs in the dot products without the
hypothesis).

Specifically, `_hc_nonneg : ∀ i, 0 ≤ c i` is consumed at line 1218 of
`aux_515D_construct_ell_U_phi_A` and propagates through the M-matrix
inversion.

## Cascade of the hypothesis

Cycle 122 propagates `_hc_nn : ∀ i, 0 ≤ M.glmAbscissae v i` through
the §515D-internal helper chain:

* `aux_515D_per_step_K_bound` (cycle 122, new) — needs `_hc_nn` to
  invoke `aux_515D_construct_ell_U_phi_A`.
* `aux_515D_max_deviation_geometric_bound` — forwards `_hc_nn` to the
  per-step K-bound.
* `aux_515D_max_deviation_bound_tendsto_zero` — forwards.
* `aux_515D_componentwise_deviation_tendsto_zero` — forwards.
* `aux_515D_output_tendsto` — forwards.
* `stable_consistent_isConvergent` — adds `hc_nn_witness` as a fresh
  hypothesis, supplied at the call site.

§513 (`convergent_isStable`) and §514 (`convergent_isPreconsistent`,
`convergent_preconsistent_isConsistent`) do NOT call into the §515D
internal helpers — they consume `IsConvergent` directly. So the
cascade is contained inside `Section515.lean`; no §513/§514
regressions.

## Why we propagate instead of refactoring

Refactoring `aux_515D_construct_ell_U_phi_A` (cycle 114) to remove
the `c ≥ 0` requirement would mean either:

* Building the M-matrix inversion with signed `c` — requires a
  different right-hand-side analysis (the `½ c²` term is fine, but
  `|A| · |c|` would have to be replaced by `|A · c|` componentwise,
  changing the M-matrix structure).
* Splitting `c = c⁺ − c⁻` and applying inversion separately — adds
  significant complexity.

Both refactors are ~3 cycles of effort and not on the critical path
to closing §515D. Propagating `hc_nn_witness` upstream is mechanical
and preserves the existing cycle 114 helper.

## Future remediation

Revisit if a downstream consumer (e.g., applying `IsConvergent` to
an explicit GLM with negative abscissae such as a backward
differentiation formula) is genuinely blocked. Most practical GLMs
have non-negative abscissae by construction, so the `hc_nn_witness`
hypothesis is satisfiable in practice.

For the textbook-faithful unconditional `stable + consistent ⇒
convergent`, see also:

* `.prover-state/issues/cycle_113_isconvergent_strengthening_514_blocker.md`
  — earlier cascade analysis.
* `.prover-state/issues/aux_515D_output_tendsto_hypotheses.md` —
  full §515D blocker history.

## Cross-references

* `OpenMath/Chapter5/Section515.lean:1213` —
  `aux_515D_construct_ell_U_phi_A` (the source of the `_hc_nonneg`
  requirement).
* `OpenMath/Chapter5/Section510.lean:126` — `IsConsistent` (does not
  encode `c ≥ 0`).
* `OpenMath/Chapter5/Section510.lean:98` — `glmAbscissae` definition.
