# Issue: bridge `u' = u` between convergence-witness and preconsistency-witness

## Blocker

Sub-lemma C of `thm:514A` (`OpenMath/Chapter5/Section514.lean::cesaro_residual_tendsto_zero`,
line 148) needs a bridge between two distinct vectors:

* `u' : Fin r → ℝ` — the convergence-witness extracted from `M.IsConvergent`
  applied to the IVP `y'(x) = 1, y(0) = 0, yex := id`.
* `u : Fin r → ℝ` — the preconsistency-witness from `M.IsPreconsistent`,
  satisfying `V·u = u` and `U·u = 𝟙`.

To close sub-lemma C, we need `u' = u`. Butcher's textbook proof
(§514, p. 410) makes this identification implicit; in our formalisation
it is not free.

## Context

The relevant Lean state, with the IsConvergent application unrolled:

```text
hConv' : ∀ φ, (∀ i, Tendsto (fun h => φ h i) (nhds 0) (nhds (u' i * 0))) →
              ∀ x, 0 < x →
              ∀ Y, (∀ n, 0 < n → Y n 0 = φ ((x - 0) / n) ∧
                                    M.IsGLMSolution ((x - 0)/n) (fun _ => 1) (Y n)) →
              Tendsto (fun n => Y n n) atTop (nhds (fun i => u' i * yex x))
```

Instantiated at `φ ≡ 0`, `x := 1`, `Y n := M.glmConstOneIterate (1/n)`,
together with sub-lemma B's closed form, this gives:

```text
Tendsto (fun n => (1/n) • Σ V^k *ᵥ (B *ᵥ 𝟙))  atTop  (nhds u')
```

Sub-lemma C's target is:

```text
Tendsto (fun n => (1/n) • Σ V^k *ᵥ (B *ᵥ 𝟙 - u))  atTop  (nhds 0)
```

By `V·u = u` ⇒ `V^k · u = u`, the `u` term is `(1/n) • (n • u) = u`.
So the target reduces to the difference of limits being `u' - u`,
i.e. **target ⇔ `u' = u`**.

## What was tried

* (Cycle 094) Original `thm:514A` scaffold deferred this entirely —
  `cesaro_residual_tendsto_zero` was left as a top-level sorry with a
  comment pointing to the bridge.
* (Cycle 095) Re-examined the `IsConvergent` definition
  (`OpenMath/Chapter5/Section512.lean::138-154`) — confirmed `u'` is
  bound by `∃ u : Fin r → ℝ, u ≠ 0 ∧ ∀ φ, ...`. The witness is
  shared across all `φ` and `Y`, but no clause forces it equal to
  `u` or to any other externally-determined vector.
* (Cycle 095) Drafted the textbook reasoning: applying continuity of
  `V *ᵥ ·` to `Y n n → u'` would yield `V *ᵥ Y n n → V *ᵥ u'`, which
  combined with the closed-form computation gives `V *ᵥ u' = u'`.
  This is a partial bridge (the `V·u' = u'` half) but does NOT pin
  down `u' = u` since `ker(I - V)` may be multi-dimensional.

## Why this is hard

Two problems:

1. **`U·u' = 𝟙` is not extractable from `IsConvergent`.** The `U`-block
   appears in `IsGLMSolution`'s stage equation, but the
   `IsConvergent` conclusion `Y n n → u' · yex(x)` doesn't expose it.
   To force `U·u' = 𝟙` we would need a more informative φ that probes
   the U-coupling — but the textbook φ ≡ 0 choice loses this signal.

2. **Even if `V·u' = u'` and `V·u = u` both hold, `u' = u` is not
   automatic** unless `ker(I - V)` is one-dimensional. With matrix
   `V` allowed to have arbitrary `1`-eigenspace, this is a real gap.

## Possible solutions

* **(a) Add a non-degeneracy hypothesis** on `V`'s `1`-eigenspace
  (e.g. assume `dim ker(I - V) = 1` or a related uniqueness clause).
  Risk: this adds a textbook-foreign hypothesis to `thm:514A`. Would
  need to be documented as a faithfulness divergence and ideally
  proven equivalent to (or implied by) preconsistency + stability.

* **(b) Prove `U·u' = 𝟙` by examining the starting-procedure
  quantification more carefully.** The `IsConvergent` statement
  quantifies over all valid φ; perhaps a more informative φ (e.g.
  φ(h) i = u_i for all h, satisfying the φ tendsto with `y₀ = 0`
  trivially since `u_i * 0 = 0`) makes `U·u'` extractable. Needs
  careful exploration of the GLM stage equation under different φ.

* **(c) Defer until a uniqueness theorem for preconsistency
  vectors.** If we prove "the preconsistency vector is unique up to
  a scalar" as a separate theorem (Butcher §510 has this implicitly),
  then combined with `u'` being a fixed point of `V` and the
  IsConvergent normalisation `u' ≠ 0`, we may get `u' = c · u` for
  some `c ≠ 0`. Then the Cesàro statement becomes `c·u = u` after
  taking limits, which forces `c = 1`. Needs a cycle of its own to
  formalise the uniqueness step.

## Cross-reference

This bridge plus sub-lemma D (`cesaro_inverse_I_minus_V.md`) are
the two remaining blockers for `thm:514A`. Sub-lemma D is mean-ergodic
infrastructure (multi-cycle); this issue is comparatively local
(single-lemma) but conceptually subtle.
