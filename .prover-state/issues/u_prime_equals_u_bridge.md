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
* (Cycle 096) **PARTIAL BRIDGE CLOSED**: the `V·u' = u'` half is now
  proven as a sorry-free lemma
  `GeneralLinearMethod.convergence_witness_isVfixed` in
  `OpenMath/Chapter5/Section514.lean`. The proof instantiates the
  trivial IVP (`f ≡ 1`, `yex := id`, `x₀ := 0`, `y₀ := 0`) with
  `φ ≡ 0` and `Y n m := M.glmConstOneIterate (1/n) m`, applies the
  closed-form lemma + the algebraic identity
  `V *ᵥ glm h n = glm h n + h • (V^n *ᵥ B𝟙 - B𝟙)`, uses
  power-boundedness (via §513 stability) to vanish the residual
  `(1/n) • (V^n *ᵥ B𝟙 - B𝟙) → 0`, and concludes by
  `tendsto_nhds_unique` against the continuous-mulVec lift of
  `Y n n → u'`. Axioms: `[propext, Classical.choice, Quot.sound]`
  only. **Remaining work**: `U·u' = 𝟙` (other half) plus a
  uniqueness step to identify `u'` with `u`.

## Why this is hard

Two problems:

1. **`U·u' = 𝟙` is provably NOT extractable from `def:512A`** (cycle
   097 confirmation). Re-reading `Section512.lean:89-96`:
   `IsGLMSolution h f Y` for the autonomous RHS `f ≡ 1` reduces, on
   the *output* side, to `y[n+1] = h • B𝟙 + V *ᵥ y[n]`. The `U`
   matrix appears only in the existential *stage* equation
   `Y_i = h • A𝟙 + U *ᵥ y[n]` (where `Y_i` are internal stages), but
   the `IsConvergent` conclusion is `Y n n → u' · yex(x)` — which
   constrains only the output sequence, never the per-step internal
   stages. Therefore **no choice of `(f, y₀, yex, φ)` constrains
   `U·u'` through `IsConvergent`'s output**, no matter how clever
   the φ. The "smarter φ" approach floated in cycle 095 (option (b)
   below) does not work for this reason.

2. **Even if `V·u' = u'` and `V·u = u` both hold, `u' = u` is not
   automatic** unless `ker(I - V)` is one-dimensional. With matrix
   `V` allowed to have arbitrary `1`-eigenspace, this is a real gap.

## Possible solutions (revised cycle 097)

The cycle-097 analysis above closes off option (b) below entirely.
Only the following remain viable, and **all of them deviate from
the textbook signature** in some way:

* **(i) Prove a GLM analog of LMM `thm:405B`
  (`convergent_isPreconsistent`) by an ergodic-style argument that
  bypasses the stage equation.** Idea: derive *some* rank/range
  condition on `(I - V, B𝟙, U)` from the Cesàro mean alone (without
  ever touching `U`). This requires invention; no textbook proof
  exists in Butcher §514 because the textbook implicitly identifies
  `u'` with `u`. **Cost**: open-ended; potentially several cycles
  of mathematical exploration.

* **(ii) Reformulate `thm:514A`'s conclusion to use `u'` itself**
  (drop the textbook `IsPreconsistent` connection in the witness).
  This requires changing the textbook signature: the resulting
  `IsConsistent`-style conclusion would witness consistency
  *relative to* the convergence-witness `u'`, not the preconsistency
  vector `u`. **Cost**: 1–2 cycles. **Risk**: faithfulness
  divergence needs careful documentation; the textbook does not
  separate these vectors.

* **(iii) Strengthen `IsConvergent` (def:512A) to also expose
  stages.** Add an extra clause that the stage sequence
  `Y_i (n) → some-vector · yex(x)`, then derive `U·u' = 𝟙` from
  it. **Cost**: 1 cycle for the definition change + downstream
  rewiring (e.g. `thm:513A` and `thm:514A`'s convergence-witness
  proofs need updating). **Risk**: textbook deviation similar to
  the LMM `is_convergent_strengthened.md` parallel.

* **(a) (Original)** Add a non-degeneracy hypothesis on `V`'s
  `1`-eigenspace (e.g. assume `dim ker(I - V) = 1` or similar).
  **Risk**: textbook-foreign hypothesis added to `thm:514A`. Would
  need to be documented as a faithfulness divergence and ideally
  proven equivalent to (or implied by) preconsistency + stability.

* **~~(b) Prove `U·u' = 𝟙` by examining the starting-procedure
  quantification more carefully.~~** **CLOSED OFF (cycle 097)**: see
  point 1 of "Why this is hard" above. The `U` matrix is provably
  invisible to `IsConvergent`'s output-only conclusion.

* **(c) Defer until a uniqueness theorem for preconsistency
  vectors.** If we prove "the preconsistency vector is unique up to
  a scalar", then combined with `u'` being a fixed point of `V`
  and `u' ≠ 0`, we may get `u' = c · u` and force `c = 1` via the
  Cesàro statement. **Cost**: a cycle of its own. **Risk**: still
  needs `U·u' = something-extractable` to bridge — and per (1)
  above this can't come from `def:512A` directly.

## Status as of cycle 097

This is now a **major open problem** for `thm:514A`. We are
deferring it and pivoting to the orthogonal infrastructure work
on `exists_inverse_of_cesaro_zero` (Path B mean-ergodic, see
`cesaro_inverse_I_minus_V.md`). Once Path B lands and its sorry
is closed, the only remaining sorry in §514 will be
`cesaro_residual_tendsto_zero`, gated on this very issue. At that
point a planning cycle should choose between options (i)–(iii)
+ (a)/(c) and commit to a path; the most likely candidate is
**(iii) strengthen `IsConvergent`** because it parallels the LMM
strengthening already on the table (`is_convergent_strengthened.md`),
because `U·u' = 𝟙` is a *natural* additional output of the
formalised `IsConvergent` definition, and because options (i) and
(c) require open-ended invention.

## RESOLUTION (cycle 099) — option (ii) via existential sidestep

**Status: RESOLVED.** Cycle 099 closed `thm:514A` by adopting
option (ii), enabled by cycle 098's option (iii) strengthening
of `IsConvergent`.

The closure observation: `IsConsistent` is *existential* in the
preconsistency vector — `∃ u v, (V·u = u ∧ U·u = 𝟙) ∧ B𝟙 + V·v = u + v`.
With cycle 098's strengthened `IsConvergent`, the convergence-witness
vector `u'` is now a full preconsistency vector (`V·u' = u'` AND
`U·u' = 𝟙` AND `u' ≠ 0`), so `u'` *itself* witnesses preconsistency.
There is no need to identify `u'` with the externally-supplied `u`
from `hPre`.

**What's now in `OpenMath/Chapter5/Section514.lean`** (cycle 099):

* `convergence_witness_satisfies_U` — `∃ u', u' ≠ 0 ∧ V·u' = u'
  ∧ U·u' = 𝟙 ∧ Tendsto Cesàro-sum atTop (nhds u')`. The U-side
  half is derived from cycle 098's stage-limit clause via the
  trivial-IVP stage equation `Y_int n i = (1/n)•(A𝟙)_i +
  (U·Y n n) i` and continuity of `M.U *ᵥ ·`.
* `convergent_isPreconsistent` — GLM analog of LMM `thm:405B`,
  one-line corollary: `IsConvergent → IsPreconsistent` without
  needing `hPre`.
* `cesaro_residual_tendsto_zero` (reformulated) — pure-algebraic
  identity, no GLM dependence; takes `u'`, `V·u' = u'`, and
  the Cesàro-sum hY_lim and produces the residual Cesàro Tendsto.
* `convergent_preconsistent_isConsistent` — uses `u'` as the
  preconsistency witness. The `_hPre` hypothesis is unused
  (underscore-prefixed binder); the theorem could be tightened to
  drop `IsPreconsistent`, but the textbook signature is preserved
  as documented faithfulness.

**Faithfulness divergence** (documented in the theorem docstring):
the `_hPre` hypothesis is unused. The textbook implicitly identifies
`u' = u`; we sidestep this by using `u'` as both the convergence
witness AND the preconsistency witness. This is faithful to the
textbook's *theorem statement* (a vector `v` exists making 510c
hold for *some* preconsistency vector), but slightly stronger
internally than the textbook's *proof sketch* (which used `u`
from the assumption).

**Axioms**: `[propext, Classical.choice, Quot.sound]` for
`convergent_preconsistent_isConsistent` and `convergent_isPreconsistent`.

## Cross-reference

Companion: `glm_isconvergent_strengthened.md` (cycle 098) — the
strengthening of `def:512A` that made this closure possible.
`cesaro_inverse_I_minus_V.md` (cycle 097) — the parallel
infrastructure dependency, also resolved.
