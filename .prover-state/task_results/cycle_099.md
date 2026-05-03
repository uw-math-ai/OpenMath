# Cycle 099 Results

## Worked on

`thm:514A` (Butcher Theorem 514A — "the necessity of consistency"):
the only remaining sorry in `OpenMath/Chapter5/Section514.lean` was
`cesaro_residual_tendsto_zero` (line 170). Closed via Priority-1
helper strengthening + Priority-3 reformulation. Also delivered the
GLM analog of LMM `thm:405B` (`convergent_isPreconsistent`).

## Approach

Followed the planner's strategy verbatim — option (ii) of
`u_prime_equals_u_bridge.md`, enabled by cycle 098's option-(iii)
strengthening of `IsConvergent`.

1. **Aristotle batch (Priority 0b)**: submitted 3 jobs at start of
   cycle (Job A = U-side extraction, Job B = Cesàro algebraic
   closure, Job C = GLM analog of `thm:405B`). All three were still
   `IN_PROGRESS` (~7–9% complete) at the one-shot status check;
   manual proofs landed first.

2. **Priority 1 — `convergence_witness_satisfies_U`**: replaced
   cycle 096's `convergence_witness_isVfixed` with a strengthened
   version returning `(u' ≠ 0) ∧ (V·u' = u') ∧ (U·u' = 𝟙) ∧
   (Cesàro-sum hY_lim → u')`. Reused cycle 096's body verbatim for
   the V-fixed conclusion; new Step 8 derives `U·u' = 𝟙` from
   `hConv_pair.2` (the cycle-098 stage-limit clause) using the
   trivial-IVP stage equation `Y_int n i = (1/n)•(A𝟙)_i +
   (U·Y n n) i`, continuity of `M.U *ᵥ ·`, and `tendsto_nhds_unique`.
   New Step 9 exposes the Cesàro-sum form by `glmConstOneIterate_closed_form`.

3. **Priority 2 — `convergent_isPreconsistent`**: one-line corollary
   of Priority 1 (`obtain ... ⟨u', _, hVu, hUu, _⟩` then
   `exact ⟨u', hVu, hUu⟩`). Genuine new theorem — GLM analog of
   LMM `thm:405B` (cycle 069).

4. **Priority 3 — `cesaro_residual_tendsto_zero`**: reformulated as
   a pure-algebraic identity (no GLM dependence, no `M.IsConvergent`
   hypothesis). Takes a matrix `V`, a vector `B1`, a fixed-point
   witness `hVu' : V·u' = u'`, and the Cesàro-sum tendsto, then
   produces the residual Cesàro tendsto via the planner's
   componentwise route: `tendsto_pi_nhds`, distribute `V^k *ᵥ (B1 - u')`
   using `V^k *ᵥ u' = u'` (induction), `field_simp` for `(1/n)·n = 1`
   (n ≥ 1 eventually), `Filter.tendsto_congr'` to bridge.

5. **Priority 4 — `witness_v_of_cesaro_inverse` rename**: cosmetic
   `u → u'` rename throughout. No behavioral change.

6. **Priority 5 — main theorem `convergent_preconsistent_isConsistent`**:
   restructured to extract `u'` (and `hVu'`, `hUu'`, `hY_lim`) from
   `convergence_witness_satisfies_U`, get `hPB` from
   `convergent_isStable`, feed everything to the now-pure-algebraic
   `cesaro_residual_tendsto_zero`, then to `witness_v_of_cesaro_inverse`,
   and pack `⟨u', v, ⟨hVu', hUu'⟩, hv⟩` as `IsConsistent`. The
   `_hPre` hypothesis is unused (binder underscore); documented in
   the theorem docstring.

7. **Priority 6 — issue/status updates**: marked
   `u_prime_equals_u_bridge.md` resolved (option ii closure narrative);
   marked `glm_isconvergent_strengthened.md` consumed; updated
   `lean_status.json` (partial → formalized, cycle 99); updated
   `plan.md` (62/175 → 63/175, `[~]` → `[x]` for `thm:514A`).

## Result

**SUCCESS** — `thm:514A` closed. Sorry count in §514 dropped 1 → 0.
`lake build OpenMath.Chapter5.Section514` succeeds (2779 jobs).
Axiom check via `lean_run_code`:

* `convergent_preconsistent_isConsistent`: `[propext, Classical.choice, Quot.sound]`
* `convergent_isPreconsistent`: `[propext, Classical.choice, Quot.sound]`

Both private helpers (`convergence_witness_satisfies_U`,
`cesaro_residual_tendsto_zero`) flow through these axioms transitively.

## Faithfulness check

### `theorem GeneralLinearMethod.convergent_preconsistent_isConsistent`

Entity ID: `thm:514A`. Textbook statement (`entities/thm_514A.json`):

> "Let `(A, U, B, V)` denote a convergent method which is, moreover,
> covariant with preconsistency vector `u`. Then there exists a
> vector `v ∈ ℝ^r`, such that (510c) holds."

Lean statement captures: **same content** for the conclusion (510c
is `B·𝟙 + V·v = u + v`, witnessed by the existential
`∃ u v, ... ∧ B·𝟙 + V·v = u + v` of `IsConsistent`). Hypothesis
shape matches: `IsConvergent ∧ IsPreconsistent`. **Stealth
strengthening**: `IsPreconsistent` is unused internally — the proof
uses the convergence-witness `u'` (from
`convergence_witness_satisfies_U`) as the consistency witness.

Justification for divergence: option (ii) of
`u_prime_equals_u_bridge.md`. The textbook's implicit `u' = u`
identification becomes unnecessary because `IsConsistent` is
existential and `u'` is itself a preconsistency vector (cycle 098
strengthening of `IsConvergent` made this extractable).

### `theorem GeneralLinearMethod.convergent_isPreconsistent` (NEW)

Not a textbook entity by name. GLM analog of LMM `thm:405B`
(formalised cycle 069). Conclusion: `IsConvergent → IsPreconsistent`.
Genuine one-line corollary of `convergence_witness_satisfies_U` —
the helper lemma does the real work; this is a meaningful named
projection.

### `private theorem GeneralLinearMethod.convergence_witness_satisfies_U` (REPLACES cycle 096's `convergence_witness_isVfixed`)

Sub-lemma, not a textbook entity. Replaces cycle 096's helper with
the U-side property added (`U·u' = 𝟙`) and the Cesàro-sum form
exposed (`hY_lim`). Cycle 098's `IsConvergent` strengthening is
the natural enabler.

### `private theorem cesaro_residual_tendsto_zero` (REFORMULATED)

Sub-lemma, not a textbook entity. Reformulation: previously
parameterised by `M.IsConvergent` and a preconsistency vector `u`,
now parameterised by the convergence-witness `u'` and its V-fixed
property. The conclusion is the *same* algebraic identity, just
with the parameter source shifted.

### `private theorem GeneralLinearMethod.witness_v_of_cesaro_inverse` (RENAMED)

Sub-lemma, not a textbook entity. Cosmetic `u → u'` rename of bound
variable. No semantic change.

## Dead ends

* **First compilation attempt failed** with `expected token` at line 154
  due to `B𝟙` (mathematical bold-1, U+1D7D9) appearing as part of an
  identifier name. Renamed to `B1` throughout the new
  `cesaro_residual_tendsto_zero` body. (Minor: unicode `𝟙` is fine
  as an *operator* but causes parser issues as a *suffix* of an
  identifier.)
* **Second compilation attempt failed** with rewrite failure in the
  `V^k *ᵥ u' = u'` induction step. Wrong rewrite order:
  `rw [pow_succ, ← Matrix.mulVec_mulVec, ih, hVu']` — but after
  `← mulVec_mulVec` the goal is `V^k *ᵥ V *ᵥ u' = u'`, where `ih`
  doesn't match (LHS has `V *ᵥ u'`, not `u'`). Fix: swap to
  `[..., hVu', ih]` so that `hVu'` reduces inner `V *ᵥ u'` to `u'`
  first. The existing `cesaro_orthogonal_to_VT_fixed` (cycle 097)
  uses this same pattern correctly — should have grep'd for it
  first instead of guessing.

## Discovery

* **Identifier hygiene**: unicode `𝟙` works as an operator (`Matrix.one`-like)
  but breaks parsing as the suffix of an ASCII identifier. Stick to
  ASCII identifiers (`B1`, `Y_int`, etc.) and reserve unicode for
  operators or standalone notation.
* **Rewrite ordering for inductive matrix-power identities**:
  `V^(k+1) *ᵥ u = V^k *ᵥ V *ᵥ u` (after `pow_succ` + `← mulVec_mulVec`)
  always wants the *inner* `V *ᵥ u` reduced first via the
  per-step hypothesis, then the *outer* `V^k *ᵥ u` via the IH.
  Pattern is reusable for all `(transpose-fixed | fixed)`-style
  power induction in matrix mulVec.
* **Existential conclusions sidestep uniqueness gaps**: when a
  textbook proof identifies two existentially-bound vectors
  implicitly, the formal closure can often skip the identification
  by witnessing the conclusion with one of them. Useful pattern
  for future "auxiliary witness" gaps (e.g. potentially in §515,
  §520 stability proofs).

## Suggested next approach

* `thm:514A` is closed. The next §514 target is `lem:515A`
  ("stability and consistency imply convergence") — the *converse*
  of `thm:514A`. This will need the same `IsConvergent` machinery
  but in the other direction: given `IsStable + IsConsistent`,
  construct the convergence-witness vector and prove the output
  Tendsto. Cycle 098's stage-limit clause may need to be *constructed*
  (rather than consumed) as part of the conclusion.
* The unused `_hPre` parameter in `convergent_preconsistent_isConsistent`
  is noted in the docstring as a stealth strengthening. A future
  cycle could expose a sharper variant
  `convergent_isConsistent : IsConvergent → IsConsistent` (one-line
  delegation), but the textbook signature is preserved as the
  primary deliverable. Decide via planner.
* Aristotle Jobs A/B/C are still in flight at cycle close. Their
  results may be useful for the planner to compare against the
  manual proof for any future cleanup, but not load-bearing.
* The deprecation warnings on `Matrix.toEuclideanLin_apply`
  (lines 334, 384, in cycle 097's `exists_inverse_of_cesaro_zero`)
  are now visible in every build. A future cleanup cycle could
  migrate to `Matrix.toLpLin_apply`. Low priority — purely cosmetic.
