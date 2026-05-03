# Cycle 096 Strategy — close `V·u' = u'` partial bridge for `thm:514A`

## Context: where we are

* **Branch tip**: `dcdadee Cycle 095 — close sub-lemma B`.
* **Sorry count**: **2**, both in `OpenMath/Chapter5/Section514.lean`:
  * line 157 — `cesaro_residual_tendsto_zero` (sub-lemma C).
  * line 180 — `exists_inverse_of_cesaro_zero` (sub-lemma D, mean-ergodic infrastructure gap).
* **Cycle 095** closed sub-lemma B (`glmConstOneIterate_closed_form`)
  cleanly via induction. Score: +1.
* **Open blockers** for sub-lemma C (per `.prover-state/issues/`):
  * `u_prime_equals_u_bridge.md` — `u'` (from `IsConvergent`) and `u`
    (from `IsPreconsistent`) are not automatically equal.
  * `cesaro_inverse_I_minus_V.md` — sub-lemma D needs multi-cycle
    mean-ergodic theorem in finite-dim; defer.

## Recent score pattern — read this carefully

| Cycle | Score | Pattern |
|-------|-------|---------|
| 091   | +2    | Closed deliverable |
| 092   | **−2**| **REVERTED — sorry count 0→3 on incomplete scaffold** |
| 093   | +2    | Closed deliverable |
| 094   | **−2**| **REVERTED — sorry count 0→3 on thm:514A scaffold** |
| 095   | +1    | Closed one sorry (3→2) |

**The lesson is brutal and explicit**: cycles that *add* sorries to
new scaffolds get scored **−2 (revert)**. Cycles that *close* sorries
or add sorry-free new deliverables score positive. Cycle 096 must
end either at sorry count ≤ 2 *or* with a sorry-free new theorem
added. **Do NOT introduce new sorries under any circumstance.**

## Primary deliverable: `convergence_witness_isVfixed`

Add a new private theorem to `OpenMath/Chapter5/Section514.lean`:

```lean
/-- Half of the `u' = u` bridge: the convergence-witness vector
extracted from `M.IsConvergent` (applied to the trivial IVP
`y'(x) = 1, y(0) = 0, yex = id`) is a fixed point of `M.V`.

This is a partial step toward `thm:514A`; the full bridge `u' = u`
to the preconsistency vector remains open — see
`.prover-state/issues/u_prime_equals_u_bridge.md`. -/
private theorem GeneralLinearMethod.convergence_witness_isVfixed
    {s r : ℕ} (M : GeneralLinearMethod s r)
    (hConv : M.IsConvergent) :
    ∃ u' : Fin r → ℝ, u' ≠ 0 ∧ M.V *ᵥ u' = u' := by
  ...
```

This is **a fresh closed lemma** — it does not change the existing
sorry count of 2, and it makes documented progress toward closing
sub-lemma C in cycle 097. It is the cycle-095 worker's recommended
next step (option 1 in `task_results/cycle_095.md` §"Suggested next
approach").

Note: derive `hStable` inline via `M.convergent_isStable hConv`
(cycle 093) inside the proof so the public signature is minimal.

### Proof skeleton (follow this literally)

#### Step 1 — extract `u'` from `IsConvergent` at the trivial IVP

Apply `hConv` with:
* `f := fun _ : ℝ => (1 : ℝ)` (constant 1).
* `L := (0 : NNReal)`. A constant function is `LipschitzWith 0`.
  - Lookup: `LipschitzWith.const`, or write
    `intro a b; simp [edist_dist, dist_self]`.
* `x₀ := (0 : ℝ)`, `y₀ := (0 : ℝ)`, `yex := id`.
* `yex x₀ = y₀`: `rfl` (since `id 0 = 0`).
* `∀ x, HasDerivAt yex (f (yex x)) x` = `∀ x, HasDerivAt id 1 x`:
  use `hasDerivAt_id'` or `hasDerivAt_id`.

Destructure: `obtain ⟨u', hu'_ne, hConv'⟩ := hConv ...`.

#### Step 2 — instantiate `hConv'` at `φ ≡ 0`, `x = 1`, `Y := glmConstOneIterate (1/n)`

Apply `hConv'` with:
* `φ := fun (_ : ℝ) (_ : Fin r) => (0 : ℝ)`.
* The φ-tendsto hypothesis: `∀ i, Tendsto (fun h => 0) (nhds 0)
  (nhds (u' i * 0))`. Simplify: `u' i * 0 = 0`, RHS is `nhds 0`,
  LHS is constant 0. Use `tendsto_const_nhds`.
* `x := (1 : ℝ)`, `hx : (0 : ℝ) < 1` is `zero_lt_one`.
* `Y := fun n m => M.glmConstOneIterate ((1 - 0 : ℝ) / n) m`
  = `fun n m => M.glmConstOneIterate (1 / (n : ℝ)) m`.
* The Y-spec hypothesis: for each `n > 0`,
  - `Y n 0 = φ ((1 - 0) / n) = 0`. By definition of
    `glmConstOneIterate` at 0: `M.glmConstOneIterate h 0 = fun _ => 0`.
    `funext i; rfl` should close it (or `simp [GeneralLinearMethod.glmConstOneIterate]`).
  - `M.IsGLMSolution (1/n) (fun _ => 1) (Y n)`: cite
    `M.glmConstOneIterate_isGLMSolution (1 / (n : ℝ))`.

Conclusion: `Tendsto (fun n => M.glmConstOneIterate (1/n) n) atTop
              (nhds (fun i => u' i * id 1))` = `nhds u'`.

Name this `hY_lim`. **Note**: the conclusion is in terms of the
*function* `fun i => u' i * 1`. Simplify to `u'` via `funext i;
ring` inside a congruence rewrite, or use `Filter.Tendsto.congr_dist`
or just `convert hY_lim using 2; funext i; ring` style.

#### Step 3 — apply continuity of `M.V *ᵥ ·` to lift the limit

`M.V *ᵥ ·` is continuous on `Fin r → ℝ`. Search Mathlib first:
* `lean_local_search "Continuous Matrix.mulVec"` — check if
  `Continuous.matrix_mulVec` or `Matrix.continuous_mulVec_left`
  exists.
* If not findable in 10 minutes, build the inline helper:

```lean
private lemma _root_.Matrix.tendsto_mulVec {r : ℕ}
    (V : Matrix (Fin r) (Fin r) ℝ) {ι : Type*} {l : Filter ι}
    {f : ι → Fin r → ℝ} {a : Fin r → ℝ}
    (hf : Tendsto f l (nhds a)) :
    Tendsto (fun n => V *ᵥ f n) l (nhds (V *ᵥ a)) := by
  refine tendsto_pi_nhds.mpr (fun i => ?_)
  simp only [Matrix.mulVec, dotProduct]
  exact tendsto_finset_sum _
    (fun j _ => ((tendsto_pi_nhds.mp hf) j).const_mul (V i j))
```

Conclude: `hVY_lim : Tendsto (fun n => M.V *ᵥ M.glmConstOneIterate (1/n) n) atTop (nhds (M.V *ᵥ u'))`.

#### Step 4 — algebraic identity using closed form

Build a separate helper lemma:

```lean
private lemma GeneralLinearMethod.V_mulVec_glmConstOneIterate_eq
    {s r : ℕ} (M : GeneralLinearMethod s r) (h : ℝ) (n : ℕ) :
    M.V *ᵥ M.glmConstOneIterate h n =
      M.glmConstOneIterate h n
      + h • (M.V ^ n *ᵥ (M.B *ᵥ (fun _ => 1)) - M.B *ᵥ (fun _ => 1)) := by
  ...
```

The cleanest path is a direct induction on `n` mirroring cycle 095's
`glmConstOneIterate_closed_form` proof structure:

* **Base** (`n = 0`): both sides reduce to `0` (LHS: `V *ᵥ 0`; RHS:
  `0 + h • (I *ᵥ B𝟙 - B𝟙) = 0` since `pow_zero`, `Matrix.one_mulVec`,
  `sub_self`, `smul_zero`).
* **Inductive step**: rewrite both sides via
  `glmConstOneIterate_closed_form` (cycle 095 lemma at line 96), then
  use `Finset.sum_range_succ` to peel off the new term, plus
  `pow_succ`, `Matrix.mulVec_mulVec` to merge `V * V^k`.

Alternative (if induction route is messy): start from
`glmConstOneIterate_closed_form` on the LHS, use
`Matrix.mulVec_smul`, `Matrix.mulVec_sum`, then re-index
`Σ_{k<n} V^(k+1) *ᵥ B𝟙 = Σ_{0<k≤n} V^k *ᵥ B𝟙
                       = Σ_{k<n} V^k *ᵥ B𝟙 - V^0 *ᵥ B𝟙 + V^n *ᵥ B𝟙`
via `Finset.sum_range_succ` (forward) and the cycle-95 closed form
(backward) to fold the residual term.

Estimated 30–80 LOC.

#### Step 5 — vanishing of the residual

`hStable.powerBound : ∃ K, ∀ n, ‖V^n‖ ≤ K` is already a lemma in
the file (line 220). Get `hPB : ∃ K : ℝ, ∀ n, ‖M.V ^ n‖ ≤ K` from
`hStable := M.convergent_isStable hConv`, then
`hPB := hStable.powerBound`.

Then:
* `‖V^n *ᵥ B𝟙 - B𝟙‖ ≤ ‖V^n *ᵥ B𝟙‖ + ‖B𝟙‖ ≤ K · ‖B𝟙‖ + ‖B𝟙‖ = (K+1) ‖B𝟙‖`.
  (Use `Matrix.linfty_opNorm_mulVec` or `norm_mulVec_le` — verify name
  with `lean_local_search "norm_mulVec"`. Or: pi-norm + Cauchy.)
* `(1/n) → 0` as `n → ∞` (via `tendsto_one_div_atTop_nhds_zero_nat`).
* `(1/n) • (bounded vector seq) → 0`. Combine via:
  - `Tendsto (1/n) → 0` and constant-bounded sequence ⇒ scalar
    multiplication tends to 0. Use `tendsto_zero_smul_of_tendsto_zero_of_bounded`
    or pi-direction squeeze.

If a direct lemma is hard to find, the cleanest approach is
componentwise: `tendsto_pi_nhds`, then for each `i`,
`|((1/n) • residual n) i| ≤ (1/n) · ‖residual n‖ ≤ (1/n) · (K+1)·‖B𝟙‖ → 0`.
Use `squeeze_zero` with bounds 0 and `(1/n) · (K+1) · ‖B𝟙‖`.

Name this `h_residual_vanish : Tendsto (fun n => (1/n) • (V^n *ᵥ B𝟙 - B𝟙)) atTop (nhds 0)`.

#### Step 6 — close `M.V *ᵥ u' = u'`

Combine:
* From Step 4: `M.V *ᵥ Y n n = Y n n + (1/n) • (V^n *ᵥ B𝟙 - B𝟙)`
  pointwise in `n` (where `Y n m := M.glmConstOneIterate (1/n) m`).
* `Tendsto (fun n => Y n n) atTop (nhds u')` (Step 2).
* `Tendsto (fun n => (1/n) • residual) atTop (nhds 0)` (Step 5).
* By `Filter.Tendsto.add`: `Tendsto (fun n => Y n n + (1/n) • residual) atTop (nhds (u' + 0)) = nhds u'`.
* By Step 4 rewriting: this equals
  `Tendsto (fun n => M.V *ᵥ Y n n) atTop (nhds u')`.
* But also from Step 3: `Tendsto (fun n => M.V *ᵥ Y n n) atTop (nhds (M.V *ᵥ u'))`.
* By `tendsto_nhds_unique`: `M.V *ᵥ u' = u'`.

Pack: `exact ⟨u', hu'_ne, hVu'_eq_u'⟩`.

### Estimated complexity

* Step 4 helper (`V_mulVec_glmConstOneIterate_eq`): 30–80 LOC.
* Step 3 inline continuity helper: 5–15 LOC (or a one-line
  Mathlib citation if the name is found).
* Steps 1–2 (IsConvergent unwinding): 30–60 LOC.
* Steps 5–6 (residual vanish + tendsto unique): 30–50 LOC.
* **Total**: 100–200 LOC. Within budget.

## NON-NEGOTIABLE rules for this cycle

### Rule 1 — No new sorries

If `convergence_witness_isVfixed` does not close cleanly:
* Do **NOT** commit it with `sorry` in the body.
* Do **NOT** add sub-helpers with `sorry` in their bodies.
* Use `lean_multi_attempt` and the search tools liberally — but if
  after substantial effort (~3 hours of cycle time) a sub-step
  refuses to close, **abort** the lemma.

The cycle-094 score (−2) was triggered by exactly this pattern. The
cycle-095 worker explicitly warned: *"better to land [the safe
deliverable] clean than to ship a broken edit"*.

### Rule 2 — Do NOT touch the existing two sorries

The sorries at `Section514.lean:157` and `:180` are **gated on
multi-cycle infrastructure** (per `cesaro_inverse_I_minus_V.md`,
`u_prime_equals_u_bridge.md`). Do not attempt them this cycle.
Closing the partial bridge `V·u' = u'` is sufficient cycle progress.

### Rule 3 — Verify lemma names before relying on them

Cycle-068 consultancy notes flag this rule explicitly. Every Mathlib
lemma cited in this strategy (`Matrix.linfty_opNorm_mulVec`,
`tendsto_zero_smul_of_tendsto_zero_of_bounded`,
`Continuous.matrix_mulVec`, `tendsto_one_div_atTop_nhds_zero_nat`,
`hasDerivAt_id'`, `LipschitzWith.const`) is a best-effort guess.
**Verify each with `lean_local_search` or `lean_loogle` before
using.** If a name doesn't exist, use the search tools to find the
correct one.

### Rule 4 — Aristotle policy this cycle

`Section514.lean` Step 4's algebraic identity
(`V_mulVec_glmConstOneIterate_eq`) is a textbook-mechanical sum
manipulation — exactly the kind of proof Aristotle handles well. If
Step 4 stalls after 30 minutes of manual work:
* Submit a single Aristotle job for `V_mulVec_glmConstOneIterate_eq`
  with the closed-form rewrite + reindex hints (`Finset.sum_range_succ`,
  `pow_succ`, `Matrix.mulVec_sum`).
* Sleep 30 min. One check after wake-up. Don't poll.
* If Aristotle returns a proof, incorporate. If not, fall back to
  manual induction on `n`.

Do **NOT** submit Step 1–3 to Aristotle — they require IsConvergent
unwinding which Aristotle's premise selection isn't tuned for.

## Backup plan (only if Step 1 IsConvergent unwinding fails)

If after ~2 hours the IsConvergent application in Step 1 cannot
close (e.g. type mismatches that resist all `lean_multi_attempt`
attempts), abort `convergence_witness_isVfixed` and fall back to:

**Backup deliverable**: write a *standalone* sorry-free helper lemma
in `Section514.lean` that future cycles will need. Specifically:

```lean
/-- Cesàro-of-power-bounded vector tends to zero in the residual
direction: `(1/n) • (V^n *ᵥ w - w) → 0` for any power-bounded `V`. -/
private lemma _root_.Matrix.cesaro_residual_vanish_of_power_bounded
    {r : ℕ} {V : Matrix (Fin r) (Fin r) ℝ}
    (hPB : ∃ K : ℝ, ∀ n, ‖V ^ n‖ ≤ K) (w : Fin r → ℝ) :
    Tendsto (fun n : ℕ => (1 / (n : ℝ)) • (V ^ n *ᵥ w - w))
      atTop (nhds 0) := by
  ...
```

This is **Step 5** of the primary deliverable, hoisted to a
standalone lemma. It is genuinely useful (will be used in any future
ergodic-style argument for §514/§515) and is closable with pure
Mathlib techniques (no IsConvergent unwinding). Estimated 30–60 LOC.

## What NOT to do

* Do **NOT** introduce any new sorries (rule 1).
* Do **NOT** attempt sub-lemma C (`cesaro_residual_tendsto_zero`) or
  sub-lemma D (`exists_inverse_of_cesaro_zero`) — both are
  multi-cycle infrastructure dependencies.
* Do **NOT** add the AN-stability infrastructure or any §530/§550/
  §551 entities. Stay focused on `thm:514A`'s partial bridge.
* Do **NOT** modify `IsConvergent`'s signature (cycle 092 already did
  the φ quantifier repair; further tweaks risk breaking thm:513A).
* Do **NOT** strengthen `IsConvergent` with joint Lipschitz / global
  C¹ / uniform M-bound preemptively. The §513/§514/§515 textbook
  proofs use only the textbook hypotheses; if a Lean proof needs
  more, file a parallel issue (per `glm_convergence_witness_deferred.md`
  precedent).
* Do **NOT** raise `maxHeartbeats` above 200000.
* Do **NOT** introduce `axiom` or `constant` declarations.
* Do **NOT** modify `scripts/autonomous_loop.py` or other loop
  infrastructure.
* Do **NOT** trust the strategy's Mathlib lemma names blindly.
  Verify each with `lean_local_search` before relying on them.
* Do **NOT** chase `MulOpposite`, `LinearMap`, or category-theory
  abstractions for the matrix-power algebra — stay in `Matrix.mulVec`
  / `Matrix.HPow` land per cycle 095's clean idioms.

## Faithfulness check (pre-commit)

For `convergence_witness_isVfixed`:

* **Entity ID**: not a textbook entity — this is a Lean-side helper
  toward closing `thm:514A`. No JSON to consult.
* **Statement coverage**: the lemma asserts that the convergence
  witness `u'` (existential clause of `IsConvergent` instantiated at
  the trivial IVP) satisfies `V *ᵥ u' = u'`. This is a partial
  consequence of Butcher's §514 textbook argument (one half of the
  `u' = u` bridge). Document the partial nature in the docstring
  with reference to `.prover-state/issues/u_prime_equals_u_bridge.md`.
* **Tautology check**: the conclusion `V *ᵥ u' = u'` does not appear
  as a hypothesis. ✓
* **Hypothesis strength check**: requires only `hConv`. Power-
  boundedness is derived inline via `hConv → IsStable → powerBound`.
  No extra hypothesis beyond the textbook setup.
* **Identity check**: the proof is a multi-step argument involving
  IsConvergent unwinding + algebraic manipulation + limit uniqueness.
  Definitely not `exact h`.
* **Absent theorem check**: no comments promise content not in the
  file. ✓

For `V_mulVec_glmConstOneIterate_eq` (Step 4 helper):

* Pure algebraic identity (textbook-mechanical). Faithfulness check
  trivial.

For (potential) backup `Matrix.cesaro_residual_vanish_of_power_bounded`:

* Pure Mathlib-style limit lemma. Faithfulness check trivial.

## Cycle 097 plan preview

After cycle 096 lands `convergence_witness_isVfixed`:
* Cycle 097 will attempt the `U·u' = 𝟙` half of the bridge via a
  smarter IsConvergent application (see
  `u_prime_equals_u_bridge.md` option (b)).
* Cycle 098 will combine both halves with a preconsistency-vector
  uniqueness argument (option (c)) to close the full `u' = u`
  bridge, then close sub-lemma C.
* Sub-lemma D (mean-ergodic) remains a separate multi-cycle effort.

This puts `thm:514A` at full closure in ~3–5 more cycles, in line
with the issue files' estimates.

## Definition of done

Cycle 096 success bar:
1. **Sorry count ≤ 2** (no new sorries).
2. **`lake env lean OpenMath/Chapter5/Section514.lean`** clean.
3. **`#print axioms` on the new theorem(s)** shows
   `[propext, Classical.choice, Quot.sound]` only.
4. **`task_results/cycle_096.md`** documents the deliverable, the
   IsConvergent unwinding pattern (so cycle 097 can reuse it), and
   the residual proof approach.
5. **`u_prime_equals_u_bridge.md`** updated to mark the partial
   bridge `V·u' = u'` as DONE, leaving `U·u' = 𝟙` and uniqueness as
   the remaining work.

Stretch (only if primary lands well before time): begin sketching the
`U·u' = 𝟙` extraction strategy in `u_prime_equals_u_bridge.md` —
**without** committing any Lean code for it. Reserve the actual
proof attempt for cycle 097.

## Final note on score expectation

A clean cycle 096 with `convergence_witness_isVfixed` closed adds a
useful new lemma without sorry-count regression. Expected score:
**+1 to +2**. If the backup deliverable
(`Matrix.cesaro_residual_vanish_of_power_bounded`) is what lands
instead, expected score: **+1** (still useful infrastructure, but
less direct §514 progress).

If neither lands, expected score: **0 or below**. To avoid a
zero-changes cycle (forbidden by CLAUDE.md), at minimum update
`u_prime_equals_u_bridge.md` with a detailed account of what was
attempted and why each step blocked — this counts as the required
"write an issue" deliverable.
