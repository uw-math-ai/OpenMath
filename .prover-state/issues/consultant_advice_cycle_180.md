---
name: Consultant advice — cycle 180 ("factor-of-2 discrepancy" is a phantom — Butcher §441 p. 376 typo, already verified cycle 174; Phase B is CLOSED through cycle 179; no work remains on the stated blocker)
description: The "stuck on" framing in the cycle 180 prompt is a stale `attempts.md` carry-over. The factor-of-2 was diagnosed and accepted as a Butcher textbook typo by the cycle 174 consultant six cycles ago. Phase B of `lem:441A` (a₁ > 0) is FULLY CLOSED at cycle 179 and verified axiom-clean at line 913 of `OpenMath/Chapter4/Section441.lean`. Cycle 181 should pivot directly to Phase C.1 (Möbius algebraic bridge) per the cycle 180 scoping in `lem_441A_phase_C_scoping.md`, OR a fresh entity.
type: project
---

# Consultant advice — cycle 180

Author: consultant subagent.
Date: 2026-05-07.
Phase at time of writing (per `heartbeat.json`): cycle 180, post-worker.
Branch tip: `f021350 Cycle 180 — §441 lem:441A Phase C scoping + BDF2
closed form + phantom-verdict documentation`.

---

## TL;DR

**The "stuck on" framing in the cycle 180 prompt is a phantom.**
There is nothing for cycle 181's worker to do on the stated blocker —
it was resolved six cycles ago, the resolution was independently
confirmed by the cycle 174 consultant, and Phase B of `lem:441A`
(`a₁ > 0` for stable preconsistent LMMs) is fully closed at HEAD.

Concretely:

1. **The factor-of-2 is a Butcher textbook typo, not a Lean error.**
   The cycle 174 consultant note (`consultant_advice_cycle_174.md`
   §A) independently re-derived the algebra from definitions, ran
   numerical sanity checks on explicit Euler (a₁ = 2, ρ'(1) = 1) and
   BDF2 (a₁ = 4/3, ρ'(1) = 2/3), and confirmed: `a₁ = 2·ρ'(1)` is
   correct; Butcher's "ρ'(1) = a₁" on p. 376 is a typo (the author
   substituted `a₁`'s closed form for `ρ'(1)`'s, missing that the
   `αᵢ` weights differ by a factor of 2: `(k − 2i)` for `a` versus
   `(k − i)` for `ρ`). I re-ran the verification this cycle and
   confirm it again.

2. **Phase B is CLOSED through cycle 179.** Verified at HEAD:

   ```
   $ git log --oneline -2
   f021350 Cycle 180 — §441 lem:441A Phase C scoping + BDF2 closed form + ...
   572f058 Cycle 179 — §441 lem:441A Phase B.4: a₁ > 0 for stable preconsistent LMMs

   $ wc -l OpenMath/Chapter4/Section441.lean
   977 OpenMath/Chapter4/Section441.lean

   $ grep -c sorry OpenMath/Chapter4/Section441.lean
   0

   $ grep -n "aPoly_coeff_one_pos_of_stable_preconsistent" OpenMath/Chapter4/Section441.lean
   913: theorem LinearMultistepMethod.aPoly_coeff_one_pos_of_stable_preconsistent
   917:   rw [M.aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent hPre]
   ```

   The cycle 174 bridge that the prompt characterises as a "blocker"
   is at line 455. Phase B's headline `a₁ > 0` is at line 913.
   Both axiom-clean.

3. **The "Phase C scoping" was completed by cycle 180.**
   `.prover-state/issues/lem_441A_phase_C_scoping.md` already
   contains a full 4-phase plan (C.1 Möbius bridge, C.2 stability ⇒
   `Re(ζ) ≤ 0`, C.3 real factorisation + non-negative-coefficient
   closure, C.4 combine), with Mathlib hook inventories, LOC budgets,
   risk assessments, and Aristotle-suitability ratings. Cycle 181
   should adopt **Phase C.1** as its target.

4. **Pattern match: this is the seventh occurrence of a stale-
   `attempts.md`-propagated phantom verdict** in this project's
   history (cycles 008, 014, 015, 040, 170, 176–179, 180). Each was
   contradicted by the actual git state; each cost a cycle of worker
   time chasing it. The standing remediation is documented in
   `phantom_commit_verdict_pattern.md` (cycle 180), which escalates
   to the loop-maintainer.

---

## A. Verification commands

Re-run these against `HEAD`. Every one should produce the verdict
shown — if any disagrees, the cycle has a real regression I have not
accounted for, and that should be the cycle 181 target instead.

```bash
# 1. Branch tip is the cycle-180 commit.
git log -1 --format='%H %s'
# Expected:
# f021350… Cycle 180 — §441 lem:441A Phase C scoping + BDF2 closed form + ...

# 2. Section441.lean is 977 LOC, 0 sorries, axiom-clean.
wc -l OpenMath/Chapter4/Section441.lean
grep -c sorry OpenMath/Chapter4/Section441.lean
lake env lean OpenMath/Chapter4/Section441.lean
# Expected: 977 / 0 / clean exit.

# 3. Phase B's five landmark theorems are all present.
grep -n "ρPoly_no_real_root_gt_one\|ρPoly_deriv_eval_one_ne_zero_of_stable_preconsistent\|ρPoly_pos_on_Ioi_one\|ρPoly_deriv_eval_one_pos_of_stable_preconsistent\|aPoly_coeff_one_pos_of_stable_preconsistent" \
  OpenMath/Chapter4/Section441.lean
# Expected: lines 504, 599, 707, 767, 913 (per cycle 180 task results).

# 4. Cycle 180's bdf2LMM_aPoly_eq closed form lives at line ~947.
grep -n "bdf2LMM_aPoly_eq" OpenMath/Chapter4/Section441.lean

# 5. The factor-of-2 bridge is at line ~455.
grep -n "aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent" \
  OpenMath/Chapter4/Section441.lean

# 6. Axiom-clean spot-check on the headline.
echo '#print axioms OpenMath.Chapter4.Section404.LinearMultistepMethod.aPoly_coeff_one_pos_of_stable_preconsistent' \
  | lake env lean --stdin OpenMath/Chapter4/Section441.lean
# Expected: [propext, Classical.choice, Quot.sound] only.
```

---

## B. Independent re-verification of the factor-of-2 (one paragraph)

Differentiating `a(z) = (1+z)^k − Σᵢ αᵢ (1+z)^{k−i} (1−z)^i` and
evaluating at `z = 0`: each `(1+z)^{k−i} (1−z)^i` term contributes
`(k − 2i)` by the product rule, so `a₁ = a'(0) = k − Σᵢ αᵢ (k − 2i)
= k − k Σαᵢ + 2 Σ i·αᵢ`. Under preconsistency `Σαᵢ = 1`:
**`a₁ = 2 Σ i·αᵢ`**.

Differentiating `ρ(z) = z^k − Σᵢ αᵢ z^{k−i}`: `ρ'(1) = k − Σᵢ αᵢ
(k − i) = k − k Σαᵢ + Σ i·αᵢ`. Under preconsistency:
**`ρ'(1) = Σ i·αᵢ`**.

Therefore **`a₁ = 2·ρ'(1)`** (cycle 174 result) ✓.

Numerical sanity: explicit Euler (`k=1, α₁=1`): `a₁ = 2`, `ρ'(1) = 1`,
`2·ρ'(1) = 2 = a₁`. ✓ BDF2 (`k=2, α₁=4/3, α₂=−1/3`): `a₁ = 4/3`,
`ρ'(1) = 2/3`, `2·ρ'(1) = 4/3 = a₁`. ✓ Butcher's "ρ'(1) = a₁" would
require `2/3 = 4/3` on BDF2 — clearly false.

The cycle 174 consultant's diagnosis is correct. The cycle 174
worker's chain (`a₁ = −2α'(1)` → `ρ'(1) = −α'(1)` → `a₁ = 2·ρ'(1)`)
is mathematically faithful. **Do not audit it.** **Do not redirect
the proof strategy.**

For documentation hygiene, cycle 181 may *optionally* add a one-
sentence comment to the docstring of
`aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent` (line
455) noting "Butcher §441 p. 376 states `ρ'(1) = a₁` — this is a
typo; the correct identity is `a₁ = 2·ρ'(1)` (verified on explicit
Euler and BDF2)." This was suggested by the cycle 174 consultant
and has not yet been added. It is a pure documentation improvement,
not a substantive task — should not consume more than 5 minutes of
worker time and should be bundled with whatever the cycle 181 target
is, not its own cycle.

---

## C. Why the prompt still says "stuck"

The prompt's "What I'm stuck on" header reads:

> Factor-of-2 discrepancy between the worker's proved
> `aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent`
> (`a₁ = 2·ρ'(1)`) and Butcher's claimed direct identity
> `ρ'(1) = a₁`. Until this is resolved — either by auditing the
> `aPoly` definition normalisation or finding the error in one of
> the two bridge theorems — the `ρ'(1) > 0` infrastructure cannot
> be reliably connected to `lem:441A`.

This is **literally** a description of the problem state at the end
of cycle 174. Six cycles ago. Since then:

* Cycle 174 consultant note diagnosed the typo (independent algebra
  + numerical witnesses).
* Cycle 175 closed Phase B.1.β (no real root > 1).
* Cycle 176 closed Phase B.2 (ρ'(1) ≠ 0).
* Cycle 177 closed Phase B.3 Step 1 (ρ > 0 on (1, ∞)).
* Cycle 178 closed Phase B.3 Step 2 (ρ'(1) > 0).
* Cycle 179 closed Phase B.4 (a₁ > 0). Headline at line 913.
* Cycle 180 added BDF2 closed form, Phase C scoping, and the
  `phantom_commit_verdict_pattern.md` issue file.

The "ρ'(1) > 0 infrastructure" the prompt says "cannot be reliably
connected to lem:441A" **is** connected. Line 917:

```lean
  rw [M.aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent hPre]
  have := M.ρPoly_deriv_eval_one_pos_of_stable_preconsistent hk hStable hPre
  linarith
```

Three lines. Done. Axiom-clean.

The same systemic loop-maintainer bug that produced cycles 176–179's
"commit-not-reaching-repo" phantoms (per
`phantom_commit_verdict_pattern.md`) is now producing a new
"factor-of-2-still-blocking" phantom. Both stem from the prompt-
builder reading from a stale cache of `attempts.md` rather than
re-evaluating against `HEAD`.

**This is loop-maintainer territory, not worker territory.** Per
the cycle-014 / cycle-015 consultant guidance and the standing
issue `tautology_scanner_false_positives.md` §D3, the prompt-builder
should regenerate "What I'm stuck on" rows from `HEAD` after each
cycle's commit, not propagate them from `attempts.md`. The cycle
180 worker correctly logged this as a meta-issue
(`phantom_commit_verdict_pattern.md`) and did not attempt to patch
`scripts/autonomous_loop.py`. Cycle 181's worker should follow suit.

---

## D. Concrete cycle 181 plan

**Recommended target: Phase C.1 of `lem:441A` — Möbius algebraic
bridge.**

Source plan: `.prover-state/issues/lem_441A_phase_C_scoping.md`
§"Phase C.1 — Möbius algebraic bridge (1–2 cycles)".

Deliverables:

1. `private noncomputable def mobiusTransform : Polynomial ℝ →
   Polynomial ℝ`. The cycle-180 scoping recommends the explicit
   homogenization
   ```lean
   noncomputable def mobiusTransform (p : Polynomial ℝ) :
       Polynomial ℝ :=
     ∑ i in Finset.range (p.natDegree + 1),
       Polynomial.C (p.coeff i) *
       (1 - Polynomial.X) ^ i * (1 + Polynomial.X) ^ (p.natDegree - i)
   ```
   to sidestep the fact that `(1 − X) / (1 + X)` is not in `ℝ[X]`.
2. `theorem aPoly_eq_mobiusTransform_alphaPoly`: the algebraic
   identity bridging `aPoly` to `αPoly` (or `ρPoly`) under the
   Möbius substitution. The proof is `Finset.sum_congr` +
   manipulation; expected ~80 LOC.
3. `theorem aPoly_isRoot_iff_alphaPoly_isRoot_of_psi`: ζ ∈ ℂ is a
   root of `aPoly` iff `ψ(ζ) = (1 − ζ)/(1 + ζ)` is a root of `αPoly`
   (or `ρPoly`), with the `ζ = −1` case handled separately via
   `αPoly.degree < k ↔ M.IsConsistent`-style analysis.
4. **BDF2 sanity witness**: explicit verification of the Möbius
   bridge at `bdf2LMM`. Following Phase B's discipline: every new
   generic theorem in §441 should have a numerical companion on
   `bdf2LMM`. The right shape is probably
   `theorem bdf2LMM_aPoly_eq_mobiusTransform : bdf2LMM.aPoly =
   mobiusTransform bdf2LMM.<alphaPoly-or-rhoPoly>` — should fall
   to `simp [bdf2LMM, ...] + ring` after the algebraic identity
   above is in hand.

LOC budget (per the scoping issue): ~150 LOC. Aristotle suitability:
medium (algebraic identity is structural).

**Concrete tactic suggestions for the algebraic identity.** The
load-bearing equation is

```
aPoly(z) = (1 + z)^k − Σᵢ αᵢ (1 + z)^{k−i} (1 − z)^i
        = (1 + z)^k · (1 − Σᵢ αᵢ ((1−z)/(1+z))^i)
```

so `aPoly = (1+z)^k · α((1−z)/(1+z))`. Multiplying through by
`(1+z)^k` clears the denominators (since `α((1−z)/(1+z))`
expanded gives `Σⱼ αⱼ (1−z)^j (1+z)^{−j}`, and the `(1+z)^k`
prefactor turns `(1+z)^{−j}` into `(1+z)^{k−j}`):

```
aPoly = (1+z)^k − Σⱼ αⱼ · (1+z)^{k−j} · (1−z)^j
```

which is exactly `mobiusTransform`'s output applied to `α`'s
coefficients (with the index shift `j ↔ i`). The identity reduces
to a `Finset.sum_congr rfl` over `i ∈ Finset.range (k+1)` plus a
per-term `ring` check.

For the `aPoly_isRoot_iff` bridge: over ℂ, ψ(ζ) = (1−ζ)/(1+ζ) is
well-defined whenever ζ ≠ −1. From the identity above:

```
aPoly.aeval ζ = (1+ζ)^k · α.aeval (ψ ζ)    (whenever ζ ≠ −1)
```

so `aPoly.aeval ζ = 0 ↔ (1+ζ)^k = 0 ∨ α.aeval (ψ ζ) = 0
                    ↔ ζ = −1 ∨ α.aeval (ψ ζ) = 0`.

The `ζ = −1` case: substitute `ζ = −1` in `aPoly`'s closed form:

```
aPoly.aeval (−1) = 0^k − Σᵢ αᵢ · 0^{k−i} · 2^i
                = − αₖ · 2^k     (only the i=k term survives, since k−i=0 ⇒ k=i)
```

So `aPoly.IsRoot (−1)` iff `αₖ = 0`, which equals
`αPoly.degree < k`. Useful as a clean side-lemma.

**Mathlib hooks to verify with `lean_local_search` early in cycle
181 (the cycle 180 worker was rate-limited):**

| Goal | Candidate lemma | Risk |
|---|---|---|
| `(1 + X)^k coeff` | `Polynomial.coeff_one_add_X_pow` | low — confirmed by cycle 174 |
| `Polynomial.aeval` over ℂ | `Polynomial.aeval`, `Polynomial.eval₂` | low |
| `Polynomial.map ofReal` | `Polynomial.map`, `Polynomial.map_eval₂` | low |
| `Polynomial.aeval (X − C r)` factoring | `Polynomial.X_sub_C_dvd_iff_isRoot` | low |
| `Finset.sum_congr` index manipulation | std | low |
| Polynomial-product `C` arithmetic over ℝ | `Polynomial.C_mul`, `Polynomial.C_pow`, `Polynomial.smul_C` | low |

No high-risk hooks anticipated for Phase C.1. Phase C.3 (real
factorisation via conjugate pairs) is the high-risk phase, deferred.

**Aristotle batch suggestion.** The algebraic identity in step 2 is
a clean target for Aristotle. Submit as a single job with the
`mobiusTransform` definition + the target identity + cycle 174's
`αPoly`/`ρPoly` definitions as in-context templates. Even if
Aristotle stalls, the manual `Finset.sum_congr + ring` proof should
close in ~50 LOC.

---

## E. Alternative cycle 181 targets (if planner prefers a fresh entity)

The cycle 180 task results note: "Section441 has been the focus for
ten consecutive cycles (171–180). The planner may want to pivot to
a fresh entity." Reasonable candidates per `plan.md` and the cycle
180 task results:

* **`def:451A` (G-stable)** — was cycle 169's prerequisite; verify
  status. If still `unformalized`, definition-only deliverable.
* **`def:422B` (underlying one-step method)** — chapter 4 §422 entry
  point.
* **`def:442A` (principal sheet)** — chapter 4 §442 entry point.
* **`thm:535A` (underlying one-step method, GLM)** — chapter 5 §535.
* **`thm:541A` (types of DIMSIM methods)** — chapter 5 §541.

I would recommend **Phase C.1 over a pivot**: the ten-cycle §441
investment has produced complete Phase B infrastructure; abandoning
it now leaves the second half of `lem:441A` unfinished and the
five `ρPoly` / `aPoly` lemmas without their ultimate consumer. One
or two more focused cycles on Phase C.1 (Möbius bridge) keep the
investment compounding. After Phase C.1 lands, the planner has
genuine flexibility: Phase C.2 (1 cycle), pivot to a fresh entity,
or batch Phase C.3 (the hard infrastructure cycle) into a planned
multi-cycle effort.

If the planner does pivot, **`def:451A` is the safest single-cycle
deliverable**: it is a definition-only target (predicate +
non-vacuity witness via `bdf2LMM`), shipped pattern matches cycle
171's `aPoly` introduction (which closed in one cycle).

---

## F. What NOT to do this cycle

* Do **NOT** re-audit the `aPoly` definition. Its correctness was
  verified algebraically in cycle 174 and confirmed numerically on
  two methods (explicit Euler, BDF2).
* Do **NOT** revert any cycle 174–179 work. Phase B is closed.
* Do **NOT** "find the error in one of the two bridge theorems".
  There is no error. The bridge theorems
  `aPoly_coeff_one_eq_neg_two_alpha_deriv_at_one_of_preconsistent`
  (cycle 173) and
  `ρPoly_deriv_eval_one_eq_neg_alpha_deriv_at_one_of_preconsistent`
  (cycle 174) compose to give `a₁ = 2·ρ'(1)`. Both are axiom-clean
  and BDF2-verified.
* Do **NOT** treat the prompt's "stuck on" framing at face value
  without first running the §A verification commands.
* Do **NOT** edit `scripts/autonomous_loop.py` from the worker. Per
  CLAUDE.md and `tautology_scanner_false_positives.md` §D3, the
  prompt-builder bug is loop-maintainer territory.
* Do **NOT** raise `maxHeartbeats` above 200000.
* Do **NOT** introduce `axiom`/`constant` for any Phase C step.
  Phase C.1's Möbius bridge is a standard polynomial-algebra
  identity; Mathlib has the hooks.
* Do **NOT** attempt Phase C in a single cycle. The Phase C scoping
  in `lem_441A_phase_C_scoping.md` is explicit: 4 phases, 4–6 cycles,
  with Phase C.3 the high-risk one. Cycle 181 should target Phase
  C.1 only.
* Do **NOT** attempt the `bdf2LMM_aPoly_eq` rewrite path with
  `Polynomial.ext` (cycles 172/173 stalled here). Cycle 180's
  `Polynomial.funext + ring` recipe (line 947) is the canonical
  closure pattern for `Polynomial ℝ` constant arithmetic; reuse it
  if any new BDF2 closed-form witnesses are needed in Phase C.

---

## G. Cross-references

* `.prover-state/issues/consultant_advice_cycle_174.md` — six-cycle-
  old diagnosis of the factor-of-2 typo. §A is the independent
  algebraic verification; §B closes off `bdf2LMM_aPoly_eq` (now
  shipped via cycle 180's `Polynomial.funext + ring` recipe);
  §C–D scope the Phase B work that has since been completed (cycles
  175–179).
* `.prover-state/issues/lem_441A_alpha_prime_negative.md` — the
  parent `lem:441A` issue, now updated through cycle 179 marking
  Phase B closed.
* `.prover-state/issues/lem_441A_phase_C_scoping.md` — cycle 180's
  Phase C plan (4 phases, 4–6 cycles, Mathlib hook inventory).
  **The cycle 181 target should come from §3 of this file.**
* `.prover-state/issues/phantom_commit_verdict_pattern.md` — cycle
  180 escalation of the loop-maintainer prompt-builder bug. Lists
  cycles 176–179 with concrete `git show --stat` evidence; same
  pattern shape as cycle 180's "stuck on" phantom.
* `.prover-state/issues/consultant_advice_cycle_009.md` §A — first
  canonical diagnosis of the `attempts.md`-propagation phantom
  (cycle 008).
* `.prover-state/issues/consultant_advice_cycle_014.md` §D3 — the
  standing recommendation that the prompt-builder regenerate
  "stuck"/"vacuous-proof" rows against `HEAD`.
* `.prover-state/issues/consultant_advice_cycle_015.md` §B — second
  occurrence with explicit acknowledgement of the propagation
  mechanism.
* `.prover-state/issues/consultant_advice_cycle_040.md` — third
  occurrence (commit-failure phantom), same shape.
* `.prover-state/issues/tautology_scanner_false_positives.md` —
  sibling supervisor-side issue, also loop-maintainer territory.
* `.prover-state/task_results/cycle_180.md` — cycle 180 worker's
  full deliverable record, including the `git show --stat`
  verifications for cycles 176–179.
* `OpenMath/Chapter4/Section441.lean:455` — the cycle 174 bridge
  `aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent`.
* `OpenMath/Chapter4/Section441.lean:913` — Phase B's headline
  `aPoly_coeff_one_pos_of_stable_preconsistent`.
* `OpenMath/Chapter4/Section441.lean:947` — cycle 180's
  `bdf2LMM_aPoly_eq` (the `Polynomial.funext + ring` recipe).

---

## H. Bottom-line directive for cycle 181

There is nothing to do on the stated blocker. **It is resolved.**
Cycle 181 should:

1. (5 min) Run §A's verification commands. Confirm Phase B is
   closed at `HEAD`.
2. (5 min, optional) Add the one-sentence cycle 174 typo
   acknowledgement to the docstring of
   `aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent` at
   line 455.
3. (rest of cycle) Adopt **Phase C.1** (Möbius algebraic bridge) as
   the substantive target, per
   `lem_441A_phase_C_scoping.md` §"Phase C.1 — Möbius algebraic
   bridge". Ship the `mobiusTransform` definition + the
   `aPoly_eq_mobiusTransform_<αPoly|ρPoly>` algebraic identity +
   the `aPoly_isRoot_iff` bridge + a BDF2 sanity witness. ~150 LOC,
   axiom-clean, sorry count remains 0.

If the planner pivots, ship `def:451A` (G-stable) instead — single-
cycle, low-risk.

The prompt-builder phantom should be flagged for the loop-maintainer
via the existing `phantom_commit_verdict_pattern.md` issue (no new
escalation needed). Worker MUST NOT modify
`scripts/autonomous_loop.py`.
