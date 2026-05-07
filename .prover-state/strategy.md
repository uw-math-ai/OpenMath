# Strategy — Cycle 181

## TL;DR

**Pivot to Phase C.1 of `lem:441A`** — the Möbius algebraic bridge
between `aPoly` and `αPoly`/`ρPoly`. Phase B is fully closed (cycle 179
shipped `a₁ > 0`); cycle 180 wrote the Phase C scoping plan
(`.prover-state/issues/lem_441A_phase_C_scoping.md`) and closed the
long-deferred BDF2 closed form. Cycle 181's worker must:

1. **(Priority 0, mandatory)** Verify git state directly before
   trusting any "stuck on" framing in this prompt. The supervisor's
   prompt-builder has been propagating phantom verdicts for five
   consecutive cycles (176–180); see
   `.prover-state/issues/phantom_commit_verdict_pattern.md`.

2. **(Priority 1, main deliverable)** Ship Phase C.1 — the
   `mobiusTransform` definition, the algebraic bridge identity
   `aPoly = mobiusTransform αPoly` (or `ρPoly` — see §2 below for
   the sign/normalisation analysis), the `aPoly_isRoot_iff`
   complex-side bridge, and a BDF2 numerical sanity witness.

3. **(Priority 2, optional)** Add a one-sentence Butcher §441 p. 376
   typo acknowledgement to the docstring of
   `aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent`
   (line 455 of `Section441.lean`). Suggested by the cycle 174
   consultant; not yet shipped.

LOC budget: ~150 LOC for Priority 1, +5 LOC for Priority 2.
Sorry count target: 0 → 0 (no new sorries).

---

## Priority 0 — Phantom-verdict verification (5 minutes)

Run these verbatim and confirm each output before doing any other
work:

```bash
# 1. Branch tip is the cycle-180 commit.
git log -1 --format='%H %s'
# Expected: f021350… Cycle 180 — §441 lem:441A Phase C scoping + ...

# 2. Section441.lean is 974 LOC, 0 sorries, axiom-clean.
wc -l OpenMath/Chapter4/Section441.lean
grep -c sorry OpenMath/Chapter4/Section441.lean

# 3. Phase B's five landmark theorems are present.
grep -n "ρPoly_no_real_root_gt_one\|ρPoly_deriv_eval_one_ne_zero_of_stable_preconsistent\|ρPoly_pos_on_Ioi_one\|ρPoly_deriv_eval_one_pos_of_stable_preconsistent\|aPoly_coeff_one_pos_of_stable_preconsistent" OpenMath/Chapter4/Section441.lean

# 4. Cycle-180 BDF2 closed form is at line ~947.
grep -n "bdf2LMM_aPoly_eq" OpenMath/Chapter4/Section441.lean

# 5. Verify the file builds.
lake env lean OpenMath/Chapter4/Section441.lean
```

If any of these disagrees with the cycle 180 task results,
**stop and escalate** — there is a real regression that takes
priority over Phase C.1.

If all five pass, proceed to Priority 1. Append a one-line
"Cycle 181 confirmation" entry to `.prover-state/attempts.md` if
you notice a phantom verdict in this prompt's "What I'm stuck on"
or "Recent cycle history" sections (the prompt-builder bug
documented in `phantom_commit_verdict_pattern.md` may continue to
propagate).

---

## Priority 1 — Phase C.1: Möbius algebraic bridge (rest of cycle)

### What to ship

Add the following to `OpenMath/Chapter4/Section441.lean` (after
line ~974, in the existing `OpenMath.Chapter4.Section404` namespace
where `aPoly` and `ρPoly` already live):

#### Step 1 — `mobiusTransform` definition

```lean
/-- The Möbius transform of a polynomial `p ∈ ℝ[X]`, defined as the
homogeneous evaluation of `p` at `(1 − X, 1 + X)`. Used to bridge
`aPoly` and `αPoly`/`ρPoly` via the substitution
`ψ(z) = (1 − z) / (1 + z)` in §441.

Concretely,
`mobiusTransform p = Σᵢ p.coeff i · (1 − X)^i · (1 + X)^{n−i}`
where `n = p.natDegree`. -/
noncomputable def mobiusTransform (p : Polynomial ℝ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (p.natDegree + 1),
    Polynomial.C (p.coeff i) *
    (1 - Polynomial.X) ^ i * (1 + Polynomial.X) ^ (p.natDegree - i)
```

#### Step 2 — The algebraic bridge

The exact statement depends on a sign/normalisation analysis that
must be done FIRST (10 minutes). Here is the analysis:

Butcher's `α(w) = w^k − α₁ w^{k−1} − ⋯ − αₖ` (the §410 polynomial).
Our codebase has TWO §410-flavour polynomials:
- `αPoly` (`OpenMath/Chapter4/Section410.lean`) — verify by inspection.
- `ρPoly` (`OpenMath/Chapter4/Section441.lean:313`) — already proved
  `ρPoly = X^k − Σᵢ C(αᵢ) X^(k−(i+1))`.

The Möbius identity (textbook, §441 p. 376) is

```
a(z) = (1 + z)^k − Σᵢ αᵢ (1 + z)^(k−i) (1 − z)^i
     = (1 + z)^k · (1 − Σᵢ αᵢ ψ(z)^i)
     = (1 + z)^k · α(ψ(z))      where  ψ(z) = (1−z)/(1+z)
```

So `aPoly = mobiusTransform <whichever-of-αPoly-or-ρPoly-equals-α>`.
The right choice is the polynomial whose coefficients match Butcher's
`α(w) = w^k − α₁ w^(k−1) − ⋯ − αₖ` directly. **Inspect
`Section410.lean` first** to determine which (or build a thin
wrapper if neither matches exactly).

The target identity:

```lean
theorem aPoly_eq_mobiusTransform_αPoly (M : LinearMultistepMethod k) :
    M.aPoly = mobiusTransform M.αPoly := by
  -- (or with M.ρPoly on the RHS, if that matches Butcher's α)
  sorry  -- ← do NOT ship this; close it before committing
```

The proof is a `Polynomial.funext + ring`-style argument, possibly
with a `Finset.sum_congr` for the index alignment. Likely ~80 LOC.

**Note on degree alignment**: `mobiusTransform p` uses
`p.natDegree + 1` summands, but `aPoly`'s sum is over `Fin k`. If
`αPoly.natDegree = k`, alignment is direct; if it differs (e.g.
when `αₖ = 0`), use `Polynomial.coeff_eq_zero_of_natDegree_lt` to
extend the sum.

#### Step 3 — Complex-side root bridge

```lean
/-- Möbius-side root correspondence: `ζ ∈ ℂ \ {-1}` is a root of
`aPoly` iff `ψ(ζ) := (1−ζ)/(1+ζ)` is a root of `αPoly` (or whichever
matches Butcher's α). The boundary case `ζ = −1` corresponds to a
degree drop in `αPoly` (i.e. `αₖ = 0`, equivalently
`αPoly.natDegree < k`). -/
theorem aPoly_isRoot_iff_alphaPoly_isRoot
    (M : LinearMultistepMethod k) (ζ : ℂ) (hζ : ζ ≠ -1) :
    (M.aPoly.aeval ζ = 0) ↔
      (M.αPoly.aeval ((1 - ζ) / (1 + ζ)) = 0) := by
  sorry
```

The proof routes through Step 2's identity evaluated at `z = ζ`:
`aPoly.aeval ζ = (1 + ζ)^k * αPoly.aeval (ψ ζ)`. Since `ζ ≠ −1`,
`(1 + ζ)^k ≠ 0`, so the equivalence is direct.

The `ζ = −1` case can be handled as an optional side-lemma:

```lean
theorem aPoly_isRoot_neg_one_iff (M : LinearMultistepMethod k) :
    M.aPoly.aeval (-1 : ℂ) = 0 ↔ … := by
  -- Substitute ζ = -1: aPoly(-1) = 0^k - Σᵢ αᵢ · 0^(k-i) · 2^i
  --                              = - αₖ · 2^k    (only i=k survives)
  -- So aPoly.aeval (-1) = 0 ↔ αₖ = 0 ↔ αPoly.degree < k.
  sorry
```

This is optional for cycle 181; ship if time permits.

#### Step 4 — BDF2 sanity witness (mandatory)

Per the Phase B cycles 175–179 discipline: every new generic theorem
in §441 should have a numerical companion on `bdf2LMM`. Ship at
least one of:

```lean
-- Direct corollary form:
theorem bdf2LMM_aPoly_eq_mobiusTransform :
    bdf2LMM.aPoly = mobiusTransform bdf2LMM.αPoly := by
  exact aPoly_eq_mobiusTransform_αPoly bdf2LMM

-- More valuable: composes cycle 180 closed form with the new bridge.
theorem bdf2LMM_mobiusTransform_αPoly_eq :
    mobiusTransform bdf2LMM.αPoly =
      Polynomial.C (4/3) * Polynomial.X
      + Polynomial.C (8/3) * Polynomial.X ^ 2 := by
  rw [← aPoly_eq_mobiusTransform_αPoly bdf2LMM, bdf2LMM_aPoly_eq]
```

The second is the better witness — it validates the bridge
numerically by composing with the cycle 180 closed form.

### Concrete tactic suggestions

**For Step 1's definition**: just write it. `Finset.range (p.natDegree
+ 1)` is the standard pattern; `Polynomial.C` for constant lifting;
`^` elaboration on polynomials is automatic.

**For Step 2's algebraic identity**: the cleanest path is the
**cycle 180 `Polynomial.funext + ring` recipe** (line ~947 of
`Section441.lean` is the template). Outline:

1. `unfold LinearMultistepMethod.aPoly mobiusTransform`
2. `apply Polynomial.funext; intro x` lifts the polynomial equality
   to a pointwise real equality.
3. `simp only [Polynomial.eval_add, Polynomial.eval_sub,
   Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
   Polynomial.eval_X, Polynomial.eval_one, ...]` expands the
   `Polynomial.eval` calls.
4. `Finset.sum_congr rfl` if the index ranges differ, then `ring`
   closes the per-term real arithmetic.

If the LHS sum is over `Fin k` and the RHS over
`Finset.range (k+1)`, you may need `Finset.sum_fin_eq_sum_range`
or a manual reindex via `Finset.sum_bij`.

**For Step 3's complex-side bridge**: use
`Polynomial.aeval_eq_zero_iff` if it exists, or rewrite via
`Polynomial.IsRoot` and `Polynomial.eval_map`. Key step: rewrite
the Step 2 identity at `ζ : ℂ` (after applying
`Polynomial.map_ofReal` to lift to `ℂ[X]`), then divide both sides
by `(1 + ζ)^k` (which is non-zero by `hζ`).

**For Step 4's BDF2 witness**: the `Polynomial.funext` template
from cycle 180 (line ~947) shows exactly how to handle BDF2's
`α (Fin.succ i)` matches: pre-evaluate via
`have h : bdf2LMM.α (Fin.succ 0) = 4/3 := rfl` then `rw [h]`. Reuse
this pattern.

### Mathlib hooks to verify FIRST

Before writing any proof, use Lean LSP search to verify these hooks:

```
lean_local_search "Polynomial.funext"
lean_local_search "Polynomial.coeff_one_add_X_pow"
lean_local_search "Polynomial.coeff_C_mul"
lean_local_search "Polynomial.coeff_eq_zero_of_natDegree_lt"
lean_loogle "Polynomial.IsRoot _ _ ↔ _"
lean_loogle "Polynomial.aeval _ _ = 0 ↔ _"
```

If `lean_local_search` errors with a ripgrep PATH issue (per cycle
180 discovery), fall back to `lean_loogle` or `Grep` over
`.lake/packages/mathlib/`.

If `Polynomial.aeval_eq_zero_iff` is missing, use
`Polynomial.IsRoot.aeval_iff`, or rewrite via
`Polynomial.eval₂_eq_zero` directly.

---

## Priority 2 — Cycle 174 typo acknowledgement (5 minutes, optional)

The cycle 174 consultant noted that Butcher §441 p. 376 contains a
typo: the textbook claims `ρ'(1) = a₁`, but the correct identity is
`a₁ = 2·ρ'(1)`. Cycle 174's
`aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent` (line 455)
is the correct version. Add a one-paragraph comment to its docstring:

```
/-- … existing docstring …

Note: Butcher §441 p. 376 states `ρ'(1) = a₁` — this is a textbook
typo. The correct identity is `a₁ = 2·ρ'(1)`. The factor of 2 arises
from the product rule on `(1+z)^{k−i} (1−z)^i`, whose derivative at
`z = 0` is `(k − 2i)` (versus `ρ`'s weight `(k − i)`). Independently
verified by re-derivation in cycle 174 and by numerical witnesses on
explicit Euler (a₁ = 2, ρ'(1) = 1) and BDF2 (a₁ = 4/3, ρ'(1) = 2/3). -/
```

This is documentation hygiene, not substantive work. Bundle into
the cycle 181 commit if Priority 1 finishes early.

---

## What NOT to do

* **Do NOT** revisit any cycle 174–180 Phase B work. Phase B is
  closed; the factor-of-2 is a confirmed Butcher typo (verified by
  cycle 174 consultant + cycle 180 worker, with numerical witnesses
  on two methods). Treating the prompt's "What I'm stuck on" framing
  as a real blocker would waste the cycle.

* **Do NOT** treat the prompt's "What I'm stuck on" / "Recent cycle
  history" sections at face value. The supervisor's prompt-builder
  has been propagating phantom "commit-not-reaching-repo" verdicts
  for five consecutive cycles (176–180). Always run Priority 0
  verification first.

* **Do NOT** attempt any Phase C step beyond C.1 in cycle 181.
  Phase C.2 (stability ⇒ left-half-plane), C.3 (real factorisation,
  HIGH RISK), and C.4 (closure) are scheduled for cycles 182+. The
  Phase C scoping issue file is explicit: 4 phases, 4–6 cycles,
  with C.3 being the high-risk phase.

* **Do NOT** use `Polynomial.ext` + per-coefficient
  `simp + norm_num` for the algebraic identity in Step 2. This is
  the cycle 172/173 stall pattern. Use `Polynomial.funext + ring`
  per cycle 180's successful recipe at line ~947.

* **Do NOT** raise `maxHeartbeats` above 200000.

* **Do NOT** introduce `axiom`/`constant` for any Phase C step.
  Phase C.1's Möbius bridge is standard polynomial algebra; Mathlib
  has the hooks.

* **Do NOT** edit `scripts/autonomous_loop.py` from the worker. The
  prompt-builder bug is loop-maintainer territory; flag via the
  existing `phantom_commit_verdict_pattern.md` issue, do not patch
  the script directly.

* **Do NOT** poll Aristotle more than once if you submit a job.
  CLAUDE.md is explicit: one check after 30 minutes.

* **Do NOT** redefine or refactor `aPoly`, `αPoly`, `ρPoly`, or any
  cycle 174–179 helper. Phase C.1 builds NEW machinery on top of
  the existing chain; it does not modify it.

* **Do NOT** pivot to a fresh entity (e.g. `def:451A`, `def:422B`,
  `def:442A`, `thm:535A`, `thm:541A`) instead of Phase C.1. The
  ten-cycle §441 investment is compounding; abandoning it now leaves
  five `ρPoly` / `aPoly` lemmas without their ultimate consumer.
  Phase C.1 is bounded (1–2 cycles, medium risk) and the natural
  next step.

---

## Aristotle policy

If Phase C.1 Step 2 (the algebraic bridge) stalls after 30 minutes
of manual effort, submit it as a single Aristotle job with the
cycle 180 `bdf2LMM_aPoly_eq` proof as an in-context template (it
demonstrates the `Polynomial.funext` recipe). Do NOT submit Step 1
(the definition) or Step 4 (BDF2 sanity) — both should close
manually in <30 minutes.

Sleep 30 minutes (or proceed with Step 4 manually while waiting),
then check ONCE. If Aristotle stalls past 30%, fall back to manual.

Do NOT submit Step 3 (complex-side bridge) to Aristotle until Step
2 is closed — Step 3 depends on Step 2's identity, and a standalone
attempt would have to re-discover Step 2 from scratch.

---

## Pre-commit checklist

Before committing, run:

```bash
lake env lean OpenMath/Chapter4/Section441.lean   # must exit 0
grep -c sorry OpenMath/Chapter4/Section441.lean   # must be 0
```

`#print axioms` on each new theorem must return only
`[propext, Classical.choice, Quot.sound]`.

Update `.prover-state/issues/lem_441A_phase_C_scoping.md`
§"Phase C.1" with a "Cycle 181 update" subsection recording what
shipped.

Do NOT update `extraction/formalization_data/lean_status.json`'s
`lem:441A` entry — this cycle does not close `lem:441A`. Bump only
the `cycle` field to 181 if the row is touched at all.

Do NOT update `plan.md`'s `lem:441A` row — its `[~]` status is
unchanged.

---

## Faithfulness check reminders

For each new `def` and `theorem`:

* **`mobiusTransform`**: Cite Butcher §441 p. 376 (the
  `(1+z)^k − Σᵢ αᵢ (1+z)^{k−i} (1−z)^i` formula). The Lean
  definition is the explicit homogenization of `α(w)` at
  `(w, 1) = (1−z, 1+z)` — this is the standard Möbius
  homogenization trick to avoid division in `ℝ[X]`. The choice to
  homogenize at `p.natDegree` rather than at `k` is a Lean
  convenience (the function is defined uniformly over all
  polynomials, not just degree-`k` ones).

* **`aPoly_eq_mobiusTransform_αPoly`** (or `_ρPoly`): Identity to
  Butcher's textbook substitution `α(ψ(z))·(1+z)^k = a(z)`. Captures
  the same content; no hypothesis weakening or strengthening.

* **`aPoly_isRoot_iff_alphaPoly_isRoot`**: Captures the textbook's
  "ζ root of a iff ψ(ζ) root of α" with the explicit `ζ ≠ −1` side
  condition (the boundary case Butcher mentions but does not
  formalize separately).

* **BDF2 sanity witness**: Numerical instance, no faithfulness
  question.

Tautology / identity / smuggling / strength checks: pass for all
expected deliverables (the bridge is a substantive algebraic
identity, not a re-export; no `Prop`-field encoding of conclusions).

---

## Deliverable bar (cycle-end self-evaluation)

* **Minimum acceptable** (Priority 1 partial): `mobiusTransform`
  definition + the algebraic bridge identity, axiom-clean. Sorry
  count 0 → 0.
* **Target** (Priority 1 full): + the complex-side root bridge
  + at least one BDF2 sanity witness.
* **Stretch** (Priority 1 + Priority 2): + the cycle 174 typo
  docstring acknowledgement.

A cycle that ships ONLY the definition (no algebraic bridge) does
NOT meet the bar — file an issue documenting the blocker if Step 2
stalls and you cannot close it manually or via Aristotle.

A cycle that ships nothing on Phase C.1 because the worker re-ran
Phase B verification or audited the cycle 174 bridge would be a
phantom-driven failure — Priority 0's role is to refute that
framing in 5 minutes, not to consume the cycle.

---

## Cross-references

* `.prover-state/issues/lem_441A_phase_C_scoping.md` — the parent
  Phase C plan (cycle 180). **Read §1 (textbook argument) and §3
  (Phase C.1 deliverable list) before starting.**
* `.prover-state/issues/lem_441A_alpha_prime_negative.md` — the
  parent `lem:441A` issue tracking the full closure.
* `.prover-state/issues/consultant_advice_cycle_174.md` — the
  factor-of-2 typo diagnosis and the original Phase B/C phasing
  recommendation.
* `.prover-state/issues/consultant_advice_cycle_180.md` — the cycle
  180 consultant's directive to pivot to Phase C.1.
* `.prover-state/issues/phantom_commit_verdict_pattern.md` — the
  cycle 180 escalation of the supervisor prompt-builder bug.
* `OpenMath/Chapter4/Section441.lean:455` — cycle 174's
  `aPoly_coeff_one_eq_two_rho_deriv_at_one_of_preconsistent`
  (Priority 2 docstring target).
* `OpenMath/Chapter4/Section441.lean:913` — cycle 179's Phase B
  headline `aPoly_coeff_one_pos_of_stable_preconsistent`.
* `OpenMath/Chapter4/Section441.lean:947` — cycle 180's
  `bdf2LMM_aPoly_eq` (the `Polynomial.funext + ring` recipe
  template).
* `OpenMath/Chapter4/Section410.lean` — the source of `αPoly` /
  `βPoly`. **Inspect to determine the right bridge target before
  writing Step 2.**
* `extraction/raw_text/ch04.txt:1947–2030` — Butcher §441 verbatim,
  including the lem:441B paragraph (separate Phase, do NOT pursue
  this cycle).
