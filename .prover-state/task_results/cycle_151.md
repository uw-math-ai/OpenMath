# Cycle 151 Results

## Worked on

* def:530B Path A Step 1: introduce the `IsExplicit` predicate on
  `GeneralizedRungeKuttaMethod` together with positive (vacuous and
  non-vacuous) and negative non-vacuity witnesses.
* Aristotle housekeeping: cancel the cycle-148 general-`n` thm:550A
  project `2c4630b2-2998-4d4a-af88-c2f83fbd9eda`.
* Issue-file updates: append cycle-151 status to
  `def_530B_scaffold_strategy.md` and `thm_550A_general_n.md`.

## Approach

### Priority 0 — Aristotle cancellation (per strategy)

Called `mcp__aristotle__cancel_project` on
`2c4630b2-2998-4d4a-af88-c2f83fbd9eda`. Did NOT re-poll first (cycle
150's poll already exhausted the CLAUDE.md "one check" rule). The
project was at 21 % when cancelled, ~89 h after submission — clear
evidence of intractability matching the cycle-141 pattern (analogous
prior project cancelled at 6 % after 24 h).

### Priority 1 — `IsExplicit` predicate + non-vacuity witnesses

Read `OpenMath/Chapter5/Section530.lean` first to verify the actual
field names and existing witnesses (the strategy's preflight read
revealed two facts that diverged from its template):

* The structure uses `ℝ`, not `ℂ` as the strategy's code template
  spelled.
* `nontrivialTwoStageGRK.A = !![0, 0; 0, 0]` — vacuously
  strict-lower-triangular, so it would have been a vacuous positive
  witness only. Rather than reuse it, I constructed a
  fresh `explicit2StageGRK` with `A := !![0, 0; 1, 0]` (Heun-style)
  to give a *genuine non-vacuous* positive witness with a non-zero
  strict-lower entry.
* No structure axioms on `b, b₀`, so the negative witness can use
  arbitrary scalars.

Added at the end of the namespace (file lines 259→370 after the
edit, immediately before `end OpenMath.Chapter5.Section530`):

* `def GeneralizedRungeKuttaMethod.IsExplicit` — strict-lower-
  triangular predicate `∀ i j, i.val ≤ j.val → A i j = 0`.
* `theorem trivialGeneralizedRK_isExplicit` — vacuous (s = 1)
  positive witness; closed by `intro i j _; fin_cases i; fin_cases j; rfl`.
* `noncomputable def explicit2StageGRK` (Heun-style) +
  `theorem explicit2StageGRK_isExplicit` — non-vacuous positive
  witness; closed by `intro i j hij; fin_cases i <;> fin_cases j <;>
  simp_all [explicit2StageGRK]`.
* `noncomputable def implicit2StageGRK` (`A 0 0 = 1/2`) +
  `theorem implicit2StageGRK_not_isExplicit` — negative witness;
  closed by `intro h; have h00 := h ⟨0, _⟩ ⟨0, _⟩ (le_refl _);
  simp [implicit2StageGRK] at h00`.

The two new `def`s required `noncomputable` because `1/2 : ℝ` invokes
`Real.instDivInvMonoid` which has no executable code — the compiler
caught this on the first `lake env lean` pass, addressed in a
follow-up edit.

### Verification

* `lake env lean OpenMath/Chapter5/Section530.lean` — clean compile
  (no errors, no warnings).
* `lake build OpenMath.Chapter5.Section530` — clean build (1178
  jobs, 2.2 s incremental).
* `lean_verify` (axiom check) on each of the three new theorems
  returned `[propext, Classical.choice, Quot.sound]` only — no
  `sorryAx`, no extra axioms.

## Result

**SUCCESS.** Path A Step 1 landed axiom-clean with the full witness
portfolio (one vacuous positive, one non-vacuous positive, one
negative). Sorry count stays at 0. The Aristotle housekeeping is
done. Both issue files are up to date.

## Faithfulness check

Per the CLAUDE.md pre-commit checklist:

### `def GeneralizedRungeKuttaMethod.IsExplicit`

* Entity ID: not a textbook entity. Internal helper for def:530B
  Path A. The docstring states this explicitly: "This predicate is
  a Lean-internal helper, not a textbook entity: Butcher §530 uses
  the explicit/implicit distinction implicitly when discussing
  methods like classical RK4, but does not name a separate
  predicate."
* Lean statement captures: a strict-lower-triangular predicate on
  the coefficient matrix `A`, encoding the standard textbook
  meaning of "explicit Runge-Kutta method" (no implicit stage
  equations; stages can be evaluated by direct recursion on the
  stage index).
* Definition smuggling check: this is *not* claimed to formalize
  any named textbook concept; it is a helper. So smuggling is N/A.

### `theorem trivialGeneralizedRK_isExplicit`

* Tautology check: conclusion is `trivialGeneralizedRK.IsExplicit`
  i.e. `∀ i j : Fin 1, i.val ≤ j.val → trivialGeneralizedRK.A i j = 0`.
  Hypotheses: none. Conclusion does not appear as a hypothesis.
* Identity check: proof is `intro i j _; fin_cases i; fin_cases j;
  rfl`, not `exact h`. Real work: the `rfl` reduces
  `trivialGeneralizedRK.A 0 0` to its definitional value `0`, which
  is the only matrix entry at `s = 1`.
* Hypothesis strength check: no hypotheses; nothing to weaken.

### `noncomputable def explicit2StageGRK`

* Internal helper, not a textbook entity. Its `b₀ = 0, b = ![1/2, 1/2]`
  is a Heun-style choice; the strict-lower-triangular `A` is the
  point. (The output weights are bookkeeping; only `A` matters for
  `IsExplicit`.)

### `theorem explicit2StageGRK_isExplicit`

* Tautology check: conclusion `explicit2StageGRK.IsExplicit` does
  not appear as a hypothesis (proof has no hypotheses beyond `i, j,
  hij` introduced by `intro`).
* Identity check: proof is a `fin_cases × fin_cases` exhaustion
  closing each of the four `(i, j)` cases. Real work: each of the
  three `i ≤ j` cases reduces the `A` entry to `0` via the
  definitional unfolding of `!![0, 0; 1, 0]`.
* Hypothesis strength check: hypothesis `hij : i.val ≤ j.val` is
  exactly what `IsExplicit` provides; not strengthened.

### `noncomputable def implicit2StageGRK`

* Internal helper, not a textbook entity. The `A 0 0 = 1/2` is the
  load-bearing non-zero diagonal entry.

### `theorem implicit2StageGRK_not_isExplicit`

* Tautology check: conclusion `¬ implicit2StageGRK.IsExplicit` does
  not appear as a hypothesis.
* Identity check: proof is `intro h; have h00 := h ⟨0, _⟩ ⟨0, _⟩
  (le_refl _); simp [implicit2StageGRK] at h00`. Real work: extracts
  the `(0, 0)` instance of `IsExplicit`, which would say `A 0 0 = 0`
  but actually evaluates to `1/2 ≠ 0`, contradicting `h00`. The final
  `simp` reduces to `False` and closes the goal.
* Hypothesis strength check: only one hypothesis is `h :
  implicit2StageGRK.IsExplicit` (the assumed-for-contradiction
  predicate); not strengthened.

All three new theorems verified axiom-clean
(`[propext, Classical.choice, Quot.sound]`) by `lean_verify`.

## Dead ends

None. The strategy's plan held up under the actual file contents
once the field types (`ℝ` not `ℂ`) and the `noncomputable` requirement
were addressed.

## Discovery

* `Real.instDivInvMonoid` has no executable code, so any
  `def : GeneralizedRungeKuttaMethod _` whose `b` or `A` involves
  `1/2 : ℝ` (or any non-trivial rational) needs the `noncomputable`
  marker. The existing `trivialGeneralizedRK`, `zeroGeneralizedRK`,
  and `nontrivialTwoStageGRK` avoid this because their entries are
  all `0`, `1`, or `2` — integer literals that `Real` provides
  computably. Future witnesses with non-integer entries should be
  marked `noncomputable` from the start.
* The strategy's negative-witness template `simp [implicit2StageGRK]
  at h00` actually closes the contradiction in one step (no
  `norm_num` follow-up needed) — `simp` recognises `(1/2 : ℝ) = 0`
  is `False` directly via the `instDivInvMonoid` arithmetic.
* `nontrivialTwoStageGRK.A = !![0, 0; 0, 0]` is *vacuously*
  strict-lower-triangular. We could have added a fourth witness
  `nontrivialTwoStageGRK_isExplicit` for completeness, but the
  Heun-style `explicit2StageGRK` is the more informative
  non-vacuous witness.

## Suggested next approach

**Cycle 152 — Path A Step 2** (per the cycle 151 strategy preview
and the updated `def_530B_scaffold_strategy.md`):

Define `applyStartingThenStep_explicit` and
`applyExactThenStarting_explicit` taking the
`∀ i, IsExplicit (S.method i)` hypothesis. Body via direct recursion
on stage index — each stage `j`'s `Y_j` is a `Finset.sum` over
already-computed `Y_0, …, Y_{j-1}`. The strict-lower-triangular `A`
guarantees `A i j = 0` for `j ≥ i`, so the sum is well-defined
without the implicit fixed-point machinery. Estimated ~80-120 LOC.

The natural Lean encoding is a `Nat`-indexed recursive helper, e.g.

```lean
noncomputable def stageValueExplicit
    {s : ℕ} (M : GeneralizedRungeKuttaMethod s) (hM : M.IsExplicit)
    (f : ℝ → ℝ) (y₀ h : ℝ) : Fin s → ℝ
  | ⟨0, _⟩ => y₀
  | ⟨j + 1, hj⟩ => y₀ + h * Finset.sum (Finset.range (j + 1))
                       (fun k => M.A ⟨j+1, hj⟩ ⟨k, by omega⟩
                                 * f (stageValueExplicit M hM f y₀ h ⟨k, by omega⟩))
```

(Decreasing-on-the-stage-index recursion, terminated by Lean's
well-founded check.) This is a single primitive; `applyStartingThenStep_explicit`
and `applyExactThenStarting_explicit` then assemble it.

**Sequencing risk**: the `noncomputable` marker propagates here too
(any `Real`-valued recursive `def` involving `*` on real reals is
fine, but division would force it). Plan to mark all four new defs
`noncomputable` from the start to avoid the cycle-151 retry pattern.

**Cycle 153 — Path A Step 3**: define `HasOrderRelativeTo_explicit`
and prove the trivial-IVP non-vacuity witness for explicit Euler ×
`trivialStartingMethod` with order `p = 0`. Estimated ~50-80 LOC.

**Avoid**: do NOT pivot to thm:550A general-`n` (deferred per
cycle-141/151 cancellations), cor:550C (depends on thm:550A), or
def:530C (depends on def:530B closure). Stay on Path A.
