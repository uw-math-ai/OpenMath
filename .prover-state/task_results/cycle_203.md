# Cycle 203 Results

## Worked on

Priority 1 from cycle 203 strategy: ship
`RKTableau.equivalent_self : M.Equivalent M` in
`OpenMath/Chapter3/Section381.lean`, closing the cycle 030 deferral
`equivalent_self_general_deferred.md` via the cycle 201/202 Banach
contraction foundation.

Priority 0 (SKIP §441 Phase C.2 smoke test) honoured. Priority 2
(thm:381H direction 2) not attempted — P1 was the budget.

## Approach

Followed the strategy's 8-step recipe verbatim:

1. `intro N _ _ f L hL y₀` (unfold `Equivalent` quantifiers).
2. `set C := ∑ i j, |M.A i j|`; derive `0 ≤ C`, `0 ≤ L*C`,
   `0 < 2*(L*C+1)`.
3. `refine ⟨1/(2*(L*C+1)), by positivity, ?_⟩` to commit to the
   threshold, with `positivity` discharging `0 < h₀` against the
   ambient nonnegativity facts.
4. Smallness `|h| · L · C < 1`: derived `h * (2*(L*C+1)) ≤ 1` from
   `hh_le` via `le_div_iff₀` (mp direction), then closed
   `nlinarith [hh_pos, h_LCnn, h_mul]`.
5. Invoke `RKStageMap_contracting h hL y₀ h_small` to get a
   `ContractingWith` packaging.
6. Build `Function.IsFixedPt (M.RKStageMap h f y₀) Y` (and same for
   `Y'`) via `show … = Y; funext i; exact (hY_stage i).symm` — the
   `RKStageMap` body β-reduces to the stage equation by defeq, so no
   `simp only [RKStageMap]` was needed.
7. `hContract.eq_or_edist_eq_top_of_fixedPoints` produced the
   disjunction; the `edist = ⊤` branch was discharged by
   `edist_ne_top Y Y'` (`Fin s → N` inherits `PseudoMetricSpace` from
   the normed-space pi instance).
8. `rw [hY_out, hY'_out, hY_eq]` closed the goal `y₁ = y₁'` by `rfl`
   (auto-applied by `rw`).

The whole proof is 33 lines including the docstring (≈18 lines of
tactic body), well under the strategy's 80–120 LOC budget.

## Result

**SUCCESS.**

* `lake env lean OpenMath/Chapter3/Section381.lean` — warm rebuild
  **6.9s**, no errors, only the pre-existing unused-variable warnings
  at lines 577 and 1830.
* `lean_verify RKTableau.equivalent_self` — axioms
  `[propext, Classical.choice, Quot.sound]` only (axiom-clean).
* `grep -c sorry OpenMath/Chapter3/Section381.lean` → 0.
* Repo-wide sorry search finds only docstring/comment occurrences —
  no actual `sorry` tactic.
* `equivalent_explicitEuler_self` (cycle 030 witness) unmodified and
  still compiles, as required by the strategy.

Issue file `equivalent_self_general_deferred.md` updated with a
`## Resolution (cycle 203)` block citing the new theorem.

## Faithfulness check

For the new theorem introduced this cycle:

* **Entity ID**: def:381A (the `Equivalent` predicate). The
  `equivalent_self` lemma itself is not a named textbook theorem —
  it is a reflexivity / non-vacuity witness for def:381A, exercising
  the predicate at arbitrary `M` (vs. cycle 030's explicit-Euler
  specialisation). Quoted statement of def:381A from
  `extraction/formalization_data/entities/def_381A.json`:

  > Two Runge–Kutta methods are 'equivalent' if, for any initial
  > value problem defined by an autonomous function f satisfying a
  > Lipschitz condition, and an initial value y0, there exists
  > h0 > 0 such that the result computed by the first method is
  > identical with the result computed by the second method, if
  > h ≤ h0.

* **Lean statement captures**: same content as applied to the
  reflexive case `M.Equivalent M`. The predicate's universal
  quantifier over `(N, f, L, hL, y₀)` and its existential ∃h₀ are
  consumed exactly as written in def:381A; the threshold
  `1 / (2 * (L * C + 1))` is an explicit constructive witness and
  does not weaken the predicate (which only asserts ∃ a positive
  threshold). The proof closes the universally-quantified
  `∀ y₁ y₁', M.IsRKOneStep f y₀ h y₁ → M.IsRKOneStep f y₀ h y₁' →
  y₁ = y₁'` body, which is precisely the "result is identical"
  conclusion from the textbook applied to a single method twice.

* **Hypothesis-strength check**: no extra hypotheses beyond what the
  `Equivalent` predicate itself takes. Lipschitz `L` is consumed
  (not strengthened); no smoothness, autonomy, or boundedness extras
  added. The reflexive case is genuinely just `M.Equivalent M` with
  no side conditions.

* **Definition-smuggling check**: not applicable — no new
  `def`/`class`/`structure`, only a theorem.

* **Tautology check**: conclusion `M.Equivalent M` does not appear
  among the hypotheses (there are no hypotheses on `M` at all
  beyond `s : ℕ`, `M : RKTableau s`).

* **Identity check**: the proof is a multi-step tactic block, not
  `exact h`; does real work via Banach contraction.

* **Absent-theorem check**: docstring promises closure of the cycle
  030 deferral, and the issue file `equivalent_self_general_deferred.md`
  has been updated to reflect this — no orphan promise.

## Dead ends

None this cycle. The strategy's recipe was deployment-ready as
written; minor refinements:

* The strategy's step 4 fallback (`by_cases L*C = 0`) was not needed
  — direct `nlinarith` closed the smallness inequality with the
  three hints `[hh_pos, h_LCnn, h_mul]`. The `h * (2*(L*C+1)) ≤ 1`
  intermediate was extracted from `hh_le` via `le_div_iff₀`
  (not `div_le_iff₀` — the strategy noted to check the direction;
  `le_div_iff₀` is correct).
* The strategy's step 6 used `simp only [RKTableau.RKStageMap]`
  to unfold the definition before the `(hY_stage i).symm` exact.
  This is unnecessary: `M.RKStageMap h f y₀ Y i` β-reduces to
  `y₀ + h • ∑ j, M.A i j • f (Y j)` by definitional equality, so
  `exact (hY_stage i).symm` works directly after `funext i`. The
  `show ... = Y` line was kept to force unfolding of
  `Function.IsFixedPt`, but the `simp` line was dropped.
* Step 7's `edist_ne_top` fired on the first try with no fallback
  needed — `Fin s → N` for `N` a normed `ℝ`-space is automatically
  a `MetricSpace` (hence `PseudoMetricSpace`) via the Pi instance.

## Discovery

1. **Definitional unfolding of `RKStageMap` is "free"** for the
   fixed-point reduction. The body `fun Y i => y₀ + h • ∑ j, M.A i j
   • f (Y j)` β-reduces under application, so the stage equation
   `Y i = y₀ + h • Σⱼ M.A i j • f (Y j)` is directly a per-component
   fixed-point equation `M.RKStageMap h f y₀ Y i = Y i` with no
   `simp` / `unfold` step needed. Useful pattern for any future
   uniqueness / existence consumer of `RKStageMap`.

2. **The `1 / (2 * (L * C + 1))` threshold is uniform across `s`**
   — no per-stage-count adjustment needed. The same `h₀` works for
   `s = 1` (explicit Euler) up to arbitrary implicit methods, because
   the entrywise bound `C = Σᵢⱼ |aᵢⱼ|` absorbs all stage-count
   dependence. The cycle 030 explicit-Euler proof used `h₀ = 1`,
   which is strictly looser than the new threshold but suffices for
   `paddedEuler`'s zero matrix; both witnesses now coexist.

3. **`le_div_iff₀` vs `div_le_iff₀`**: the strategy correctly noted
   the direction matters. `le_div_iff₀ (0 < c) : a ≤ b / c ↔ a * c ≤
   b` is what's needed for the `h ≤ 1/D ⇒ h*D ≤ 1` rearrangement.

## Suggested next approach

Cycle 204 candidates, ordered by tractability:

1. **`paddedEuler.equivalent_self` specialisation** (≈5 LOC):
   immediate corollary, `paddedEuler.Equivalent paddedEuler := by
   exact paddedEuler.equivalent_self`. Useful as a §380 non-vacuity
   witness; one-line proof.

2. **One direction of `thm:381H` (PEquivalent → Equivalent)**
   — direction 2 of 4 in `thm_381H_deferred.md`. The strategy
   flagged this as Priority 2 for cycle 203 but explicitly warned
   against starting unless P1 closed with >1 hour budget. Now P1
   has landed, so cycle 204 has a clean runway. The conceptual
   gap is the "Banach iteration starting from a constant tuple
   preserves partition-block equality" iteration-invariant lemma
   — likely 1.5 cycles of work as the strategy noted, so plan
   accordingly.

3. **Replace the loose `Σᵢⱼ |aᵢⱼ|` entrywise bound with the
   tighter sup-norm row form `max_i Σⱼ |aᵢⱼ|`** in
   `RKStageMap_lipschitz`. The cycle 202 task results noted this as
   future work; the new `equivalent_self` would then admit a larger
   `h₀` threshold. Optional / cosmetic.

4. **`RKStageMap.fixedPoint_unique` named corollary**: a Banach
   uniqueness lemma at the `RKStageMap` level abstracted away from
   `Equivalent`/`IsRKOneStep`. Useful infrastructure for the §381H
   direction 2 work. ~15 LOC. Could be paired with (1) as a small
   cycle.

5. **§441 Phase C.2 GPFS smoke test**: still blocked, 23rd
   consecutive timeout would be at risk; recommend continuing the
   skip until the loop-maintainer surfaces a recovery signal.
