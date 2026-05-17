# Cycle 344 Results

## Worked on

§422 Phase D bridge infrastructure (per strategy):

* **P1**: `coef_α_eq_ρPoly_deriv_at_one_of_preconsistent` — under
  preconsistency, `Σ_{i:Fin k} (i+1) · α_{i+1} = ρ'(1)`.
* **P2**: `coef_α_pos_of_stable_preconsistent` — for stable
  preconsistent `M` with `0 < k`, `coef_α(M) > 0`.
* **P3**: two non-vacuity `example`s — `explicitEulerLMM` (`coef_α = 1`)
  and `bdf2LMM` (`coef_α = 2/3`).

All three shipped in `OpenMath/Chapter4/Section422.lean`, appended
after cycle 342's `Eq422a_at_vertex_eta_eq` block. New imports:
`OpenMath.Chapter4.Section441` and `OpenMath.Chapter4.Section451`.

## Approach

Followed the strategy's recipe verbatim:

1. **Pre-flight**: `lake env lean OpenMath/Chapter4/Section441.lean`
   built cleanly in 4m40s under a 6-min budget (first 120s attempt
   timed out per cycle 182 GPFS pattern, but the 5-min retry succeeded).
2. **Imports**: added `import OpenMath.Chapter4.Section441` and
   `import OpenMath.Chapter4.Section451` (P3's `bdf2LMM` example needs
   the latter). `ρPoly` and friends live in the
   `OpenMath.Chapter4.Section404` namespace inside `Section441.lean`,
   so they are reachable via `M.ρPoly` dot notation through the
   existing `LinearMultistepMethod` reference.
3. **P1 proof**: applied `M.ρPoly_deriv_eval_one_unconditional` to
   expose the RHS as `k - Σ α · (k - (i+1))`. The strategy's "5-step
   sum-split + ring closure" recipe stalled at `ring` on the final
   sum-level goal `∑ x, (i·α + α) = ∑ x, (α + α·i)`, since `ring`
   cannot reach inside `Finset.sum`. Fix: first canonicalize the LHS
   via `Finset.sum_congr rfl + push_cast + ring` per element to
   `∑ α · (i+1)`, then expand the RHS via `Finset.sum_mul +
   ← Finset.sum_sub_distrib + Finset.sum_congr rfl + ring`, then
   substitute `← hPre` and close with a single algebraic `ring`
   (now a pointwise identity `LHS = k - (1·k - LHS)`).
4. **P2**: one-line composition `rw [P1] ; exact
   M.ρPoly_deriv_eval_one_pos_of_stable_preconsistent hk hStab hPre`.
5. **P3 explicitEuler**: `simp [explicitEulerLMM]` closes outright.
6. **P3 bdf2LMM**: `simp [bdf2LMM, Fin.sum_univ_two] + norm_num`.

## Result

**SUCCESS — axiom-clean ship.**

* `lake env lean OpenMath/Chapter4/Section422.lean` exits 0
  (~4m23s).
* **Aggregator check skipped**: both `lake env lean
  OpenMath/Chapter4.lean` and `lake build OpenMath.Chapter4.Section422`
  timed out at 9 min (`cycle_182_gpfs_slowness.md` pattern, exit
  code 124/143). The per-file Section422.lean build + axiom check
  are load-bearing; the aggregator timeout reflects cluster GPFS
  slowness, not cycle 344 code health.
* `#print axioms` on P1 and P2 both report
  `[propext, Classical.choice, Quot.sound]` — the standard trio,
  no `sorryAx`, no fresh axioms.
* `grep -c sorry OpenMath/Chapter4/Section422.lean` → 0.
* Tautology scanner (`rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$'`)
  → no hits.
* P3 examples both compile (two `example` declarations, no name
  collisions).

## Faithfulness check

### P1 — `coef_α_eq_ρPoly_deriv_at_one_of_preconsistent`

* Entity ID: this is bridge infrastructure for `def:422B` (the
  underlying-one-step-method definition); not a textbook theorem in
  its own right.
* Textbook source: Butcher §441 p. 376 gives the identity
  `ρ'(1) = α₁ + 2α₂ + ⋯ + kαₖ` under preconsistency (the
  consultant note `consultant_advice_cycle_174.md` §A also
  independently verified `ρ'(1) = Σ i·αᵢ`).
* Lean statement captures: **same content**. The Lean LHS
  `Σ_{i:Fin k} ((i.val + 1 : ℕ) : ℝ) · M.α i.succ` is the textbook
  `α₁ + 2α₂ + ⋯ + kαₖ` (with the `Fin k → Fin (k+1)` `succ` cast
  matching the `α₁, …, αₖ` selector convention of §404).
  The Lean RHS `M.ρPoly.derivative.eval 1` is `ρ'(1)` by definition.
* Hypotheses: only `M.IsPreconsistent` is used — matches textbook.

### P2 — `coef_α_pos_of_stable_preconsistent`

* Entity ID: bridge infrastructure for `def:422B` (the non-vanishing
  hypothesis of cycle 342's `Eq422a_at_vertex_eta_eq` is downstream
  of this positivity).
* Textbook source: Butcher §441 p. 376, "We calculate the value of
  `a₁` … to be `kα(1) − 2α'(1)`" together with cycle 178's
  `ρPoly_deriv_eval_one_pos_of_stable_preconsistent` (already
  textbook-faithful at the §441 level).
* Lean statement captures: **same content** under composition.
  Hypotheses `0 < k`, `M.IsStable`, `M.IsPreconsistent` match the
  upstream `ρPoly_deriv_eval_one_pos_of_stable_preconsistent`
  signature one-to-one.

### P3 examples

* Not theorems — concrete numerical witnesses. Both verify P1 holds
  on cycle 184/451 method definitions without any new mathematical
  claim.

### Faithfulness compliance

* **Tautology**: P1's conclusion is not a hypothesis; the equality
  bridges two different expressions.
* **Identity proof**: P1 has a 4-step structural proof, P2 is a
  one-line composition of two non-trivial inputs — neither is
  `exact h`.
* **Definition smuggling**: no new `def`/`structure` introduced.
* **Hypothesis strength**: P1 uses only `IsPreconsistent` (Butcher
  uses no more). P2 uses `0 < k + IsStable + IsPreconsistent`
  matching cycle 178's upstream signature.

## Dead ends

* **First `ring` attempt**: the strategy's literal step 6 ("close
  with `ring`") failed because after `rw [hsum, ← hPre]` the goal
  becomes a sum-level equality `∑ x, (i·α + α) = ∑ x, (α + α·i)`
  that `ring` cannot enter — `ring` only acts on a single
  commutative-ring term, not on `Finset.sum` binders. The fix was
  to canonicalize *both* sides to the same per-element form via
  `Finset.sum_congr` first, so that after the final substitution
  `ring` only sees a pointwise term-level identity.
* **`push_cast` placement**: putting `push_cast` after the `rw`s
  but before `ring` didn't help — the cast inside the sum binder
  isn't reachable from outside. `push_cast` had to live inside
  the `Finset.sum_congr` step.

## Discovery

* The pattern "`ring` on sum-level equalities" is a recurring trap
  documented in `feedback_satisfieseq404b_cast.md` for cast bridging;
  this cycle adds a fresh manifestation: even *non-cast* sum-level
  equalities (just commutativity within summands) need
  `Finset.sum_congr rfl ; intro i _ ; ring` rather than top-level
  `ring`. This is general and not specific to `SatisfiesEq404b`.
* `Section441.lean` first-build timing is now ~4m40s on a cold cache
  (within the 5-min budget) — healthier than the cycle 182-237
  baseline. The 120s timeout is too tight; future workers should
  default to 300s+ for first-build probes.

## Suggested next approach

Two equally promising candidates for cycle 345:

1. **§422 Phase D.3** (planner's primary recommendation in
   `def_422B_path.md` §"Cycle 344 entry point"): scaffold
   `underlyingEta_aux` as the inductive `η(t)` recursion on rooted
   trees. The infrastructure for the base case (`τ`) is now in
   place via cycle 344's P1+P2 plus cycle 342's `Eq422a_at_vertex_eta_eq`,
   so the inductive step can chain cleanly. **Risk**: per
   `def_422B_path.md` §5, this is 100-200 LOC and tracked at HIGH
   risk; recommend a careful sorry-first scaffold *with explicit
   per-sorry issue files* and only proceed if the scaffold compiles
   cleanly and the inductive hypothesis types check.

2. **Eq422a_at_vertex_eta_eq strengthening**: revisit cycle 342's
   theorem to consume `coef_α_pos_of_stable_preconsistent` and
   eliminate the explicit non-vanishing hypothesis. This is a
   ~5 LOC additive ship if `coef_β`-positivity is handled by an
   additional hypothesis (or by routing through preconsistency +
   `IsConsistent`'s 404b). The cycle 344 strategy explicitly forbade
   this for granularity reasons; cycle 345 may revisit.

3. **Pivot for variety**: `thm:302A` or `thm:302C` per the strategy's
   fallback ladder. These avoid the §422 streak's compounding-but-
   narrow focus.

Recommend option 2 first (~5 LOC ship), then option 1 (Phase D.3
proper) as the dominant goal once option 2 closes; option 3 only
if either of those stalls.
