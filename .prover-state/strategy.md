# Cycle 345 Strategy — §422 Phase D consolidation: consume cycle 344's `coef_α > 0`

## §A — Recommended target: `Eq422a_at_vertex_eta_eq` consolidation

Cycle 344 just shipped the bridge `coef_α(M) = ρ'(1)` (P1) plus
`coef_α(M) > 0` for stable preconsistent `M` (P2). Cycle 342 left
the headline `Eq422a_at_vertex_eta_eq`
(`OpenMath/Chapter4/Section422.lean:662`) taking an explicit
non-vanishing hypothesis `coef_α + coef_β ≠ 0`. Cycle 345's job is
to **ship a `_of_stable_preconsistent` corollary** that discharges
the non-vanishing condition under textbook hypotheses, modulo an
explicit β-side hypothesis.

This is the cycle 344 worker's recommended option 2 ("~5 LOC additive
ship"). It is genuinely small (one corollary + one non-vacuity
witness), strictly additive, and visibly consumes both cycle 342 and
cycle 344's work, keeping the §422 Phase D chain self-consistent
before cycle 346 attempts Phase D.3 proper.

## §B — Deliverables (in order)

### P1 (LOAD-BEARING, ~30 LOC) — `Eq422a_at_vertex_eta_eq_of_stable_preconsistent`

Add immediately after cycle 344's `coef_α_pos_of_stable_preconsistent`
(line ~736 of `Section422.lean`):

```lean
/-- *Phase D consolidation (cycle 345):* under the textbook hypotheses
of stability + preconsistency plus the side hypothesis that the
β-side coefficient `Σ_{i:Fin (k+1)} i · M.β i` is non-negative,
`Eq422a` at the single-vertex tree determines `η(τ)` uniquely.

This routes the non-vanishing requirement of cycle 342's
`Eq422a_at_vertex_eta_eq` through cycle 344's `coef_α > 0`. The
β-side non-negativity hypothesis surfaces a residual textbook
assumption: Butcher §422 implicitly requires `coef_α + coef_β > 0`,
which under preconsistency reduces to `Σ (i+1) · β_i > 0` (the
β-polynomial derivative at 1). Closing this from
`M.IsStable + M.IsConsistent` alone requires §441 β-side machinery
not yet built; defer that to a Phase D′ refinement cycle. -/
theorem Eq422a_at_vertex_eta_eq_of_stable_preconsistent
    {k : ℕ} (M : OpenMath.Chapter4.Section404.LinearMultistepMethod k)
    (hk : 0 < k)
    (hStab : M.IsStable) (hPre : M.IsPreconsistent)
    (hβ_nn : 0 ≤ ∑ i : Fin (k + 1), ((i.val : ℕ) : ℝ) * M.β i)
    {η_q : Quotient PhiEquivalent.setoidSigma}
    (hEq : Eq422a M η_q) :
    elementaryWeightQ_phi η_q RootedTree.vertex
      = (∑ i : Fin (k + 1), M.β i)
          / ((∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ)
              + (∑ i : Fin (k + 1), ((i.val : ℕ) : ℝ) * M.β i)) := by
  apply Eq422a_at_vertex_eta_eq hEq
  have hα_pos := coef_α_pos_of_stable_preconsistent M hk hStab hPre
  linarith
```

**Tactic notes**:
* The `apply Eq422a_at_vertex_eta_eq hEq` step closes everything
  except the non-vanishing side-goal.
* The side-goal is `coef_α + coef_β ≠ 0`. We have `coef_α > 0`
  (cycle 344) and `0 ≤ coef_β` (hypothesis), so `coef_α + coef_β > 0
  ≠ 0` via `linarith`.
* No `field_simp`/`push_cast`/`ring` needed at this layer — they
  already fire inside cycle 342's underlying `Eq422a_at_vertex_eta_eq`.

### P2 (NON-VACUITY, ~10–20 LOC) — BDF2 witness

Append a non-vacuity example for BDF2. The cycle 344 P3 example
confirms `bdf2LMM.coef_α = 2/3`; we need a witness that makes the
full P1 fire.

**Shape (preferred) — bare `example`**:

```lean
example (η_q : Quotient PhiEquivalent.setoidSigma)
    (hEq : Eq422a bdf2LMM η_q) :
    elementaryWeightQ_phi η_q RootedTree.vertex = <literal> := by
  have := Eq422a_at_vertex_eta_eq_of_stable_preconsistent
    bdf2LMM (by norm_num)
    bdf2LMM_isStable bdf2LMM_isPreconsistent
    (by simp [bdf2LMM, Fin.sum_univ_three]; norm_num)
    hEq
  -- close arithmetic comparison with simp + norm_num (compute literal first)
```

**Compute the literal first** by reading `bdf2LMM` β-values from
`Section451.lean`. The expected workflow:
1. Locate `bdf2LMM`: `grep -n "def bdf2LMM" OpenMath/Chapter4/Section451.lean`.
2. Read off `β : Fin 3 → ℝ`. Standard BDF2 has `β = ![2/3, 0, 0]`
   (β₀ = 2/3, β₁ = β₂ = 0).
3. Compute `coef_β = 0·(2/3) + 1·0 + 2·0 = 0`, `sum_β = 2/3`,
   `coef_α + coef_β = 2/3 + 0 = 2/3`, `η(τ) = (2/3)/(2/3) = 1`.
4. The `hβ_nn` discharge: `simp [bdf2LMM, Fin.sum_univ_three]`
   evaluates the sum to `0`, which is `≥ 0`; close with `le_refl 0`
   or `norm_num`.

**If BDF2's β-values differ** from the canonical `(2/3, 0, 0)`,
adjust the literal expected value. The shape stays the same.

**Required bdf2LMM helpers**: `bdf2LMM_isStable` (cycle 169,
`OpenMath/Chapter4/Section454.lean`) and `bdf2LMM_isPreconsistent`
(verify presence via grep before P2; if absent, ship a one-line
inline witness `by simp [bdf2LMM, LinearMultistepMethod.IsPreconsistent,
Fin.sum_univ_two]` rather than blocking on a missing lemma).

### P3 (STRETCH, only if P1+P2 close in <60 min) — explicit Euler non-vacuity

The cycle 344 P3 already shows `explicitEulerLMM.coef_α = 1`. Add a
mirror non-vacuity to P2 for `explicitEulerLMM`, computing
`η(τ) = sum_β / (coef_α + coef_β)` at the explicit Euler β-values
`(0, 1)`. Expected: `coef_β = 0·0 + 1·1 = 1`, `sum_β = 1`,
`η(τ) = 1 / (1 + 1) = 1/2`.

Purely additive sanity; only include if cycle 345 has genuine time
remaining.

## §C — Pre-flight checks (do these FIRST, before writing P1)

1. **Build the dependency**: run `lake env lean
   OpenMath/Chapter4/Section441.lean` cold. Per cycle 344 this took
   ~4m40s. **Budget 8 minutes**; if it times out twice, defer to
   §F fallback.
2. **Confirm cycle 342 signature stable**: `grep -n
   "theorem Eq422a_at_vertex_eta_eq" OpenMath/Chapter4/Section422.lean`
   should show line ~662 with the signature shown in §B P1. If the
   signature has moved, adjust line references.
3. **Confirm cycle 344 P2 signature**: `grep -n
   "coef_α_pos_of_stable_preconsistent" OpenMath/Chapter4/Section422.lean`
   should show line ~736.
4. **Read `bdf2LMM`'s β-vector** before writing P2's expected
   literal: `grep -A 20 "def bdf2LMM" OpenMath/Chapter4/Section451.lean`.
5. **Confirm `bdf2LMM_isStable` exists**: `grep -rn
   "bdf2LMM_isStable" OpenMath/Chapter4/`. If absent, replace with
   inline proof or skip P2's BDF2 specialization in favor of P3's
   explicit Euler version.

If any pre-flight check fails: document in `task_results/cycle_345.md`
and fall back to §F.

## §D — What NOT to try

Per `attempts.md` and the issue files:

1. **DO NOT attempt Phase D.3** (`underlyingEta_aux` inductive
   step). The cycle 344 worker flagged it HIGH risk + 100–200 LOC.
   Per cycle 149/150 and cycle 200/201 rollback precedents, a
   sorry-first multi-cycle scaffold without a credible single-cycle
   close gets rolled back and costs −2. Reserve Phase D.3 for cycle
   346+ with explicit Aristotle batch + phased scoping.

2. **DO NOT try to prove `coef_α + coef_β > 0` from stability +
   consistency alone**. The textbook argument routes through §441
   β-side machinery (analogous to cycle 178's α-side
   `ρPoly_deriv_eval_one_pos_of_stable_preconsistent`) that does
   not yet exist in the project. Surfacing the β-nonneg hypothesis
   in P1 is the deliberate choice; eliminating it is a Phase D′
   refinement target for a later cycle.

3. **DO NOT use `ring` on sum-level equalities** (cycle 344's
   documented dead end). If a `ring` step fires after a rewrite
   that exposes a `∑ x, …` binder, switch to
   `Finset.sum_congr rfl ; intro i _ ; ring` first to normalize
   per-element, then close at the outer level. This shouldn't fire
   in P1 (no sum-level rewrites needed) but may fire in P2 when
   expanding `coef_β` literally on bdf2LMM.

4. **DO NOT touch `scripts/autonomous_loop.py`**. Per CLAUDE.md and
   `tautology_scanner_false_positives.md`, scanner/prompt-builder
   bugs are loop-maintainer territory.

5. **DO NOT introduce `axiom`/`constant`** or raise `maxHeartbeats`
   above 200000.

6. **DO NOT touch any files outside**
   `OpenMath/Chapter4/Section422.lean`, `lean_status.json`,
   `plan.md`, `.prover-state/issues/def_422B_path.md`, and
   `.prover-state/task_results/cycle_345.md` unless absolutely
   required by P2 (e.g., a missing `bdf2LMM_isStable` reference).

7. **DO NOT poll Aristotle more than once**. No live Aristotle
   submissions from cycle 344 to poll. Don't submit a new one in
   cycle 345 unless P1's `linarith` step genuinely stalls.

8. **DO NOT try aggregator builds** (`lake env lean
   OpenMath/Chapter4.lean` or `lake build OpenMath.Chapter4.Section422`).
   Per cycle 344 these reliably time out at 9 min on this cluster
   (`cycle_182_gpfs_slowness.md` pattern). The per-file Section422
   build + axiom-clean spot-check (`#print axioms` via stdin) are
   load-bearing.

9. **DO NOT attempt the Eq422a_at_vertex_eta_eq_of_isConsistent
   form** (i.e., using `M.IsConsistent` to substitute `coef_α =
   sum_β`). That substitution simplifies the numerator/denominator
   but doesn't eliminate the non-vanishing requirement — and per
   §D-2 above, proving `coef_α + coef_β > 0` from consistency alone
   is multi-cycle work.

## §E — Pitfall reminders

* **Type ascription on `((i.val : ℕ) : ℝ)`**: keep the double cast
  exact. Cycle 342's signature uses `((i.val : ℕ) : ℝ)` (Nat
  intermediate); deviating breaks unification. Copy the literal
  string from line 662.
* **`Fin.succ` vs `(i + 1 : Fin (k+1))`**: cycle 342 uses
  `M.α i.succ` for the α-sum (selecting α₁..αₖ from
  `α : Fin (k+1) → ℝ`). Match it exactly.
* **Discharging `0 < k` in P2 BDF2 example**: BDF2 has `k = 2`,
  closes via `by norm_num` or `by decide`.
* **Bind order for `Eq422a_at_vertex_eta_eq` application**: the
  cycle 342 theorem takes `hEq` then `h_ne` as explicit args.
  `apply ... hEq` leaves `h_ne` as the residual side-goal.

## §F — Fallback if P1 stalls

If the Section441 pre-flight build (§C step 1) times out twice OR
P1's `linarith` discharge stalls:

**Skip P1+P2 entirely**. Instead ship a smaller cosmetic deliverable:

### F-fallback (LAST RESORT, ~30 LOC) — `coef_α_eq_of_isConsistent` corollary

Cycle 342 P2 (`Eq422a_at_vertex_linear_of_isConsistent`) uses a
`push_cast + ring` step to bridge `SatisfiesEq404b`'s cast form
to the §422 coefficient form. Extract that bridge as a standalone
named lemma in §422:

```lean
theorem coef_α_eq_sum_β_of_isConsistent
    {k : ℕ} (M : OpenMath.Chapter4.Section404.LinearMultistepMethod k)
    (hCons : M.IsConsistent) :
    (∑ i : Fin k, ((i.val + 1 : ℕ) : ℝ) * M.α i.succ)
      = ∑ i : Fin (k + 1), M.β i := by
  -- extract from cycle 342 P2's body
  sorry  -- worker fills with the appropriate push_cast + ring chain
```

Plus a non-vacuity on `bdf2LMM` (`coef_α = 2/3 = sum_β`).

This isolates the cast bridge used by cycle 342 P2, making
downstream consumers (e.g., a future `Phase D′` that proves
`coef_α + coef_β > 0` under consistency) able to cite it directly.

The fallback ship is genuinely independent of the Section441 build
state — it touches only Section422 + Section451 (which builds cold
in <30s consistently). The `sorry` above is a placeholder for the
worker to fill — F-fallback does NOT ship with a sorry committed.

## §G — Verification checklist (run before commit)

1. `lake env lean OpenMath/Chapter4/Section422.lean` exits 0.
   Budget 6 min; per cycle 344 a 5-min run is typical.
2. `grep -c sorry OpenMath/Chapter4/Section422.lean` → 0.
3. Tautology scanner: `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$'
   OpenMath/Chapter4/Section422.lean` → no hits.
4. `#print axioms
   OpenMath.Chapter4.Section422.Eq422a_at_vertex_eta_eq_of_stable_preconsistent`
   via stdin → `[propext, Classical.choice, Quot.sound]` only.
5. Per-symbol axiom check on any new private helpers in P2.
6. Update `lean_status.json`: `def:422B` row stays `partial`;
   bump cycle reference to 345; append one-sentence summary of P1
   consolidation. **Do NOT mark `formalized`** — Phase D.3 +
   Phase E still gate the seal.
7. Update `plan.md`'s `def:422B` row with cycle 345 entry.
8. Append "Cycle 345 update" section to
   `.prover-state/issues/def_422B_path.md` at the existing "Cycle
   344 update" location, documenting P1 + P2 ship and the residual
   β-nonneg side hypothesis as a Phase D′ refinement target.
9. Write `.prover-state/task_results/cycle_345.md` per the
   CLAUDE.md template (Worked on / Approach / Result /
   Faithfulness check / Dead ends / Discovery / Suggested next
   approach).

## §H — Stretch ladder if cycle 345 has remaining time

After P1 + P2 (the cycle 345 ship bar):

1. **P3** explicit Euler non-vacuity (§B above, ~10 LOC).
2. **F-fallback** as a NAMED additive ship (not a fallback):
   extract `coef_α_eq_sum_β_of_isConsistent` (§F above, ~15 LOC).
   This is useful infrastructure regardless of P1+P2 outcome.
3. **Scoping doc update** for Phase D′ (β-side machinery): append
   to `def_422B_path.md` a new §A.0.3 sketching the
   `coef_β_pos_of_stable_consistent` proof obligation. Estimate
   LOC + cycle count. Do NOT ship Lean code; pure planning.

If cycle 345 hits all of P1+P2+P3+F-fallback, that's a strong
cycle. The §422 streak is now 9 consecutive cycles (336–344);
breaking it cleanly with a small consolidation maintains
momentum without ballooning into Phase D.3 multi-cycle work.

## §I — Cycle 346 outlook (for the next planner)

After cycle 345 ships the consolidation, cycle 346's planner has
two natural directions:

* **Phase D.3 proper** (HIGH risk, multi-cycle): scaffold
  `underlyingEta_aux : RootedTree → ℝ` by well-founded recursion
  on `RootedTree.order` (cycle 343's `WellFoundedRelation`),
  handling the τ base case via cycle 345's
  `Eq422a_at_vertex_eta_eq_of_stable_preconsistent` and the
  inductive step via a per-tree linear isolation argument. The
  cycle 344 worker recommends sorry-first scaffold + per-sorry
  issue files; per the cycle 149/150 / 200/201 precedents, this
  must be paired with a credible single-cycle close path OR a
  multi-phase decomposition matching `lem_310B_plan.md` /
  `lem_441A_phase_C_scoping.md` template depth.

* **Phase D′ refinement** (MEDIUM risk, 1–2 cycles): build the
  §441 β-side machinery to prove `coef_β` non-negativity (or
  `coef_α + coef_β > 0`) under stable + consistent. This would
  eliminate cycle 345's β-nonneg hypothesis and complete the
  `Eq422a_at_vertex_eta_eq_of_stable_consistent` story
  textbook-faithfully. Concrete prerequisite: define `βPoly` /
  bridge it through Section441 analogues of cycle 178's
  `ρPoly_deriv_eval_one_pos_of_stable_preconsistent`.

The planner should weigh these against pivot candidates from
`cycle_336_pivot_options.md` (thm:302A, thm:302B, etc.) per the
"variety vs. compounding focus" tradeoff documented in cycle 335.
