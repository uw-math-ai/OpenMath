# Cycle 346 strategy

## Context summary

Cycle 345 closed Phase D consolidation in `OpenMath/Chapter4/Section422.lean`:
* `Eq422a_at_vertex_eta_eq_of_stable_preconsistent` (load-bearing P1)
  — discharges the non-vanishing side hypothesis of cycle 342's
  `Eq422a_at_vertex_eta_eq` under stable + preconsistent `M`, modulo
  an explicit `hβ_nn : 0 ≤ coef_β(M)`.
* `coef_α_eq_sum_β_of_isConsistent` — named cast bridge extracted
  from cycle 342's body.
* Two non-vacuity `example`s on `explicitEulerLMM`.

All axiom-clean. Section422.lean: 759 → 864 LOC (+105).

**Deferred this cycle (per cycle 345 §"Dead ends" / §"Suggested
next approach"):** the BDF2 numerical non-vacuity for P1 was
*not* shipped because `bdf2LMM.IsStable` (Dahlquist-stable) does
not exist in the codebase. Only `bdf2LMM_isGStable` (Section451)
and `bdf2LMM_isAStable` (Section454) ship.

**Aristotle results**: none pending. No queued jobs to process.

**Streak observation**: cycles 336–345 = 10 consecutive §422 cycles.
Cycle 335 task results called for breaking the streak; cycle 336
opened §422 work which then ran 10 cycles, shipping a complete
Phase 0 + Phase A + Phase B + Phase C + Phase D chain. Phase D.3
(full inductive solver for `η : RootedTree → ℝ`) is multi-cycle
HIGH-risk per cycle 343/344's infrastructure work; pursuing it
now risks the same multi-cycle stall as cycle 200/201 (`thm:381H`
rollback) or cycle 149/150 (`def:530B` rollback). The cycle 345
worker's option 2 (`bdf2LMM_isStable`) is **LOW risk, single-cycle**,
and unblocks the deferred BDF2 non-vacuity — that's this cycle's
target.

## Primary deliverable — `bdf2LMM_isStable`

Ship `bdf2LMM.IsStable` (Dahlquist-stable) directly from the
definition in `OpenMath/Chapter4/Section404.lean:202`. Pattern after
the existing `explicitEulerLMM_isStable` proof (Section404:213) but
for the 2-step recurrence.

### Math

BDF2's homogeneous recurrence (Section404:189–191 unfolded on
`bdf2LMM`):

```
Y (m + 2) = (4/3) · Y (m + 1) - (1/3) · Y m,    ∀ m : ℕ.
```

Characteristic polynomial roots: `z = 1` and `z = 1/3` (both real,
both in closed unit disc, with root `1` simple ⇒ Dahlquist-stable
by Butcher Theorem 142F's criterion, but we prove directly).
General solution `Y_n = A + B · (1/3)^n` where:
* `A := (3 · Y 1 - Y 0) / 2`
* `B := (3 · (Y 0 - Y 1)) / 2`

Derivation (paper): `Y_0 = A + B`, `Y_1 = A + B/3` ⇒
`Y_0 - Y_1 = 2B/3` ⇒ `B = (3/2)(Y_0 - Y_1)`,
`A = Y_0 - B = (3·Y_1 - Y_0)/2`. Sanity check:
`A + B/3 = (3·Y_1 - Y_0)/2 + (Y_0 - Y_1)/2 = (3·Y_1 - Y_0 + Y_0 - Y_1)/2 = Y_1` ✓.

Boundedness: `|Y_n| ≤ |A| + |B| · (1/3)^n ≤ |A| + |B|` since
`(1/3)^n ≤ 1`. So `C := |A| + |B|` witnesses
`∃ C, ∀ n, |Y n| ≤ C`.

### Lean recipe

Place the two new theorems in `OpenMath/Chapter4/Section451.lean`
immediately after `bdf2LMM_isAStable` (line ~238+). Reason:
Section451 already has `bdf2LMM` in scope, imports Section404
(`IsStable`/`IsHomogeneousSolution` definitions), and is downstream
of Section454; placing the new theorem here lets Section422-side
consumers (which already import Section451 transitively via cycle
344's `coef_α` bridge in Section422) use `bdf2LMM_isStable`
without further import work.

```lean
namespace OpenMath.Chapter4.Section404

/-- BDF2's homogeneous-recurrence solutions decompose as
`Y_n = A + B · (1/3)^n` where
`A := (3 · Y 1 - Y 0) / 2` and `B := (3 · (Y 0 - Y 1)) / 2`.

Proved by strong induction on `n`; base cases at `n = 0, 1` are
direct arithmetic, and the inductive step at `n + 2` uses the
homogeneous recurrence `Y (n+2) = (4/3) · Y (n+1) - (1/3) · Y n`
plus the IH at `n + 1` and `n`. -/
private theorem bdf2_solution_decomp (Y : ℕ → ℝ)
    (hY : bdf2LMM.IsHomogeneousSolution Y) :
    ∀ n, Y n = (3 * Y 1 - Y 0) / 2
              + (3 * (Y 0 - Y 1)) / 2 * (1 / 3 : ℝ) ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp; ring
    | 1, _ => simp; ring
    | n + 2, ih =>
      have hrec : Y (n + 2) = (4 / 3 : ℝ) * Y (n + 1) - (1 / 3) * Y n := by
        have h := hY n
        simp only [bdf2LMM, Fin.sum_univ_two,
                   show (n + 2 - (0 + 1) : ℕ) = n + 1 from by omega,
                   show (n + 2 - (1 + 1) : ℕ) = n from by omega] at h
        linarith
      rw [hrec, ih (n + 1) (by omega), ih n (by omega)]
      ring

/-- BDF2 is Dahlquist-stable (Butcher §403, p. 341).

Every solution of BDF2's homogeneous recurrence is bounded:
the explicit decomposition (`bdf2_solution_decomp`) yields
`|Y_n| ≤ |A| + |B|`. -/
theorem bdf2LMM_isStable : bdf2LMM.IsStable := by
  intro Y hY
  refine ⟨|((3 * Y 1 - Y 0) / 2)| + |((3 * (Y 0 - Y 1)) / 2)|,
          fun n => ?_⟩
  rw [bdf2_solution_decomp Y hY n]
  have h_one_third_nonneg : (0 : ℝ) ≤ 1 / 3 := by norm_num
  have h_one_third_le_one : (1 / 3 : ℝ) ≤ 1 := by norm_num
  calc |((3 * Y 1 - Y 0) / 2) + ((3 * (Y 0 - Y 1)) / 2) * (1 / 3 : ℝ)^n|
      ≤ |((3 * Y 1 - Y 0) / 2)|
        + |((3 * (Y 0 - Y 1)) / 2) * (1 / 3 : ℝ)^n| := abs_add _ _
    _ = |((3 * Y 1 - Y 0) / 2)|
        + |((3 * (Y 0 - Y 1)) / 2)| * |(1 / 3 : ℝ)^n| := by rw [abs_mul]
    _ ≤ |((3 * Y 1 - Y 0) / 2)|
        + |((3 * (Y 0 - Y 1)) / 2)| * 1 := by
        gcongr
        rw [abs_pow, abs_of_nonneg h_one_third_nonneg]
        exact pow_le_one₀ h_one_third_nonneg h_one_third_le_one
    _ = |((3 * Y 1 - Y 0) / 2)|
        + |((3 * (Y 0 - Y 1)) / 2)| := by ring

end OpenMath.Chapter4.Section404
```

### Pre-flight verification (5 min)

Before writing the proof:

1. **Verify `IsHomogeneousSolution`'s shape on `bdf2LMM`.** Inspect
   Section404:189–191. The unfold yields
   `Y (m+2) = ∑ i : Fin 2, bdf2LMM.α i.succ * Y (m+2 - (i.val + 1))`.
   `Fin.sum_univ_two` gives:
   * `i = 0`: `bdf2LMM.α 1 * Y (m+2 - 1) = (4/3) · Y (m+1)`
   * `i = 1`: `bdf2LMM.α 2 * Y (m+2 - 2) = (-1/3) · Y m`
   So `Y (m+2) = (4/3) · Y (m+1) + (-1/3) · Y m`. The Nat-subtraction
   `m + 2 - 1 = m + 1` and `m + 2 - 2 = m` need explicit `omega`
   side-conditions (already in the sketch via the `show` blocks).
   The `bdf2LMM.α (0:Fin 2).succ = bdf2LMM.α 1 = 4/3` and
   `bdf2LMM.α (1:Fin 2).succ = bdf2LMM.α 2 = -1/3` unfolds need
   `simp only [bdf2LMM]` to expose the match. The `+ (-1/3)·Y n`
   ↔ `- (1/3)·Y n` form-bridge closes by `linarith` (no manual
   rewriting needed).
2. **`Nat.strong_induction_on` motive with `match` on `n`**: should
   propagate `ih` correctly. If Lean complains about motive
   inference, fall back to:
   ```lean
   intro n
   induction n using Nat.strong_induction_on with
   | _ n ih =>
     rcases n with _ | _ | n
     · simp; ring  -- n = 0
     · simp; ring  -- n = 1
     · -- n + 2 case: use ih at (n+1) and n
       ...
   ```
   Either form should work; the `match` is slightly cleaner.
3. **`pow_le_one₀` name**: Mathlib's name may have drifted. Try
   `pow_le_one₀ (h0 : 0 ≤ a) (h1 : a ≤ 1) : a^n ≤ 1` first; if it
   doesn't fire, try `pow_le_one`, `pow_le_one_of_le_one`. Verify
   with `lean_local_search "pow_le_one"`.

## Secondary deliverable — `coef_β` non-negativity helper + numerical witnesses

After PRIMARY lands, ship the following additive helpers in
`OpenMath/Chapter4/Section422.lean` immediately after cycle 345's
deliverables (current EOF ~864):

```lean
/-- If every β-coefficient of an LMM is non-negative, then so is
`coef_β(M) := ∑ i, (i.val : ℝ) · M.β i`. Pure structural
helper; one-line via `Finset.sum_nonneg` + `mul_nonneg`. -/
theorem coef_β_nonneg_of_β_nonneg
    {k : ℕ} (M : LinearMultistepMethod k)
    (hβ : ∀ i : Fin (k + 1), 0 ≤ M.β i) :
    0 ≤ ∑ i : Fin (k + 1), ((i.val : ℕ) : ℝ) * M.β i := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (Nat.cast_nonneg _) (hβ i)

/-- BDF2's β-coefficients are all non-negative. -/
theorem bdf2LMM_β_nonneg : ∀ i : Fin (2 + 1), 0 ≤ bdf2LMM.β i := by
  intro i
  fin_cases i <;> simp [bdf2LMM] <;> norm_num

/-- BDF2's `coef_β` is non-negative (in fact = 0, since
`β 1 = β 2 = 0`). -/
theorem bdf2LMM_coef_β_nonneg :
    0 ≤ ∑ i : Fin (2 + 1), ((i.val : ℕ) : ℝ) * bdf2LMM.β i :=
  coef_β_nonneg_of_β_nonneg bdf2LMM bdf2LMM_β_nonneg
```

Naming convention: `coef_β_nonneg_of_β_nonneg` mirrors cycle
344's `coef_α_pos_of_stable_preconsistent` naming style.

## Stretch — BDF2 P1 non-vacuity (full closure of cycle 345 deferral)

If PRIMARY and SECONDARY both land cleanly with budget remaining,
ship the BDF2 specialization that cycle 345 deferred. Place in
Section422.lean just after `bdf2LMM_coef_β_nonneg`:

**Numerical sanity check first** (do NOT skip — verify the closed
form before writing the example):

For BDF2 (k = 2):
* `coef_α(M) = ∑ i : Fin 2, ((i.val + 1 : ℕ) : ℝ) · M.α i.succ`
  = `1 · (4/3) + 2 · (-1/3) = 4/3 - 2/3 = 2/3`. ✓ Matches cycle 344's
  `bdf2LMM.coef_α = 2/3`.
* `coef_β(M) = ∑ i : Fin 3, ((i.val : ℕ) : ℝ) · M.β i`
  = `0 · (2/3) + 1 · 0 + 2 · 0 = 0`.
* `sum_β(M) = ∑ i : Fin 3, M.β i = 2/3 + 0 + 0 = 2/3`.

Therefore `η(τ) = sum_β / (coef_α + coef_β) = (2/3) / (2/3 + 0) = 1`.

So **BDF2's `η(τ) = 1`**, NOT 1/2 (which is the explicit Euler
case in cycle 345 because explicit Euler has `coef_α = 1, coef_β = 1,
sum_β = 1` ⇒ `1/(1+1) = 1/2`).

```lean
/-- BDF2 specialisation of cycle 345's
`Eq422a_at_vertex_eta_eq_of_stable_preconsistent`. The
underlying-one-step-method `η ∈ G₁` corresponding to BDF2 has
`η(τ) = 1` (verified numerically: coef_α = 2/3, coef_β = 0,
sum_β = 2/3, so η(τ) = (2/3) / (2/3 + 0) = 1). -/
example {η_q : Quotient OpenMath.Chapter3.Section312.RKTableau.PhiEquivalent.setoidSigma}
    (hEq : Eq422a bdf2LMM η_q) :
    elementaryWeightQ_phi η_q OpenMath.Chapter3.Section310.RootedTree.vertex = 1 := by
  have h := Eq422a_at_vertex_eta_eq_of_stable_preconsistent
    bdf2LMM hEq (by norm_num) bdf2LMM_isStable bdf2LMM_isPreconsistent
    bdf2LMM_coef_β_nonneg
  rw [h]
  -- Goal reduces to (sum_β) / (coef_α + coef_β) = 1
  simp [bdf2LMM, Fin.sum_univ_two, Fin.sum_univ_three]
  norm_num
```

The `RootedTree.vertex` reference may need namespace qualification
(`OpenMath.Chapter3.Section310.RootedTree.vertex`) per Section422's
existing examples. If the `simp` fails to reduce, fall back to
explicit `unfold` of `coef_α` / `coef_β` / `sum_β` (these names
may not exist as `def`s — check Section422 for whether cycle 344
introduced them as `def`s or only as inline sums; the cycle 345
update suggests they appear inline in the theorem statements). If
they're inline, write the goal verbatim and use `simp [bdf2LMM,
Fin.sum_univ_two, Fin.sum_univ_three]; norm_num` to close.

## Ship checklist

1. **Pre-flight** (5 min): `lake env lean OpenMath/Chapter4/Section451.lean`
   warm smoke test. Then `lean_hover_info` on
   `bdf2LMM.IsHomogeneousSolution` and on `pow_le_one₀` to confirm
   shapes. Read Section404:213–225 (`explicitEulerLMM_isStable`
   template) and Section451:140–151 (`bdf2LMM` definition).
2. **Write `bdf2_solution_decomp`** as a private theorem in
   Section451.lean immediately after `bdf2LMM_isAStable`. Build:
   `lake env lean OpenMath/Chapter4/Section451.lean`.
3. **Write `bdf2LMM_isStable`** consuming the decomposition. Build.
4. **Write SECONDARY (β-helpers + BDF2 numerical witness)** in
   Section422.lean. Build:
   `lake env lean OpenMath/Chapter4/Section422.lean`.
5. **STRETCH (if budget allows)**: write the BDF2 P1 non-vacuity
   example. Build.
6. **Axiom check**: `#print axioms` on `bdf2LMM_isStable`,
   `coef_β_nonneg_of_β_nonneg`, `bdf2LMM_β_nonneg`, `bdf2LMM_coef_β_nonneg`.
   Confirm `[propext, Classical.choice, Quot.sound]` only on each.
   The `bdf2_solution_decomp` is `private` so its axioms don't
   matter for the public surface but should also be clean.
7. **Sorry count**:
   `grep -c sorry OpenMath/Chapter4/Section{422,451}.lean` → 0/0.
8. **Tautology scanner**:
   `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/Chapter4/Section{422,451}.lean`
   → no hits.
9. **lean_status.json**: no entity row changes — `bdf2LMM_isStable`
   is not a textbook entity but an infrastructure theorem;
   `def:422B` row gets a one-line cycle 346 note in its `notes`
   field documenting the BDF2 non-vacuity stretch (if shipped).
10. **plan.md**: no `[x]`/`[~]`/`[ ]` state changes expected
    (§422 row stays `[~]` per def:422B's partial status; §451
    row's `bdf2LMM_isGStable` reference can be amplified with a
    cycle 346 note mentioning the new `bdf2LMM_isStable` — both
    are inline notes, not state changes).
11. **task_results/cycle_346.md** — standard sections.
12. **Commit + push** with standard `Cycle 346 — bdf2LMM_isStable …`
    message.

## What NOT to try

* **Do NOT attempt Phase D.3** (the `underlyingEta_aux`
  well-founded-recursion inductive solver). Per cycle 345's
  "Suggested next approach" option 3, this is multi-cycle HIGH-risk
  work requiring per-tree linear isolation. A sorry-first scaffold
  would trigger the cycle 200/201 / cycle 149/150 rollback pattern.
  Out of scope for cycle 346.

* **Do NOT attempt the general Phase D′ β-side machinery**
  (analog of cycle 178's `ρPoly_deriv_eval_one_pos_of_stable_preconsistent`
  but for `coef_β`). Per cycle 345 option 1, this requires defining
  `βPoly` analogous to `ρPoly` (Section441), bridging `coef_β` to
  its derivative, and proving non-negativity from
  `M.IsStable + M.IsConsistent` alone. Multi-cycle. The
  `coef_β_nonneg_of_β_nonneg` general helper proposed above
  takes `(∀ i, 0 ≤ M.β i)` as an explicit hypothesis — strictly
  weaker mathematically but a guaranteed single-cycle additive
  ship that unblocks BDF2 numerically.

* **Do NOT pivot to a fresh entity** from `cycle_336_pivot_options.md`.
  The cycle 345 deliverable's BDF2 non-vacuity deferral is a
  natural, small, well-scoped closure target. Pivoting to
  `thm:302A` (definition-smuggling risk per
  `cycle_250_strategy_alpha_definition_error.md`), `thm:302B`
  (multi-cycle PowerSeries infrastructure per cycle 336 §A audit),
  or `thm:384A` (blocked on `Equivalent → PhiEquivalent`, see
  cycle 239 update + `thm_381H_deferred.md`) would trade a
  guaranteed single-cycle ship for unclear scope.

* **Do NOT try to derive `bdf2LMM_isStable` from `bdf2LMM_isGStable`
  or `bdf2LMM_isAStable`**. The bridges `IsGStable ⇒ IsStable` and
  `IsAStable ⇒ IsStable` are non-trivial theorems (A-stability and
  G-stability concern the test equation / Lyapunov contraction
  function, while Dahlquist `IsStable` concerns the *pure
  homogeneous recurrence* — they coincide on certain method classes
  but the implication is not automatic in general). Building such
  a bridge is its own multi-cycle task. The direct decomposition
  above (~80 LOC including helper) is shorter.

* **Do NOT touch `Section441.lean`** — 43+ consecutive GPFS-blocked
  compile timeouts since cycle 182 (most recent: cycle 239's 43rd
  timeout). Skip per `.prover-state/issues/cycle_182_gpfs_slowness.md`.
  `bdf2LMM_isStable`'s proof does NOT require Section441
  infrastructure (it uses direct algebraic decomposition, not the
  §441 `ρPoly`-root machinery from cycles 175–178).

* **Do NOT introduce `sorry`/`axiom`/`constant`**. PRIMARY has a
  fully sketched closed proof; SECONDARY is trivial; STRETCH is a
  one-liner over both. All axiom-clean closure expected.

* **Do NOT introduce `maxHeartbeats` overrides above 200000**.
  The strong induction `match` plus three `ih` calls should fit
  well within default heartbeats. If something blows up, decompose
  further (e.g. extract the inductive step's `ring` manipulation
  into a `private lemma`).

* **Do NOT modify `scripts/autonomous_loop.py`** or any supervisor
  prompt-builder logic. Phantom commit verdicts (per
  `.prover-state/issues/phantom_commit_verdict_pattern.md`) are
  loop-maintainer territory. Cycle 345 scored 1 per the cycle
  summary noting "heartbeat-only git diff … phantom-commit-verdict
  pattern"; cycle 346 should proceed normally and not chase scanner
  false positives. The supervisor's diff-snapshot can lag behind
  the commit; trust `git log -1 --stat HEAD` not the supervisor's
  reported diff.

## Fallback if PRIMARY stalls

If `bdf2_solution_decomp`'s strong induction hits a Lean elaboration
issue (e.g. `match` pattern incompatibility with strong induction's
motive, `Nat.strong_induction_on` API drift, or `simp only [bdf2LMM,
Fin.sum_univ_two, ...]` failing to expose the recurrence cleanly):

1. **Try the `rcases n with _ | _ | n` fallback** (per pre-flight
   verification #2). This is the standard Mathlib idiom for
   "split into n=0, n=1, n+2" without `match` on the motive.
2. **Try splitting the recurrence unfold into a separate `have`**:
   ```lean
   have hrec_unfold : ∀ m,
       Y (m + 2) = (4 / 3 : ℝ) * Y (m + 1) + (-1 / 3) * Y m := by
     intro m
     have h := hY m
     simp only [bdf2LMM, Fin.sum_univ_two] at h
     -- normalize Nat subtraction
     have h1 : (m + 2 - (0 + 1) : ℕ) = m + 1 := by omega
     have h2 : (m + 2 - (1 + 1) : ℕ) = m := by omega
     rw [h1, h2] at h
     linarith
   ```
   Then use `hrec_unfold n` inside the inductive step.
3. **If `match n, ih with` causes universe / motive issues**, use:
   ```lean
   match n with
   | 0 => simp; ring
   | 1 => simp; ring
   | n + 2 => -- here `ih` is the closure from the outer induction
     ...
   ```
4. **If those also stall**, DROP PRIMARY entirely and ship just
   SECONDARY (`coef_β_nonneg_of_β_nonneg` + numerical witnesses
   for `bdf2LMM`, `explicitEulerLMM`, `implicitEulerLMM`). This
   is a guaranteed clean ~40 LOC ship that doesn't unblock BDF2
   non-vacuity (STRETCH becomes infeasible without PRIMARY) but
   adds reusable Phase D′ infrastructure plus three numerical
   witnesses. The scope falls from "Phase D consolidation +
   stretch" to "additive helpers" — still strictly additive,
   axiom-clean, sorry count 0.

This ensures cycle 346 ships *something* axiom-clean and
non-trivial regardless of PRIMARY's outcome.

## Time budget

* Pre-flight + Lean MCP checks: 10 min.
* PRIMARY (`bdf2_solution_decomp` + `bdf2LMM_isStable`): 45 min.
* SECONDARY (β-helpers + BDF2 numerical): 15 min.
* STRETCH (BDF2 P1 non-vacuity example): 15 min.
* Axiom check + sorry/tautology scan + housekeeping: 10 min.
* Commit + push: 5 min.

Total: ~100 min. Within typical cycle budget.

If PRIMARY runs over 60 min, switch to fallback (SECONDARY only).
