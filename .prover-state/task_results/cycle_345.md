# Cycle 345 Results

## Worked on

§422 Phase D consolidation, per planner strategy:

* **P1** (load-bearing, ~30 LOC): `Eq422a_at_vertex_eta_eq_of_stable_preconsistent`
  — corollary of cycle 342's `Eq422a_at_vertex_eta_eq` that discharges
  its non-vanishing side hypothesis under stable + preconsistent `M`
  via cycle 344's `coef_α_pos_of_stable_preconsistent`, modulo an
  explicit β-side non-negativity hypothesis.
* **P2** (non-vacuity, ~15 LOC): bare `example` on
  `explicitEulerLMM` exercising the full P1 chain and pinning
  `η(τ) = 1/2`. (BDF2 variant skipped — `bdf2LMM_isStable` not yet
  shipped; only `bdf2LMM_isGStable` / `bdf2LMM_isAStable` exist.)
* **P3 / F-fallback as named additive ship** (~20 LOC):
  `coef_α_eq_sum_β_of_isConsistent` extracts the `push_cast`/`ring`
  cast bridge from cycle 342's `Eq422a_at_vertex_linear_of_isConsistent`
  body so future Phase D′ consumers can cite it directly. Plus a
  one-line non-vacuity `example` on `explicitEulerLMM`.

All ships strictly additive to `OpenMath/Chapter4/Section422.lean`.

## Approach

Followed §B P1 of the planner strategy verbatim:

1. **Pre-flight** (per §C). Cold-built `Section422.lean` (build
   completed cleanly via dependency cache → no Section441 rebuild
   needed); verified cycle 342's `Eq422a_at_vertex_eta_eq` signature
   at line 662; confirmed `coef_α_pos_of_stable_preconsistent` at
   line 736.
2. **BDF2 stability gap** (per §C step 5): `bdf2LMM_isStable`
   (Dahlquist-stable, `LinearMultistepMethod.IsStable`) does **not**
   exist in the codebase. Only `bdf2LMM_isGStable` (Section451)
   and `bdf2LMM_isAStable` (Section454) ship. The strategy's §B
   P2 fallback ("replace with inline proof or skip P2's BDF2
   specialization in favor of P3's explicit Euler version") triggered;
   shipped the explicit Euler non-vacuity as the primary witness.
3. **P1**: applied `Eq422a_at_vertex_eta_eq hEq`; the residual
   side-goal was `coef_α + coef_β ≠ 0`, discharged by
   `coef_α_pos_of_stable_preconsistent M hk hStab hPre`
   (`coef_α > 0`) plus the explicit `hβ_nn : 0 ≤ coef_β`
   hypothesis, closed by `linarith`. No `field_simp`/`push_cast`
   needed — those fire inside cycle 342's underlying theorem.
4. **P2**: applied P1 with `explicitEulerLMM_isStable`,
   `explicitEulerLMM_isPreconsistent`, `Nat.one_pos`, and a
   `by simp [explicitEulerLMM, Fin.sum_univ_two]` discharge of
   `hβ_nn` (β-coef = 0·0 + 1·1 = 1 ≥ 0). Final goal reduces to
   `1 / (1 + 1) = 1/2`, closed by `simp + norm_num`. One iteration
   needed to remove an unnecessary inner `norm_num` and unused
   `Fin.sum_univ_one` simp arg flagged by the linter (lint+build
   passed second time, exit 0).
5. **F-fallback ship**: extracted the `push_cast`+`ring` cast
   bridge from `Eq422a_at_vertex_linear_of_isConsistent` lines
   623–635 verbatim, named it `coef_α_eq_sum_β_of_isConsistent`.
   Plus a one-line non-vacuity on `explicitEulerLMM`
   (`explicitEulerLMM_isConsistent` already in Section404).

## Result

**SUCCESS.** Three new public symbols (2 theorems + 1 `example`)
plus two non-vacuity `example`s shipped to Section422.lean.
`lake env lean OpenMath/Chapter4/Section422.lean` exits 0 with no
warnings. `grep -c sorry OpenMath/Chapter4/Section422.lean` → 0.
Tautology scanner (`rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$'`)
→ no hits. Axiom check via `#print axioms` on the two new public
theorems pending in this writeup (output to be appended after
the cold `lean_axiom_check_345.lean` run completes).

LOC trajectory: Section422.lean 759 → 864 (+105). Within the
strategy's stated budget (~30 + 15 + 20 = ~65 LOC; observed
slightly higher due to docstrings).

**Axiom check (verified via temporary `#print axioms` block at
end of Section422.lean, removed before commit):**

```
'OpenMath.Chapter4.Section422.Eq422a_at_vertex_eta_eq_of_stable_preconsistent'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'OpenMath.Chapter4.Section422.coef_α_eq_sum_β_of_isConsistent'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

Both new public theorems axiom-clean.

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `Eq422a_at_vertex_eta_eq_of_stable_preconsistent`

* No standalone textbook entity ID — this is a derived
  *corollary* of cycle 342's `Eq422a_at_vertex_eta_eq` (which
  itself implements Butcher §422 p. 1163's η-coefficient
  determination).
* Textbook statement (Butcher §422, `extraction/raw_text/ch04.txt:1163`):
  > "the coefficient of η(τ) on the left-hand side is
  > −(α₁ + 2α₂ + ⋯ + kα_k)" [...] "and this is non-zero because
  > the method is stable and consistent."
* Lean statement captures: **weaker than the textbook claim**. The
  textbook asserts `coef_α + coef_β ≠ 0` from
  "stable + consistent" alone (via the polynomial-derivative
  positivity argument routed through §441). Our P1 surfaces an
  *explicit* `hβ_nn : 0 ≤ coef_β` hypothesis because the §441
  β-side machinery analogous to cycle 178's
  `ρPoly_deriv_eval_one_pos_of_stable_preconsistent` (which
  closes the α-side) has not yet been built. The α-side
  positivity is closed (cycle 344). The β-side closure is
  deferred to a future Phase D′ cycle.
* Justification for divergence: documented in the docstring
  ("residual textbook assumption [...] Phase D′ refinement
  cycle") and in the §H of the planner strategy.

### `coef_α_eq_sum_β_of_isConsistent`

* No standalone textbook entity ID — this is the cast bridge
  for Butcher's (404b) equation. Functionally equivalent to
  `M.IsConsistent.2 : M.SatisfiesEq404b` modulo a cast form
  difference.
* Textbook statement (Butcher §404, p. 342, equation (404b)):
  > "α₁ + 2α₂ + ⋯ + kα_k = β₀ + β₁ + ⋯ + β_k"
* Lean statement captures: **same content**, with the §422
  coefficient cast form `((i.val + 1 : ℕ) : ℝ)` on the LHS
  (matching `coef_α(M)` in `Eq422a_at_vertex_linear`) versus
  the §404 cast form `((i : ℕ) + 1 : ℝ)` in
  `LinearMultistepMethod.SatisfiesEq404b`. The two cast forms
  are propositionally equal via `push_cast`+`ring`; this theorem
  packages that equivalence under the `IsConsistent` hypothesis
  (so callers don't have to redo the cast bridge inline).
* Hypothesis strength: matches textbook `IsConsistent` exactly
  (no extra hypotheses).

### `example` witnesses

* **explicit Euler P1 non-vacuity** (`η(τ) = 1/2`): exercises
  the full P1 chain. Routes through `explicitEulerLMM_isStable`
  (Section404), `explicitEulerLMM_isPreconsistent` (Section404),
  and `Nat.one_pos`. No new mathematical content; only confirms
  P1 is non-vacuous at the canonical 1-step example.
* **`coef_α_eq_sum_β_of_isConsistent` non-vacuity**: one-line
  application to `explicitEulerLMM_isConsistent`. Confirms the
  textbook (404b) equation holds on the canonical example.

Both `example`s match the textbook (both Eulers are k=1
preconsistent + consistent + stable per Butcher §404/§403).

## Dead ends

* **BDF2 non-vacuity for P1**: planner strategy P2 expected
  `bdf2LMM_isStable`, but only `bdf2LMM_isGStable` and
  `bdf2LMM_isAStable` exist. Proving Dahlquist-stability
  (`IsStable`) for BDF2 inline would require the
  homogeneous-recurrence boundedness argument from scratch
  (multi-cycle work, not in scope). Switched to the explicit
  Euler non-vacuity (planner strategy §B P3 stretch) as the
  primary witness instead. The §454 `gStable_isAStable`
  bridge does not chain back to `IsStable` — that would be
  a separate `gStable_isStable` theorem, also not yet built.
* **First-pass build failure (~5s waste)**: inner `(by simp; norm_num)`
  block for the explicit Euler `hβ_nn` discharge had a redundant
  `norm_num` that fired after `simp` already closed the goal,
  triggering "No goals to be solved". Plus an unused
  `Fin.sum_univ_one` simp arg flagged by the linter on the outer
  final-goal simp. Both fixed in the second pass (removed inner
  `norm_num`, removed `Fin.sum_univ_one`). Second build clean.

## Discovery

* **`Eq422a_at_vertex_eta_eq` consumes its non-vanishing
  hypothesis additively**: the cycle 342 signature takes
  `hEq` then `h_ne` as explicit args. `apply Eq422a_at_vertex_eta_eq hEq`
  leaves `h_ne : coef_α + coef_β ≠ 0` as the only residual
  side-goal. The discharge via `coef_α > 0` + `0 ≤ coef_β`
  ⇒ `coef_α + coef_β > 0 ≠ 0` is exactly two `linarith` hints
  — no `field_simp`/`push_cast`/`ring` plumbing needed at the
  consolidation layer.
* **The `IsStable` ⇒ `IsAStable` / `IsGStable` chain is one-way
  in current Section454**: `bdf2LMM_isGStable` and
  `bdf2LMM_isAStable` exist, but no `bdf2LMM_isStable`
  (Dahlquist-stable). This means downstream consumers of
  `IsStable` cannot currently leverage BDF2's strong stability
  witnesses. Worth a future Phase D′ note: build
  `gStable_isStable` (or `aStable_isStable`) bridges so the
  cycle 345 P1 corollary can be instantiated on BDF2 directly.
* **`coef_α_eq_sum_β_of_isConsistent` cast bridge is reusable**:
  the cycle 342 `Eq422a_at_vertex_linear_of_isConsistent` body
  inlines the `push_cast`+`ring` bridge from the §404 cast form
  `((i : ℕ) + 1 : ℝ)` to the §422 cast form
  `((i.val + 1 : ℕ) : ℝ)`. Now that it's named, any future
  Phase D′ consumer (e.g. a `coef_β_pos_of_stable_consistent`)
  can cite it directly instead of re-implementing the bridge.

## Suggested next approach

Two natural continuations for cycle 346:

1. **Phase D′ refinement (MEDIUM risk, 1–2 cycles)**: build the
   §441 β-side machinery to prove `coef_β ≥ 0` (or
   `coef_α + coef_β > 0`) under `M.IsStable + M.IsConsistent`,
   eliminating the explicit `hβ_nn` hypothesis in P1. Concrete
   prerequisites:
   * Define `βPoly` analogous to `ρPoly` (Section441)
   * Bridge `coef_β = β-poly-derivative-at-1` (analog of
     cycle 344's α-side bridge)
   * Bridge `M.IsConsistent ⇒ β-poly-derivative-at-1 ≥ 0`
   * Compose to ship `Eq422a_at_vertex_eta_eq_of_stable_consistent`
     (no explicit β hypothesis)
2. **`bdf2LMM_isStable` ship (LOW risk, ~30 LOC)**: build the
   `IsAStable ⇒ IsStable` bridge (or `IsGStable ⇒ IsStable`)
   in Section454, then ship `bdf2LMM_isStable` as a one-line
   corollary. This unblocks the BDF2 non-vacuity for cycle 345 P1
   that was deferred this cycle.
3. **Phase D.3 proper** (HIGH risk, multi-cycle): scaffold
   `underlyingEta_aux : RootedTree → ℝ` by well-founded recursion
   on `RootedTree.order` (cycle 343's `WellFoundedRelation`),
   handling τ via cycle 345's
   `Eq422a_at_vertex_eta_eq_of_stable_preconsistent` and the
   inductive step via per-tree linear isolation. The cycle 344
   worker flagged HIGH risk + 100–200 LOC, contingent on Aristotle
   batch decomposition and credible single-cycle close paths.

Option 1 or 2 are the additive low-risk options; option 3 is the
phase-D.3 main thrust. Per the cycle 335 "variety vs. compounding
focus" note, after 10 consecutive §422 cycles (336–345) a pivot
to `cycle_336_pivot_options.md` candidates (thm:302A, thm:302B,
etc.) is also reasonable.
