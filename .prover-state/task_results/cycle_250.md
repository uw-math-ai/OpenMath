# Cycle 250 Results

## Worked on

`RootedTree.alphaWeight` (Butcher §302, elementary weight α(t)) — bare
definition + base case + 4 non-vacuity witnesses. Placed in
`OpenMath/Chapter3/Section301.lean` (not Section310 as the strategy
suggested; Section310 cannot import the σ/γ machinery without a cycle).

## Approach

**Priority 0 / Priority 1 (inventory)**: confirmed HEAD at cycle 249
(`0aa1ec0`). Found `RootedTree.order` already exists in Section310.lean
(line 98), so per strategy Section D, pivoted to Phase B
(`alphaWeight`). Read Section301.lean to confirm `density`, `symmetry`,
and `tau_values` (which gives `r(τ)=σ(τ)=γ(τ)=1`) are all available.

**Faithfulness check on the strategy itself**: the strategy's Phase B
proposed `α(t) := 1/γ(t)` labelled "Butcher §312, the γ-only form".
Cross-referenced against `extraction/raw_text/ch03.txt:207–223`:
Butcher's α(t) is defined in §302 (NOT §312) via Theorem 302A as
`α(t) = r(t)!/(σ(t)γ(t))`. The "γ-only form" is a planner hedge that
smuggles an incorrect definition under the textbook name. Filed
`.prover-state/issues/cycle_250_strategy_alpha_definition_error.md`
documenting the error for future planner cycles. Per memory
`feedback_planner_faithfulness_spotcheck.md` and CLAUDE.md
"Definition smuggling check", pivoted to the correct (302a) definition.

**Priority 2 (definition + base case)** in Section301.lean:
```lean
noncomputable def alphaWeight (t : RootedTree) : ℝ :=
  (Nat.factorial (order t) : ℝ) / ((symmetry t : ℝ) * (density t : ℝ))

theorem alphaWeight_vertex : alphaWeight (mk []) = 1 := by
  unfold alphaWeight
  obtain ⟨hr, hs, hd⟩ := tau_values
  rw [hr, hs, hd]
  norm_num
```

**Non-vacuity witnesses (4 ≥ strategy's 3)**:
- `alphaWeight vertex = 1` (r=1).
- `alphaWeight cherry = 1` (r=2).
- `alphaWeight broom₃ = 1` (r=3, σ=2, γ=3 → 6/6 = 1).
- `alphaWeight (mk [vertex, cherry]) = 3` (r=4, σ=1, γ=8 → 24/8 = 3).

The fourth witness is the critical regression check: under the
strategy's wrong `1/γ` definition this would have evaluated to 1/8;
under the correct (302a) it gives the value 3 matching Butcher Table
310(II) row r=4, second entry (`f'(f, f'f)`).

Each witness proof uses `unfold alphaWeight`, then `rw` with three
`rfl`-resolved ℕ-valued equations for `order`/`symmetry`/`density`, then
`norm_num [Nat.factorial]` to close the real-arithmetic identity.

## Result

**SUCCESS.**

- `lake env lean OpenMath/Chapter3/Section301.lean`: clean.
- `lake build OpenMath.Chapter3.Section301`: built (1933 jobs, 18s).
- `#print axioms RootedTree.alphaWeight`:
  `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
- `#print axioms RootedTree.alphaWeight_vertex`:
  `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
- `grep -c sorry`: 0 in Section301.lean and Section310.lean.
- Tautology scanner: 0 hits.
- LOC delta: Section301 228 → 301 (+73, matches strategy's ~25–35 LOC
  estimate plus the extended faithfulness comment, the extra witness,
  and the issue cross-reference docstring).

## Faithfulness check

For each new `def`/`theorem` introduced this cycle:

### `RootedTree.alphaWeight`

- Entity ID: no extracted entity (α(t) is named throughout Butcher §302
  but is not a separately-extracted definition/theorem entity — it
  appears as a variable in `def_310A`, `lem_310B`, `lem_312B`, and is
  characterised by Theorem 302A). Textbook statement (Theorem 302A
  equation (302a), `extraction/raw_text/ch03.txt:212–213`):

  > α(t) = r(t)! / (σ(t)γ(t))

- Lean statement captures: **same content** under the same convention
  used for `RootedTree.symmetry` in cycle 017 (define via the closed
  form, treat the textbook-textual definition as an unformalised
  mathematical fact). Butcher introduces α textually as a labelling
  count, then proves (302a). The faithful Lean encoding would (a)
  define α as the labelling count, (b) prove (302a) follows. We adopt
  (302a) as the stipulative definition; the equivalence with the
  labelling count is deferred.

- Faithfulness convention: identical to and documented alongside the
  σ-symmetry-group convention. Downstream consumers (`lem:310B`,
  `lem:312B`, …) consume only the closed-form value.

### `RootedTree.alphaWeight_vertex`

- Entity ID: derivable corollary of `def_310A`/`thm_301A` for the
  elementary tree τ.
- Lean statement captures: **same content**. The combined (301d) base
  cases `r(τ) = σ(τ) = γ(τ) = 1` plus the (302a) definition give
  `α(τ) = 1!/(1·1) = 1`, which is what Lean proves.

### Tautology check (per CLAUDE.md)

- `alphaWeight_vertex` conclusion `alphaWeight (mk []) = 1` does NOT
  appear as a hypothesis (theorem has no hypotheses besides
  `tau_values` which is a separate combined fact).
- Proof is NOT `exact h`, `:= h_something`, or `:= id` — it unfolds
  the definition, applies (301d), and discharges via `norm_num`.
- No `h_<name>` patterns introduced.

### Definition smuggling check

- `alphaWeight` ≠ `RootedTree.theta` (cycle 249's identically-1 weight).
- `alphaWeight` ≠ `1/γ(t)` (the order condition / proof-of-311D θ).
- `alphaWeight` IS Butcher's (302a) closed form.

### Hypothesis strength check

- No hypotheses on the definition or base case beyond the implicit
  positivity of σ, γ that holds automatically in `ℝ` from `ℕ` coercion
  (and avoids the division-by-zero pathology only because we ship with
  `1!/(1·1) = 1`, where σ, γ are positive). No extra hypotheses
  introduced.

## Dead ends

None pursued. Caught the strategy's `α := 1/γ` smuggling on first
read of the entity JSON's variable list and `extraction/raw_text/ch03.txt`,
before any Lean code was written for the wrong definition.

The strategy's Phase A target (`RootedTree.order`) was already shipped
in Section310.lean at line 98 — confirmed in Priority 1 step #1, no
duplicate definition attempted.

## Discovery

1. **Butcher's α(t) lives in §302, not §312.** The cycle 250 strategy
   misattributed it to §312 (where Φ-weights are defined). §312
   introduces `RKTableau.elementaryWeight Φ(t)` (the Runge–Kutta
   approximation analogue), which is distinct from §302's α(t) (the
   exact-solution Taylor coefficient). The `1/γ(t)` expression that
   does appear in §312 (line 1827) is the **order condition**
   `Φ(t) = 1/γ(t)` linking the two — not a definition of either α or Φ.

2. **Section310 cannot host α(t).** `density` and `symmetry` live in
   Section301, and Section301 imports Section310 — not the other
   direction. The strategy's "insert in Section310.lean (near line
   230)" placement is impossible. Section301 is the correct home.

3. **Strategy's "scaffold for lem:310B" framing is incorrect.** The
   `lem_310B.json` `dependencies` list shows `thm:306A` and `def:310A`;
   `lem:310B`'s statement uses `θ(t)` and `σ(t)`, not `α(t)`. α(t)
   shows up as a tabulated value in §310 Table 310(II) but is not
   referenced in any of `lem:310B`'s textbook statement, proof, or
   dependencies. This is worth recording for the planner: future
   "α(t) for lem:310B" framings should be rejected.

4. **Faithfulness convention is reusable.** Cycle 017's σ-divergence
   pattern (define via closed form, defer combinatorial equivalence)
   transfers cleanly to α — no new project policy needed.

## Suggested next approach

For cycle 251, several candidates with declining priority:

1. **Begin `lem:310B` proper.** Now that θ(t), σ(t), γ(t), r(t), and α(t)
   are all defined, the Butcher §310 weight formula
   `Σ_t (h^r(t) / σ(t)) · θ(t) · F(t)(y_0)` is the obvious next target.
   This requires (a) a tree-indexed sum infrastructure
   (`∑ t : RootedTree, …` is not directly meaningful — `RootedTree` is
   infinite), (b) the use of `iteratedFDeriv` for `F(t)`. Item (a) is
   the bigger lift; it likely requires a finitary truncation by order
   `r(t) ≤ N`, which composes with cycle 250's `alphaWeight`.

2. **Prove `alphaWeight_pos`.** Stretch goal from the strategy. Needs
   `density_pos` and `symmetry_pos` lemmas (Section323 already has
   `order_pos`). One small cycle.

3. **Prove the textbook equivalence for `alphaWeight`.** That is, build
   the labelling-count combinatorial definition and prove it equals the
   closed form (302a). Multi-cycle; same scope as the deferred
   symmetry-group equivalence (see
   `.prover-state/issues/symmetry_group_equivalence.md`). Probably
   defer indefinitely.

4. **Compute `Φ` values on `explicitEuler` for `cherry`/`broom₃`.**
   Section312 already verified `Φ(τ) = 1`. Extending to higher-order
   trees would test the §312 recursive machinery against Butcher's
   Table 312(I) values. Low risk, medium value.

Cycle 251 planner should pick (1) only after auditing what
tree-indexed-sum infrastructure (finitary or otherwise) already exists
in Section383 / `bcoeff` definitions. (2) and (4) are reasonable
fallbacks if (1) is too ambitious.
