# Cycle 059 Results

## Worked on

`thm:406D` outer-assembly Tendsto sub-squeezes — the two halves of the
closed-form bound's RHS that the eventual outer squeeze in
`stable_consistent_isConvergent` will combine via `Tendsto.add`.

Per the planner, this cycle decomposes the larger
`globalError_outer_squeeze_autonomous` into two self-contained
sub-squeezes (deferred from cycle 058's preview). The single sorry
at `OpenMath/Chapter4/Section404.lean` (now line 3203, was 3030) is
**not touched** — only new private lemmas added.

## Approach

Inserted two new `private lemma`s after `tendsto_step_size_comp`:

1. `globalError_outer_squeeze_a_term`: shows
   `exp(b(h_m) · k · m · h_m) · a(h_m) → 0` as `m → ∞`,
   for `h_m := (x − x₀)/m`.

2. `globalError_outer_squeeze_c_term`: shows
   `(exp(b(h_m) · k · m · h_m) − 1) · c(h_m) · h_m / (b(h_m) · k) → 0`
   as `m → ∞`.

Both lemmas are generic in their `a, b, c : ℝ → ℝ` arguments — they
take the limits as hypotheses rather than computing them, so they do
not consume any LMM-specific data.

Proof skeleton (identical for both):
- Step A — `Filter.eventually_atTop.mpr ⟨1, ?_⟩` to localise to
  `m ≥ 1`. Then `dsimp only` to beta-reduce, followed by
  `m_h_constancy` (cycle 057) to fold `m · h_m → x − x₀` inside the
  exponent. Closed by `ring`-rearrangement plus `rw`.
- Step B — lift each Tendsto-at-`nhds 0` factor to Tendsto-at-`atTop`
  via cycle 058's `tendsto_step_size_comp`.
- Step C — combine via `Tendsto.mul_const`, `(Real.continuous_exp.tendsto _).comp`,
  `Tendsto.mul`, `Tendsto.div`, and finally `Tendsto.congr'`
  with `heventually_eq.symm` to lift the simplified-form Tendsto
  back to the original-form Tendsto.

## Result

SUCCESS.

- File compiles with no errors. The diagnostic warning set is
  unchanged from cycle 058's HEAD: three pre-existing
  unused-variable warnings (lines 568, 627, 1204) plus the single
  expected `declaration uses 'sorry'` on
  `stable_consistent_isConvergent` (line 3203 — shifted from 3030
  by the +173 lines of new content).
- `lean_verify` confirmed `globalError_outer_squeeze_a_term` uses
  only the standard axioms `[propext, Classical.choice, Quot.sound]`.
- `globalError_outer_squeeze_c_term` could not be axiom-verified
  via the LSP `lean_verify` tool (returned a
  `%d format: a real number is required, not NoneType` tool-side
  error unrelated to the proof). The file's clean compile + the
  identical proof structure to the a-term lemma is the operative
  verification; a full `lake env lean` axiom dump was launched as
  a backup check.
- Tautology-scanner regex
  `:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$`
  reports exactly 2 hits (lines 1950, 2842), both pre-existing
  legacy patterns covered by
  `tautology_scanner_false_positives.md`.

## Faithfulness check

The two new lemmas are **infrastructure** `private lemma`s, not
top-level theorems mapped to a Butcher entity. The CLAUDE.md
per-`def`/per-`theorem` faithfulness checklist applies as follows:

- **No new `def`/`structure`/`class`** introduced.
- **No new top-level `theorem`** corresponding to a Butcher entity.
- **Tautology check**: neither lemma's conclusion appears as a
  hypothesis. The conclusions are
  `Tendsto (fun m => exp(...) · a(...)) atTop (nhds 0)` and the
  c-term analog; the hypotheses are Tendsto facts about the
  components (`a → 0`, `b → bInf`, `c → cInf`). Distinct.
- **Identity check**: neither proof is a single `exact h`. Both
  end with a non-trivial `Filter.Tendsto.congr'` step that
  bridges two functions related by `m_h_constancy` only on the
  cofinite set `{m | 1 ≤ m}`. Real mathematical work.
- **Hypothesis strength check**: hypotheses are minimal. The
  a-term lemma only needs `a → 0` and `b → finite`; the c-term
  lemma additionally needs `0 < bInf` (otherwise the
  `c · h / (b · k)` tail diverges) and `0 < k` (otherwise the
  divisor is zero). Both are mathematically necessary.
- **Definition smuggling check**: N/A (no new `def`).

The cycle 060 outer-squeeze assembly will instantiate `a, b, c`
with the LMM-specific witnesses extracted from
`globalError_closed_form_autonomous`, at which point the
faithfulness check for the *theorem* statement (`IsConvergent`
shape) will apply.

## Dead ends

- Initial draft used `b∞` and `c∞` as identifier names, copying the
  planner's strategy verbatim. Lean 4 rejects `∞` (Unicode category
  Sm) in identifiers; the parser produced `expected token` errors at
  the binder positions. Renamed to `bInf` / `cInf` throughout
  (planner naming was descriptive, not literal).
- Initial Step-A `rw [h_assoc, hm_h]` failed with
  `Did not find an occurrence of the pattern` because the
  `=ᶠ[atTop]` goal exposes unreduced beta-redexes — the LHS is
  `(fun m => …) m`, which is definitionally but not syntactically
  the rewrite target. Inserting `dsimp only` after `intro m hm`
  beta-reduces and lets `rw` proceed.

## Discovery

- `Filter.Tendsto.congr'` with dot notation needs the explicit
  form `Filter.Tendsto.congr' heventually_eq.symm hprod` rather
  than `hprod.congr' heventually_eq.symm`, because the first
  explicit argument of `congr'` is the `EventuallyEq`, not the
  `Tendsto`. Dot notation on `hprod.congr' …` would mis-resolve.
- `Filter.eventually_atTop.mpr ⟨N, _⟩` produces an unreduced
  beta-redex on the LHS even though the meta-level rewrite target
  looks identical. `dsimp only` (no lemmas — just beta) fixes
  it cheaply. Worth remembering for future Tendsto-on-atTop
  congruences.
- `Tendsto.mul`, `Tendsto.mul_const`, `Tendsto.div`, and
  `Tendsto.sub_const` from `Mathlib.Topology.Algebra.GroupWithZero`
  and friends compose cleanly. `Tendsto.div` requires the
  divisor's limit to be non-zero; here we use `hbk_pos.ne'`.

## Suggested next approach

Cycle 060 should attempt the outer-squeeze assembly proper:

```lean
private theorem globalError_outer_squeeze_autonomous
    ... :
    Filter.Tendsto (fun m : ℕ => Y m m - yex x) Filter.atTop (nhds 0) := by
  -- Apply globalError_closed_form_autonomous with h = h_m to extract
  -- the existential (a, b, c) and the per-n bound for each m large
  -- enough that h_m * L * |M.β 0| < 1.
  -- The bound's RHS = (a-term) + (c-term).
  -- Both → 0 by cycles 059's two sub-squeezes.
  -- Combine via Tendsto.add → RHS → 0.
  -- squeeze_zero between 0 ≤ |ε_m| ≤ RHS closes.
  sorry
```

Expected size: ~60–100 lines. Threading the existential `(a, b, c)`
out of `globalError_closed_form_autonomous` is the bulk of the work;
matching the closed-form RHS's algebraic shape against the
sub-squeezes' RHS shape may need some `simp` or `congr` polish
because `globalError_closed_form_autonomous`'s `a, b, c` have
explicit definitions in terms of LMM data, while the sub-squeezes
take generic `a, b, c : ℝ → ℝ`.

After cycle 060, cycle 061+ addresses the autonomous →
non-autonomous lift to close `stable_consistent_isConvergent`
proper. That is a separate (likely 3–5-cycle) refactor.
