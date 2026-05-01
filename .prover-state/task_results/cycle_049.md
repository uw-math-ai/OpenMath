# Cycle 049 Results

## Worked on

Internal infrastructure for the `thm:406D` (`stable_consistent_isConvergent`)
scaffold body — the φ(h) → 0 helper that the cycle 050 outer assembly will
consume. Per planner strategy, the cycle's primary deliverable was the
per-index lemma `starting_error_each_tendsto_zero` and its stretch sum form
`starting_error_sum_tendsto_zero`. Both shipped, axiom-clean.

Sorry count unchanged at 1 (the documented `sorry` at
`OpenMath/Chapter4/Section404.lean:1898` — the cycle 047 thm:406D scaffold).

## Approach

Followed planner strategy verbatim:

1. **Per-index lemma**: signature mirrors `IsConvergent` (line 305) line-for-line
   — `(hyex_diff : ∀ x ≥ x₀, HasDerivAt yex (f x (yex x)) x)` and
   `(hstart : ∀ i, Tendsto (fun h => start h i) (nhds 0) (nhds y₀))` — so cycle
   050 can destructure `IsConvergent`'s hypotheses and feed them in unchanged.
   Proof in 5 steps:
   - `(hyex_diff x₀ le_rfl).continuousAt` ⇒ `ContinuousAt yex x₀`
   - `tendsto_const_nhds.add (tendsto_const_nhds.mul Filter.tendsto_id)` ⇒
     `h ↦ x₀ + i·h → x₀` (rewriting `x₀ + i·0` → `x₀` via `simpa`)
   - Compose with `ContinuousAt.tendsto` ⇒ `yex(x₀ + i·h) → yex x₀ = y₀`
     (collapse with `simpa [hy0]`)
   - `Filter.Tendsto.sub` against `hstart i` ⇒
     `yex(x₀ + i·h) - start h i → 0`
   - `Filter.Tendsto.abs` ⇒ `|yex(x₀ + i·h) - start h i| → 0`

2. **Sum form**: `tendsto_finset_sum (Finset.univ : Finset (Fin k))` with the
   per-index lemma supplied for each `i`. The target `∑ _i, 0 = 0` collapses
   via `simpa`.

3. **No Aristotle this cycle** (per strategy). The lemmas were ~25 + ~10 lines;
   manual proof was faster than the 30-min Aristotle round-trip, and Aristotle
   compute is reserved for cycle 050's larger outer assembly.

## Result

SUCCESS — both lemmas compile, no errors, no `sorry` introduced.

`lake env lean OpenMath/Chapter4/Section404.lean` produces only the previously
documented warnings:

* `Section404.lean:568` `unused variable hM` (pre-existing, cycle 044)
* `Section404.lean:627` `unused variable hh` (pre-existing, cycle 044)
* `Section404.lean:1204` `unused variable hMmax0` (pre-existing, cycle 045)
* `Section404.lean:1898` `declaration uses sorry` (cycle 047 scaffold,
  unchanged)

In-place axiom check (`#print axioms` for both lemmas, then reverted):

```
'_private.OpenMath.Chapter4.Section404.0.OpenMath.Chapter4.Section404.starting_error_each_tendsto_zero'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.OpenMath.Chapter4.Section404.0.OpenMath.Chapter4.Section404.starting_error_sum_tendsto_zero'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

Both axiom-clean (no `sorryAx`). Sorry count: still exactly 1, at line 1898.

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `starting_error_each_tendsto_zero` (private lemma)

* Entity ID: not a Butcher entity. Internal infrastructure for `thm:406D`'s
  φ(h) → 0 step.

* Textbook context (quoted from `entities/thm_406D.json`, `proof_text`):
  > "where ζᵢ, for i = 0, 1, …, k-1, are linear combinations of the errors in
  > yᵢ and tend to zero as h → 0."

  Butcher's `ζᵢ` (denoted `ζ_i` in the LaTeX) is the per-index "starting error"
  — the gap between `yᵢ` (the starting-method output) and `y(xᵢ) = yex(x₀ + ih)`
  (the exact solution at the `i`-th node). Our `|yex(x₀ + i·h) - start h i|`
  is exactly `|ζᵢ(h)|`. The lemma proves Butcher's claim "tend to zero as h → 0"
  for each index.

* Lean statement captures: same content (per-index variant of Butcher's claim).

* Tautology check: PASS — conclusion `Tendsto … (nhds 0) (nhds 0)` is not in
  any hypothesis.

* Identity check: PASS — 5-step proof composing 4 distinct Mathlib facts; not
  vacuous.

* Hypothesis-strength check: `hyex_diff` (`∀ x ≥ x₀, HasDerivAt yex …`) is
  stronger than strictly necessary — the proof only uses the `x = x₀` instance.
  Documented in the lemma's docstring as intentional: matches the
  `IsConvergent` predicate's hypothesis shape (line 313) so cycle 050 can feed
  it unchanged. Weakening would force an adapter at the call site.

### `starting_error_sum_tendsto_zero` (private lemma)

* Entity ID: not a Butcher entity. Internal infrastructure.

* Textbook context (quoted from `entities/thm_406D.json`, `proof_latex`):
  > "‖ε_n‖ ≤ Θ ∑_{i=0}^{k-1} ‖ζ_i‖ + Θ C h k ∑_{i=k}^{n-1} ‖ε_i‖
  >       + Θ D (n-k) h²"
  > … "We rewrite (406g) in the form
  >   ‖ε_n‖ ≤ φ(h) + Θ C h k ∑_{i=1}^{n-1} ‖ε_i‖ + Θ D n h²,
  > where φ(h) takes positive values and will converge to zero as h → 0."

  Butcher's `φ(h)` is `Θ ∑_{i=0}^{k-1} ‖ζ_i‖`. Up to the `Θ` constant
  (which the cycle 050 outer assembly will multiply in separately), our
  `∑ i : Fin k, |yex(x₀ + i·h) - start h i|` equals `∑_{i=0}^{k-1} ‖ζ_i‖`.
  The sum form proves Butcher's "φ(h) … will converge to zero as h → 0" claim.

* Lean statement captures: same content (sum form of Butcher's φ(h) → 0
  claim).

* Tautology, identity, hypothesis-strength checks: same as the per-index
  lemma. The hypothesis-strength comment about `hyex_diff` carries over —
  this lemma is just a `tendsto_finset_sum` lift of the per-index version,
  using the same hypothesis shape for the same reason.

* Class/structure check: N/A — no new `class` or `structure`.

* Definition-smuggling check: N/A — no new `def`.

* Absent-theorem check: PASS — both lemmas are present and proved.

## Dead ends

None significant. One minor name correction during proof writing:
`tendsto_id` does not exist in the global namespace; the correct name is
`Filter.tendsto_id` (signature `∀ {x : Filter α}, Filter.Tendsto id x x`).
Caught immediately by `lean_diagnostic_messages`; one-line fix.

The strategy's draft proof anticipated this drift in its "may need …" notes
(see strategy's "Mathlib lemmas" table caveat). Confirmed via `lean_multi_attempt`
of `#check @Filter.tendsto_id` before patching.

## Discovery

* `tendsto_finset_sum` lives outside the `Topology/Algebra/Group/Basic` /
  `InfiniteSum/Basic` files the strategy guessed — it's not even
  declared in `Mathlib/Topology/Algebra/`. Searching by usage rather than
  declaration site located it (`grep -l tendsto_finset_sum`). Its true
  declaration site is somewhere reachable transitively via `import Mathlib`
  (the file uses the bulk import); locating the exact home file is
  unimportant since we already have full access via `import Mathlib`.
  Signature confirmed via `lean_multi_attempt #check @tendsto_finset_sum`:

  ```
  ∀ {ι α M} [TopologicalSpace M] [AddCommMonoid M] [ContinuousAdd M]
    {f : ι → α → M} {x : Filter α} {a : ι → M} (s : Finset ι),
    (∀ i ∈ s, Tendsto (f i) x (𝓝 (a i))) →
    Tendsto (fun b ↦ ∑ c ∈ s, f c b) x (𝓝 (∑ c ∈ s, a c))
  ```

  Useful for future cycles needing per-index → sum lifts.

* `(hyex_diff x₀ le_rfl).continuousAt` worked first try — no need for the
  `(le_refl x₀)` or `by linarith` fallbacks the strategy anticipated. The
  `≥`-introduction unifies cleanly with `le_rfl`.

* `simpa using h0` handled the `x₀ + i·0 = x₀` rewrite without explicit
  `mul_zero, add_zero` hints. `simpa using` for the `|0| = 0` collapse in the
  final `.abs` step likewise needed no `[abs_zero]` hint — `simpa` finds it.

* The sum form's target `∑ _i ∈ Finset.univ, (0 : ℝ) = 0` collapses via plain
  `simpa using h_sum`. No `Finset.sum_const_zero` hint needed; `simpa`'s
  default lemma set covers it.

## Suggested next approach

**Cycle 050 (the outer assembly for `thm:406D`)** is now unblocked on the
"φ(h) → 0" side. The four pieces are in place:

* Cycle 045: `globalError_recurrence_bound_textbook` (the (406c) per-step
  bound, line ~1331)
* Cycle 046: `discrete_gronwall_exp_bound` (the (406h) closed form)
* Cycle 048: `sum_theta_psi_contraction` (the Σ θψ contraction, line 1762)
* Cycle 049 (this cycle): `starting_error_each_tendsto_zero` and
  `starting_error_sum_tendsto_zero` (φ(h) → 0)

The cycle 050 planner should focus on **shape-matching** between cycles 045
and 048's `Sε`/`idx` signatures before writing the outer assembly:

1. Read cycle 045's exact ψ-bound shape (around line 1331). What is its
   `Sε`-shape (max over `Fin k`? Σ over `Ico (n-k) n`?).
2. Read cycle 048's `sum_theta_psi_contraction`'s `Sε` parameter.
3. Pick an `Sε` instantiation for the cycle 050 call to cycle 048 that
   matches cycle 045's output shape. If they don't align, derive a small
   adapter lemma (`Sε_max ≤ Sε_sum`-style) before the outer assembly.

The other open question is whether `thm:406D` needs `0 < k` (inherited from
`theta_isHomogeneousSolution` and `theta_bounded_of_isStable`). For a
`k = 0` LMM, the recurrence `Σ_{i=0}^0 αᵢ y_{n-i} = …` reduces to
`-y_n = h β₀ f(x_n, y_n)` (since `α₀ = -1`), which is a bizarre degenerate
case. Two options for cycle 050:

* **Push `0 < k` up to the theorem statement** (simplest, matches
  Butcher's implicit assumption that `k ≥ 1` for "linear *multistep*").
* **Handle `k = 0` separately** (more general but probably vacuous —
  there are no Butcher LMMs with `k = 0`).

The cycle 050 planner should pick one approach and document the choice in
the strategy file.

After `thm:406D` is closed, the natural next target is `thm:243A` (the
Ch.2 → Ch.4 cross-chapter deferral). Its `def:404B` dependency is already
in place from earlier cycles.
