# Cycle 035 Results

## Worked on

`def:404A` — **preconsistent linear multistep method** (Butcher §404,
p. 341). Opens Chapter 4 of the formalization (previously 0/27).

New file: `OpenMath/Chapter4/Section404.lean` containing
- `LinearMultistepMethod k` (the `k`-step LMM coefficient record),
- `LinearMultistepMethod.IsPreconsistent` predicate (Butcher 404a),
- `explicitEulerLMM` (1-step LMM witness) + preconsistency proof,
- `implicitEulerLMM` (1-step LMM witness) + preconsistency proof.

Plumbing: `OpenMath/Chapter4.lean` (chapter aggregator) and
`import OpenMath.Chapter4` added to `OpenMath.lean`.

## Approach

- Read `entities/def_404A.json` (`dependencies = []`,
  `transitive_dependencies = []`) to confirm `def:404A` is
  self-contained — no Chapter 1–3 prerequisites needed.
- Created the LMM structure as recommended by the planner:
  `α, β : Fin (k+1) → ℝ` with `α 0 = -1` as a *hypothesis*
  (textbook normalisation).
- Encoded preconsistency (404a) `1 = α₁ + … + α_k` as
  `1 = ∑ i : Fin k, M.α i.succ` so the `α 0` slot is skipped.
- Provided two concrete instances (CLAUDE.md non-vacuity rule):
  explicit Euler (β: 0,1) and implicit Euler (β: 1,0). Both close
  preconsistency with a single `simp` call.

## Aristotle usage

**Skipped this cycle** per planner instructions. Justification: the
two new theorems (`explicitEulerLMM_isPreconsistent`,
`implicitEulerLMM_isPreconsistent`) are trivial unfolding plus
`Fin (1+1)` arithmetic. CLAUDE.md's "Aristotle-first" rule is
explicitly conditioned on having ~5 sub-lemmas worth submitting;
here there were zero. A 30-minute round-trip would have inflated
cycle wall-clock for a goal that `simp` closed in <1s.

## Result

**SUCCESS.**

- `lake env lean OpenMath/Chapter4/Section404.lean` — clean compile
  (no warnings, no errors). After removing the initially-flagged
  unused-simp-arg `Fin.sum_univ_one`, output is empty.
- `lake build OpenMath.Chapter4.Section404` — built (518s; first
  build of a Chapter 4 file).
- `lake build` (full) — succeeded (8054 jobs;
  `OpenMath.Chapter4` built in 325s, `OpenMath` aggregator in 303s).
- Axiom check on both witnesses:
  ```
  'OpenMath.Chapter4.Section404.explicitEulerLMM_isPreconsistent'
    depends on axioms: [propext, Classical.choice, Quot.sound]
  'OpenMath.Chapter4.Section404.implicitEulerLMM_isPreconsistent'
    depends on axioms: [propext, Classical.choice, Quot.sound]
  ```
  Standard Lean 4 axioms only — no `sorry`, no `axiom`/`constant`.

## Faithfulness check

### `LinearMultistepMethod` (structure)

- Entity ID and textbook statement (quoted from
  `entities/def_404A.json` `context_latex`):
  > Linear multistep methods for the ODE $y' = f(x,y)$ are defined
  > by coefficients $\alpha_i$ and $\beta_i$. For a $k$-step method
  > with step size $h$, the numerical approximation $y_n$ satisfies
  > $\sum_{i=0}^k \alpha_i y_{n-i} = h \sum_{i=0}^k \beta_i
  >  f(x_{n-i}, y_{n-i})$, with $\alpha_0 = -1$.
- Lean structure captures: **same content** — coefficients
  `α, β : Fin (k+1) → ℝ` and the textbook normalisation
  `α 0 = -1` as a structure field.
- Definition smuggling check: the only `Prop` field, `α_zero`, is a
  *hypothesis* (the textbook normalisation convention every concrete
  LMM must supply), not a smuggled conclusion. Documented as such
  in the docstring.
- We do not yet encode the recurrence operator itself — only the
  coefficient data. This is faithful to Butcher's setup-then-define
  prose: the recurrence is in the section context, but the
  `LinearMultistepMethod` *coefficient record* is what `def:404A`
  and downstream definitions (404B, 405B, …) actually quantify over.
  The recurrence operator can be added later when a downstream
  entity (`def:402A` convergence, `def:406A` LTE) needs it.

### `LinearMultistepMethod.IsPreconsistent` (definition)

- Entity ID and textbook statement (quoted from
  `entities/def_404A.json`):
  > A linear multistep method satisfying (404a) is said to be
  > 'preconsistent'.

  with (404a) being `1 = α₁ + α₂ + ⋯ + α_k`.
- Lean predicate captures: **same content** —
  `1 = ∑ i : Fin k, M.α i.succ` is exactly the sum
  `α₁ + α₂ + ⋯ + α_k` (using `i.succ : Fin (k+1)` to skip `α 0`).
- Definition smuggling check: `IsPreconsistent` is the algebraic
  condition (404a) directly. This **matches** Butcher's *definition*
  (the textbook says "a linear multistep method satisfying (404a)
  is said to be preconsistent"), so (404a) IS the definition — not
  a characterisation theorem masquerading as a definition.

### `explicitEulerLMM` / `implicitEulerLMM` (witnesses)

- Entity-derived statement: explicit Euler is
  `y_n - y_{n-1} = h · f(x_{n-1}, y_{n-1})`, equivalently
  `α 0 = -1, α 1 = 1, β 0 = 0, β 1 = 1`. Implicit Euler swaps
  β to `(1, 0)`.
- Lean records capture: **same content**. Encoded via
  `if i = 0 then -1 else 1` etc. on `Fin (1+1)`.
- Tautology check: each witness is a concrete data record, not a
  theorem. Their preconsistency proofs evaluate the `Fin 1` sum
  via `simp` unfolding plus arithmetic — the proof terms are NOT
  identity / hypothesis-rename.
- Hypothesis strength check: no extra hypotheses; the structure
  fields are only the textbook coefficients and the textbook
  normalisation.

### Tautology / identity / hypothesis-strength sweep

- `explicitEulerLMM_isPreconsistent` / `implicitEulerLMM_isPreconsistent`:
  conclusion is `M.IsPreconsistent`, no hypotheses to compare against
  (aside from the structure fields baked into the definitions).
  Tautology check: trivially clean.
- Identity check: proofs are `simp [...]`, not `:= h_xxx` or
  `:= id`. They genuinely evaluate `1 = ∑ i : Fin 1, …` to `1 = 1`.

## Dead ends

None this cycle. The planner pre-checked `lean_local_search
"LinearMultistep"` and confirmed Mathlib has no LMM scaffolding to
reuse. The proof script `simp [..., Fin.sum_univ_one]` initially
flagged `Fin.sum_univ_one` as unused (simp's normalisation of
`Fin (1+1)` already evaluates the sum without it); dropping the
hint silenced the linter and the proofs still close.

## Discovery

1. **`Fin (1+1)` sums normalise via `simp` alone.** For 1-step LMM
   witnesses, `simp [LinearMultistepMethod.IsPreconsistent,
   <method>]` is enough — no need for `Fin.sum_univ_one` /
   `Fin.sum_univ_succ` lemmas. This will also work for the upcoming
   `def:404B` consistency witness on the same Euler instances.

2. **Ordering of `if i = 0 then …` works on `Fin (k+1)`.** The
   coercion `(0 : Fin (k+1))` and decidable equality on `Fin` make
   the boolean encoding trivial; `α_zero` closes by `simp` against
   the if-then-else.

3. **Cold-build wall-clock for a single Mathlib-importing Chapter 4
   file is ~9 min** on this cluster. Subsequent Chapter 4 files will
   reuse the cached Mathlib oleans; expect <30 s incremental.

## Suggested next approach

The natural follow-up is `def:404B` (consistency, equation (404b))
since the LMM structure is now in place. (404b) reads
`α_1 + 2α_2 + ⋯ + k α_k = β_0 + β_1 + ⋯ + β_k`, encodable as
`(∑ i : Fin k, (i.succ : ℝ) * M.α i.succ) = ∑ i, M.β i`.

Both Euler witnesses already trivially satisfy this:
- explicit Euler: LHS = `1 · 1 = 1`, RHS = `0 + 1 = 1`. ✓
- implicit Euler: LHS = `1`, RHS = `1 + 0 = 1`. ✓

So `def:404B` is also a one-cycle target with the same witness shape
and would unblock `def:402A` (convergent LMM), `def:403A`
(Dahlquist stability), and the deferred `thm:243A`. Recommended for
cycle 036.

After 404B, candidate ordering for the rest of §40:
- `def:402A` (convergent LMM) — needs the recurrence operator;
  moderate-sized cycle.
- `def:403A` (Dahlquist stability) — depends on the characteristic
  polynomial of the LMM; small structural cycle.
- `def:406A` (local truncation error) — depends on 404B.
