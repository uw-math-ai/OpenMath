# Cycle 048 Results

## Worked on
`sum_theta_psi_contraction` — abstract Σ θψ contraction inequality
inserted in `OpenMath/Chapter4/Section404.lean` immediately before the
`thm:406D` scaffold (`LinearMultistepMethod.stable_consistent_isConvergent`).

This is the first of the three sub-lemmas listed in cycle 047's
"Suggested next approach", and is consumed by the cycle 050 outer
assembly that dispatches the scaffold's remaining `sorry`.

## Approach
Followed the strategy's proof outline exactly:

1. `Finset.abs_sum_le_sum_abs` to push absolute value inside the sum.
2. `abs_mul` + two `mul_le_mul_of_nonneg_*` rewrites to bound each
   `|θ (idx i) * ψ i|` by `Θ * (C·h·Sε i + D·h²)` using `hθ` and `hψ`.
3. `Finset.sum_le_sum` to lift the pointwise bound to a sum bound.
4. `simp_rw` of the algebraic identity
   `Θ * (C·h·Sε i + D·h²) = Θ·C·h·Sε i + Θ·D·h²` to split the sum.
5. `Finset.sum_add_distrib` + `← Finset.mul_sum` + `Finset.sum_const` +
   `Nat.card_Ico` + `nsmul_eq_mul` to collapse the `Σ Θ·D·h²` summand
   to `Θ·D·h² · ((n - k : ℕ) : ℝ)`.
6. `apply le_of_eq; ring` closes the trailing `≤` whose two sides are
   already equal up to commutativity.

The strategy's draft ended with `ring`, but `ring` does not close `≤`
goals (only `=`), so swapped to `apply le_of_eq; ring`. No other
deviation from the strategy.

The two `_hh` and `_hkn` parameters were kept in the signature
(prefixed with `_` to silence the unused-variable linter) because
downstream consumers of this lemma will likely have those facts in
scope and naming them in the API shape stabilises the call sites in
cycle 050.

## Result
SUCCESS.

* `lake env lean OpenMath/Chapter4/Section404.lean` compiles cleanly,
  with only the same three pre-existing unused-variable warnings
  (lines 568, 627, 1204) and the cycle 047 scaffold's documented
  `sorry` warning at the `thm:406D` body (now line 1823 — shifted by
  the new lemma's insertion).
* `#print axioms` for `sum_theta_psi_contraction` shows
  `[propext, Classical.choice, Quot.sound]` — the standard Lean
  axioms, no `sorryAx`.
* Sorry count check: only one true `sorry` remains in the codebase
  (`OpenMath/Chapter4/Section404.lean:1823`, the cycle 047 scaffold).
  Two further `grep` hits at lines 548 and 1816 are inside doc-strings
  and not Lean tokens. Net sorry count unchanged: 1 → 1, as required.

## Faithfulness check
For each new `def` or `theorem` introduced this cycle:

- **`sum_theta_psi_contraction`** — *not a Butcher entity*; this is
  internal infrastructure (private lemma) on the path to closing
  `thm:406D`. It encodes one half of Butcher's algebraic step in the
  (406h) recurrence derivation: the contraction
  `|Σ_{i=k}^{n-1} θ_{idx i} · ψ_i| ≤ Θ · (C·h·Σ Sε + D·h²·(n-k))`
  given pointwise `|θ| ≤ Θ` and `|ψ_i| ≤ C·h·Sε_i + D·h²`.

  - Lean statement captures: same content as the textbook step
    (Butcher §406D, p. 347, between equations (406g) and (406h)), but
    parametrised over an abstract index function `idx : ℕ → ℕ` and an
    abstract per-index majoriser `Sε : ℕ → ℝ`. This abstraction does
    *not* weaken the inequality — it factors out two pieces of
    bookkeeping (Butcher's specific `θ_{n-1-i}` indexing, and
    Butcher's specific `Sε i := max_{j<k} |ε(i-j-1)|`) so the lemma
    can be reused both for the (406h) derivation and for any
    related contraction in the same shape.

  - Justification for the abstraction:
    * The cycle 050 outer assembly will instantiate `idx` to
      `fun i => n - 1 - i` and `Sε` to either the per-index `Mmax`
      bound from cycle 045 or a tighter "max of recent errors"
      term. Keeping both abstract avoids fighting `Nat`-subtraction
      and `Finset.sup'` API inside this lemma — both deferred to
      consumer call sites where the concrete shape is known.
    * The hypotheses `hθ`, `hψ`, `hΘ`, `hh`, `hkn` are exactly the
      ones Butcher has at this step in his proof (Θ ≥ 0, h ≥ 0,
      uniform θ-bound, per-index ψ-bound, sum range `Ico k n`). No
      hypothesis is *stronger* than Butcher's at this step. The
      `_hh : 0 ≤ h` and `_hkn : k ≤ n` are not consumed inside this
      lemma — they're passed through to make the API stable for
      cycle 050. They are *not* mathematically necessary for this
      contraction (the inequality holds for arbitrary `h, k, n`),
      but every realistic caller will have them in scope, so leaving
      them in the signature avoids a pointless plumbing change at
      the call site.
    * **Tautology check**: the conclusion is a non-trivial bound
      `|Σ θψ| ≤ Θ·C·h·Σ Sε + Θ·D·h²·(n-k)` that does not appear
      verbatim in any hypothesis. Pass.
    * **Identity check**: the proof is a 5-step calc, not `exact h`.
      Pass.
    * **Hypothesis strength check**: as above, `_hh` and `_hkn` are
      *not used internally* — they could be dropped. Documented
      here (and prefixed with `_` so the linter is silent).
    * **Definition smuggling check**: not applicable (no new
      `def`/`structure`/`class`).
    * **Absent theorem check**: no comment promises content not in
      the file.

## Dead ends
The strategy's draft proof ended with `ring`, but `ring` only closes
`=` goals, not `≤`. The build error printed both sides identical, so
swapping `ring` for `apply le_of_eq; ring` resolved it cleanly.
Recorded here for future cyclers: a `simp_rw [hpoint]` followed by
algebraic rewrites can leave a trailing `lhs ≤ rhs` where lhs and rhs
are syntactically equal up to commutativity — the canonical closer is
`apply le_of_eq; ring`, not `ring` alone.

## Discovery
Two minor:

1. The `_`-prefix-on-unused-hypothesis convention silences the
   unused-variable linter without changing the lemma's API shape.
   This keeps signatures stable across cycles even when the proof
   doesn't yet need every hypothesis. Useful for staged work where
   cycles 048/049/050 all touch the same plumbing.

2. The Mathlib spelling that this file already uses heavily —
   `Finset.sum_add_distrib`, `← Finset.mul_sum`, `Finset.sum_const`,
   `Nat.card_Ico`, `nsmul_eq_mul`, `Finset.abs_sum_le_sum_abs` — is a
   self-contained "contraction toolkit" for this shape of bound.
   Cycles 044/045/046 used the same toolkit; cycle 048 confirms it
   for one more shape. This catalogue should make cycle 050's outer
   assembly significantly faster.

## Suggested next approach
**Cycle 049 (φ(h) → 0 helper).** From `IsConvergent`'s starting-method
hypothesis (`∀ i, Tendsto (fun h => start h i) (nhds 0) (nhds y₀)`),
plus continuity of `yex` at `x₀`, conclude
`Tendsto (fun h => max_{i < k} |yex(x₀ + i·h) - start h i|) (nhds 0)
 (nhds 0)`.

Pure `Filter.Tendsto` analysis with no LMM-specific content.
Recommended steps:
1. Show `Tendsto (fun h => yex (x₀ + i·h)) (nhds 0) (nhds y₀)` for each
   `i < k` from continuity of `yex` at `x₀` (textbook hypothesis).
2. Combine with `Tendsto (fun h => start h i) (nhds 0) (nhds y₀)` to
   get `Tendsto (fun h => yex (x₀ + i·h) - start h i) (nhds 0) (nhds 0)`
   for each `i`.
3. Use `Filter.Tendsto.abs` to lift to `|·|`.
4. Use `Finset.sup'_tendsto` (or hand-roll a finite max via induction
   on `k`) to combine the per-index limits into a single max.

Then the **stretch goal from this cycle** (`abs_max_le_sum_in_Fin_k`)
is the bridge from "max form" to "sum form" of φ(h) → 0 — useful in
the cycle 050 outer assembly.

**Cycle 050 (outer assembly, dispatching the `thm:406D` scaffold).**
Chain:
- cycle 045 (per-step ψ bound `globalError_recurrence_bound_textbook`)
  → produces the `hψ` hypothesis with `Sε i := Mmax · 1` (uniform
  bound) or the tighter "max of recent ε" form,
- cycle 048 (`sum_theta_psi_contraction`, this cycle) → contracts the
  `Σ θψ` part of the global error decomposition,
- cycle 046 (`discrete_gronwall_exp_bound`) → yields the closed-form
  exponential bound on `|ε_n|`,
- cycle 049 (φ(h) → 0) + `Real.exp_nonneg` → drives the limit through
  `Tendsto.mul_zero` / `Tendsto.add_zero`.

Outer assembly should be ~50 lines of plumbing once all four pieces
are in place. The biggest risk is matching `idx` and `Sε` up correctly
between cycle 048 (this cycle) and cycle 045's per-step bound shape;
recommend the planner audit cycle 045's exact `ψ`-bound shape before
the cycle 050 worker starts.

The cycle 048 stretch goal (`abs_max_le_sum_in_Fin_k`) was *not*
attempted this cycle — primary lemma was chosen as the only
deliverable to keep the cycle low-risk. Cycle 049 (or its planner)
can pick it up if needed.
