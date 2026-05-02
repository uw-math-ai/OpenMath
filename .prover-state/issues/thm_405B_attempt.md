# Issue: thm:405B (convergent ⇒ preconsistent) closing strategy

## Status (cycle 069) — CLOSED

`thm:405B` (`convergent_isPreconsistent`) was **closed** in cycle 069
via the `homogeneousFromOnes` strong-recursion helper plus the
trivial-IVP argument. The `thm:243A` iff packager
`isConvergent_iff_isStable_and_isConsistent` is wired up against
cycle 068's `stable_consistent_isConvergent` (forward) and the
three `convergent_*` lemmas (reverse); two of the latter
(`thm:405A`, `thm:405C`) remain as sorry-first scaffolds for cycles
070/071.

The notes below documented the closing strategy *before* the proof
landed; they are retained as reference for the analogous cycle 070
work on `thm:405A` and the cycle 071 work on `thm:405C`.

## Context

`IsConvergent` (the strengthened cycle 068 version, see
`is_convergent_strengthened.md`) takes the form

```
∀ f, Continuous (uncurry f) →
∀ L, LipschitzWith L (uncurry f) →
∀ x₀ y₀ yex, yex x₀ = y₀ → ContDiff ℝ 1 yex →
  (∀ x, HasDerivAt yex (f x (yex x)) x) →
∀ M_bound, 0 ≤ M_bound → (∀ t, |f t (yex t)| ≤ M_bound) →
∀ start, (∀ i, Tendsto (start · i) (𝓝 0) (𝓝 y₀)) →
∀ x, x₀ < x →
∀ Y, (∀ m > 0, (∀ i, Y m i.val = start (h_m) i) ∧ M.IsLMMSolution h_m x₀ f (Y m)) →
  Tendsto (fun m => Y m m - yex x) atTop (𝓝 0)
```

To close `convergent_isPreconsistent` from `hConv : M.IsConvergent`,
the textbook strategy (Butcher §405) instantiates the IVP
`y' = 0`, `y(0) = 1`, `x = 1` with `start h _ := 1`, then constructs
the homogeneous-recurrence solution `η : ℕ → ℝ` with `η_0 = ⋯ = η_{k-1} = 1`
and `η_{n+k} = Σ_{i=1}^{k} α_i η_{n+k-i}` for `n ≥ 0`. Setting
`Y m n := η n` (constant in `m`) gives an LMM solution of the
trivial IVP, so `hConv` yields `η m → 1` as `m → ∞`. Taking limits
in the recurrence at large `n` then forces `1 = Σ_{i=1}^{k} α_i`,
i.e. `M.IsPreconsistent`.

## Lean obstructions

### Obstruction 1: constructing `η`

The canonical homogeneous extension of the all-ones starting
sequence requires *strong recursion* on `ℕ` because the recurrence
references `η (n - 1), …, η (n - k)`. Two viable encodings:

1. `Nat.strongRecOn` — works but produces `motive`/`IH`-laden goals.
2. Direct recursion with `termination_by` and `decreasing_by` —
   cleaner but requires explicit `omega` discharge of
   `n - (j.val + 1) < n` in the recursive call.

The recursion below should compile but has not been validated this
cycle:

```lean
noncomputable def LinearMultistepMethod.homogeneousFromOnes
    {k : ℕ} (M : LinearMultistepMethod k) (k_pos : 0 < k) : ℕ → ℝ
  | n => if h : n < k then 1
         else
           ∑ j : Fin k,
             M.α j.succ *
               LinearMultistepMethod.homogeneousFromOnes M k_pos
                 (n - (j.val + 1))
  termination_by n => n
  decreasing_by
    simp_wf
    have hm : k ≤ n := Nat.not_lt.mp h
    have hj : j.val < k := j.isLt
    omega
```

### Obstruction 2: discharging `IsLMMSolution` for `η`

Once `η` is defined, we need to show `M.IsLMMSolution h_m 0 (fun _ _ => 0) (fun n => η n)`.
By `isLMMSolution_zero_iff` (Section404), this reduces to
`M.IsHomogeneousSolution η`, i.e.

```
∀ m, η (m + k) = ∑ j : Fin k, M.α j.succ * η (m + k - (j.val + 1)).
```

This holds *by definition* once `m + k ≥ k`, which is automatic.
The case-split unfolds the `if h : n < k` branch; with `n := m + k`
and `k_pos`, we have `¬ (m + k < k)` so the recurrence branch fires.

### Obstruction 3: discharging the convergence hypotheses

The 8 named hypotheses for `hConv` are mostly trivial (`continuous_const`,
`LipschitzWith.const`, `contDiff_const`, `hasDerivAt_const`, `abs_zero`,
`tendsto_const_nhds`, etc.). The only fiddly one is

```
Continuous (Function.uncurry (fun (_ _ : ℝ) => (0 : ℝ)))
```

which equals `continuous_const` after `simp [Function.uncurry]`.

### Obstruction 4: limit-of-recurrence argument

After `hConv` yields `Tendsto (fun m => η m - 1) atTop (𝓝 0)`,
we have `η m → 1`. Then

```
η (m + k) = ∑ j : Fin k, M.α j.succ * η (m + k - (j.val + 1))
```

Take `m → ∞`. For each `j`, `η (m + k - (j.val + 1)) → 1` (shifted
limit). The RHS tends to `(∑ M.α j.succ) · 1 = Σ M.α j.succ`. The
LHS tends to `1`. Hence `1 = Σ M.α j.succ`, i.e. preconsistency.

In Lean, this requires:
- `Filter.Tendsto.comp` with the shift `m ↦ m + k - (j.val + 1)`
  (or `m ↦ m + k`).
- `Tendsto.const_mul` and `Finset.tendsto_sum` to lift to the sum.
- `Filter.tendsto_nhds_unique` to extract `1 = Σ M.α j.succ`.

## Recommendation for next cycle

**If continuing on `thm:405B`:** add the helper
`LinearMultistepMethod.homogeneousFromOnes` as a sibling lemma in
`Section404.lean` (or in `Section405.lean` if it stays self-contained),
prove the two characterising lemmas
(`homogeneousFromOnes_lt_k_eq_one`, `homogeneousFromOnes_recurrence`),
then close `convergent_isPreconsistent` via the limit-of-recurrence
argument above. Estimated 1.5–2 cycles.

**If skipping to `thm:405A` first:** the textbook's proof of
`thm:405B` cites `thm:405A`, but in our formalisation we do **not**
need `IsStable` to derive `IsPreconsistent` — the limit argument
goes through directly because `η m → 1` is given by `hConv`, not
derived from boundedness. (Butcher's appeal to stability is to
ensure η stays bounded so the ε-argument in the textbook works.
The Lean proof can sidestep this.)

## Cycle 069 deliverable bar (per planner)

The cycle deliverable per the planner is the scaffold + iff
packager + Priority 0 cleanup, all of which are done. The
`thm:405B` closing is bonus and is deferred to cycle 070 per the
backup plan.
