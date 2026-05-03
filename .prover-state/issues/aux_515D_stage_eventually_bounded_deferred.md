# Issue: `aux_515D_stage_eventually_bounded` deferred — needs M-matrix-based eventual bound on `f ∘ Y_int n`

## Status (cycle 111) — RESOLVED

Closed cycle 111 in `OpenMath/Chapter5/Section515.lean` (the
`aux_515D_stage_eventually_bounded` private theorem).

**Approach used**: sum-norm self-bound, *not* M-matrix. The
M-matrix approach outlined below is mathematically valid but
heavy in Lean carpentry. Instead, summing the absolute-valued
stage equation over `i` gives a scalar self-bound
`Sₙ ≤ hₙ K Lr Sₙ + hₙ K s |f 0| + B_Uₙ` where `K := ∑_{i,j}|A_{ij}|`
(Frobenius L¹-norm of `A`) and `Sₙ := ∑ᵢ |Y_int n i|`. For `n` with
`hₙ K Lr < 1/2` (automatic from `hₙ → 0`), this gives
`Sₙ ≤ 2(hₙ K s |f 0| + B_Uₙ)`. Output convergence makes `B_Uₙ`
bounded, so `Sₙ` is eventually bounded; Lipschitz lifts to `f`.

**Key advantage**: no signature change needed. The helper still
takes the original cycle-110 hypotheses without an added Frobenius
norm hypothesis. Axioms verify clean (`[propext, Classical.choice,
Quot.sound]`).

**Sorry count delta**: 2 → 1 (only `aux_515D_output_tendsto` at
`Section515.lean:1504` remains).

**Faithfulness note**: this is a *strict simplification* over the
strategy's M-matrix recipe — no new hypothesis, no new helper, no
new external lemma. The textbook claim ("Y_int eventually bounded")
is captured by the conclusion. The bound constant
`Bf := Lr · 2(Δx K s |f 0| + B_Ulim + 1) + |f 0|` is explicit but
not tight; tightness is irrelevant since the conclusion is mere
existence. The M-matrix machinery in `OpenMath/Chapter5/MMatrix.lean`
remains in place for future use.

## Status (cycle 110) — OPEN (resolved cycle 111)

Cycle 110 closed `aux_515D_stage_tendsto` modulo this single helper
sorry. The stage-side limit argument now reduces to a clean
*eventual boundedness* claim on the values `f(Y_int n j)`. This is
deliberately separated from the limit-shuffling work so that the
(non-trivial) M-matrix rearrangement can be tackled in a focused
follow-up cycle.

## Blocker

The helper sorry sits at `OpenMath/Chapter5/Section515.lean` (the
new `private theorem aux_515D_stage_eventually_bounded` opened just
before `aux_515D_stage_tendsto`). Its statement:

```lean
private theorem aux_515D_stage_eventually_bounded {s r : ℕ}
    (M : GeneralLinearMethod s r)
    (_hStab : M.IsStable)
    {f : ℝ → ℝ} {L : NNReal} (_hf_lip : LipschitzWith L f)
    {x₀ y₀ : ℝ} {yex : ℝ → ℝ}
    (_hyex_x₀ : yex x₀ = y₀)
    {u : Fin r → ℝ}
    {x : ℝ} (_hxx : x₀ < x)
    (Y : ℕ → ℕ → Fin r → ℝ) (Y_int : ℕ → Fin s → ℝ)
    (_hY_int_eq : ∀ n : ℕ, 0 < n → ∀ i,
      Y_int n i =
        (∑ j, M.A i j * (((x - x₀) / (n : ℝ)) * f (Y_int n j)))
        + (∑ j, M.U i j * Y n n j))
    (_h_output : Filter.Tendsto (fun n : ℕ => Y n n) Filter.atTop
                   (nhds (fun i => u i * yex x))) :
    ∃ Bf : ℝ, 0 ≤ Bf ∧
      ∀ᶠ n in Filter.atTop, ∀ j : Fin s, |f (Y_int n j)| ≤ Bf
```

The conclusion says: there is a uniform bound `Bf` such that on the
cofinite tail `n ≥ N`, every stage value `f(Y_int n j)` has
`|f(Y_int n j)| ≤ Bf`.

## Textbook-style proof outline (M-matrix comparison)

Rearrange the stage equation `_hY_int_eq` by passing the absolute
value in and using Lipschitz of `f`:

```
|Y_int n i| ≤ h_n · (Σ_j |M.A i j| · (L · |Y_int n j| + |f 0|))
              + |(M.U *ᵥ Y n n) i|
            = h_n L · (Σ_j |M.A i j| · |Y_int n j|)
              + h_n · (Σ_j |M.A i j|) · |f 0|
              + |(M.U *ᵥ Y n n) i|
```

In matrix form, with `|A| := A.map(|·|)`:

```
(I - h_n L |A|) · |Y_int n| ≤ h_n · |A| · 𝟙 · |f 0| + |M.U *ᵥ Y n n|
```

For sufficiently large `n` (i.e. small enough `h_n = (x - x₀)/n`) the
hypothesis `‖h_n L |A|‖ < 1` (Frobenius norm) holds, so the M-matrix
machinery in `OpenMath/Chapter5/MMatrix.lean` applies:

* `Matrix.EntrywiseNonneg.nonneg_of_one_sub_mulVec_nonneg` (cycle
  106/107) gives the comparison principle.
* `Matrix.EntrywiseNonneg.inv_one_sub_of_norm_lt_one` (cycle 106)
  gives `(I - h_n L |A|)^{-1} ≥ 0`.

Combined: `|Y_int n|` is dominated entrywise by
`(I - h_n L |A|)^{-1} · (h_n · |A| · 𝟙 · |f 0| + |M.U *ᵥ Y n n|)`.

The output convergence `_h_output` ensures the RHS is *eventually*
bounded uniformly in `n` (because `|M.U *ᵥ Y n n|` converges and
`h_n → 0`). Hence `|Y_int n|` is eventually bounded, and Lipschitz
`f` lifts this to a bound on `|f(Y_int n j)| = |f(Y_int n j) - f(0)
+ f(0)| ≤ L · |Y_int n j| + |f 0|`, giving the desired `Bf`.

## What was tried

* Cycle 110 inlined-proof attempt was rejected per the strategy
  ("Do NOT inline-prove the M-matrix boundedness inside
  `aux_515D_stage_tendsto`"). The cycle 110 deliverable is the
  stage-side *limit shuffling* with the boundedness as a separate
  helper sorry.
* No Aristotle batch yet for this specific sub-lemma; the
  M-matrix infrastructure is in place (cycle 105–107) but the
  rearrangement step is non-trivial Lean carpentry and is best
  hand-written rather than batched.

## Possible solutions

### Approach 1: Direct M-matrix application (recommended for cycle 111)

Estimated 60–90 min. Concrete steps:

1. **Add hypothesis** `(h_norm : ‖((x - x₀) * (L : ℝ)) • A.map (|·|)‖ < 1)`
   or equivalent, so the M-matrix invariant is available for
   *some* tail of `n`. (Faithfulness divergence: textbook tacitly
   assumes this — surface it precisely, analogous to cycle 107's
   `aux_515B_eta_contraction`.)
2. **Choose `N`** such that for `n ≥ N`, `‖h_n L |A|‖ < 1` holds
   (use the `tendsto_one_div_atTop_nhds_zero_nat` style limit).
3. **Rearrange the stage equation** to the form
   `(I - h_n L |A|) · |Y_int n| ≤ rhs`.
4. **Apply `nonneg_of_one_sub_mulVec_nonneg`** entrywise to
   conclude `|Y_int n| ≤ (I - h_n L |A|)^{-1} · rhs`.
5. **Bound the RHS** uniformly using output convergence:
   `|M.U *ᵥ Y n n|` is eventually bounded (it converges), and
   `h_n → 0` makes the `h_n · |A| · 𝟙 · |f 0|` term eventually
   bounded by 1 (or any other constant).
6. **Lift to `f`** via Lipschitz: `|f(y)| ≤ L · |y - 0| + |f 0|`.

### Approach 2: Replace `_hStab` with stronger M-matrix hypothesis

If the cycle 111 proof needs an extra `‖h₀ L |A|‖ < 1` type
hypothesis on the *helper itself*, surface it on the helper's
signature (clean) rather than threading through `IsConvergent`'s
already-strengthened cycle 098 form (heavyweight).

### Approach 3 (rejected): Submit to Aristotle

The proof needs careful M-matrix infrastructure plumbing, and
historical Aristotle performance on M-matrix and discrete-Grönwall
arguments has been weak (cycles 094/096/103). Better to hand-write.

## Cross-references

* `OpenMath/Chapter5/MMatrix.lean` — the cycle 105–107 M-matrix
  infrastructure (`EntrywiseNonneg`, `nonneg_of_one_sub_mulVec_nonneg`,
  `inv_one_sub_of_norm_lt_one`).
* `lem_515B_eta_contraction_deferred.md` — sibling issue (now
  closed in cycle 107) with the same M-matrix flavor.
* The capstone `GeneralLinearMethod.stable_consistent_isConvergent`
  in `OpenMath/Chapter5/Section515.lean` consumes
  `aux_515D_stage_tendsto` (which calls this helper), so closing
  this helper closes one of the remaining 2 sorries in
  `OpenMath/Chapter5/Section515.lean`.

## Non-vacuity status

The lemma is not vacuously stated. The conclusion is a genuine
*eventual* uniform bound on `|f(Y_int n j)|` over all stages `j`,
predicated on output convergence. Without the M-matrix machinery
the bound cannot be derived by elementary means: the implicit
stage equation couples `Y_int n j` to `f(Y_int n k)` across all
`k`, and only the M-matrix comparison principle disentangles the
chain.
