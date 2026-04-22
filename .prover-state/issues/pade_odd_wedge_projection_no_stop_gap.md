# Issue: odd wedge projection no-stop lemma still missing

## Blocker
Cycle 343 split the remaining odd down-arrow gap into the two exact live helper
seams in `OpenMath/PadeOrderStars.lean`:

1. `oddDownArrowRadiusPhaseEndpointSigns_on_trueSlice_of_neg_errorConst`
2. `oddDownArrowRadiusPhaseFixedRadiusSlice_not_meet_clopen_both`

The first seam is blocked by the quantitative target now exposed directly in
code:

```lean
K * r < (-padePhiErrorConst n d) * Real.sin (((↑(n + d) + 1) : ℝ) * r) / 2
```

for the `K, δ₀` returned by `padeR_exp_neg_local_bound n d`.

The second seam is blocked because the current live inputs only prove
nonemptiness of each true-wedge radius slice; they do **not** prove that the
fixed-radius slice of the zero set is connected, singleton, or otherwise unable
to meet both sides of a clopen partition.

## Context
- `oddDownArrowRadiusPhaseSliceZero_of_neg_errorConst` no longer reuses the
  failed `η = r` strip instantiation. It is now closed modulo the new helper
  `oddDownArrowRadiusPhaseEndpointSigns_on_trueSlice_of_neg_errorConst`.
- `oddDownArrowRadiusPhaseProjectionNoStop_of_neg_errorConst` is now closed
  modulo the new helper
  `oddDownArrowRadiusPhaseFixedRadiusSlice_not_meet_clopen_both`.
- `OpenMath/PadeOrderStars.lean` compiles with exactly these 2 helper `sorry`s
  after the cycle-343 refactor.
- Cycle-343 Aristotle batch:
  - `c3160f50-9736-432f-8a49-3c422c7603cc`
  - `ee966484-4a7c-4cec-bfd7-e0571355ca08`
  - `fb99a47e-1f05-4adb-9cb2-e44462435db7`
  - `ec9a08b7-4ed5-419d-afd5-9974589af9f1`
  - `6ad5578f-fa4a-42ec-96eb-4c85673cad17`
- After the mandated single 30-minute wait and single refresh, **all five**
  cycle-343 Aristotle jobs were still `QUEUED`.
- Lean search found off-the-shelf sine lower bounds such as
  `Real.mul_lt_sin` / `Real.mul_le_sin`. These only reduce the first seam to a
  constant comparison:

  ```lean
  K < (-padePhiErrorConst n d) * (((↑(n + d) + 1) : ℝ)) / Real.pi
  ```

  or a nearby equivalent, but the current live hypotheses still provide no
  theorem connecting the `K` from `padeR_exp_neg_local_bound` to that explicit
  coefficient.

## What was tried
- Read the cycle-342 handoff, the existing blocker issue, and the two live
  `sorry` bodies first as instructed.
- Added the true-wedge helper
  `oddDownArrowRadiusPhaseEndpointSigns_on_trueSlice_of_neg_errorConst` above
  `oddDownArrowRadiusPhaseSliceZero_of_neg_errorConst`.
- Moved the old inner seam into a named local target `hgapTarget` inside that
  helper so the blocked comparison is explicit in code.
- Rewrote `oddDownArrowRadiusPhaseSliceZero_of_neg_errorConst` to use the new
  helper and keep the existing IVT proof shape on `Set.Icc (-r) r`.
- Added the fixed-radius helper
  `oddDownArrowRadiusPhaseFixedRadiusSlice_not_meet_clopen_both` above
  `oddDownArrowRadiusPhaseProjectionNoStop_of_neg_errorConst`.
- Rewrote the final projection theorem so its remaining contradiction is exactly
  delegated to that fixed-radius helper.
- Verified with
  `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/PadeOrderStars.lean`
  that the file compiles with exactly the two new helper `sorry`s.
- Submitted the five focused cycle-343 Aristotle jobs listed above, slept once
  for 30 minutes, and refreshed once.

## Possible solutions
- Strengthen the local asymptotic input near the origin from the coarse
  `≤ K * ‖z‖ ^ (n + d + 2)` remainder bound to a theorem with explicit
  next-order coefficient control, or at least a little-o statement strong enough
  to dominate the true-slice main term.
- Alternatively, derive a concrete upper bound on the **specific** `K` returned
  by `padeR_exp_neg_local_bound n d` that is small enough to imply the target
  inequality above after a standard lower bound on `Real.sin`.
- For the final clopen contradiction, prove one additional slice theorem on the
  true wedge for fixed `ρ`:
  either uniqueness of the zero on `Set.Icc (-ρ) ρ`, connectedness of the fixed
  radius zero slice, or a monotonicity theorem for
  `s ↦ Complex.im (padeR n d (...) * exp (-(...)))`.
  Without one of those, the current same-radius witnesses in `C` and `Cᶜ` do
  not contradict the live topology alone.

## Cycle 344 Addendum

### Exact true-slice statement now exposed

The cycle-343 local target

```lean
K * r < (-padePhiErrorConst n d) * Real.sin (((↑(n + d) + 1) : ℝ) * r) / 2
```

is not the right seam to attack directly. The better local statement is a
**second-order factorization** of `padeR n d z * exp (-z)` at the origin.

Let `m := n + d`. For `m > 0`, the candidate exact degree-`m + 2` coefficient is

```lean
a₂(n,d) =
  padePhiErrorConst n d *
    (((n : ℝ) - d) * ((↑m + 1 : ℝ))) /
      (((↑m : ℝ) * ((↑m + 2 : ℝ))))
```

equivalently

```lean
a₂(n,d) =
  padePhiErrorConst n d * ((n - d) * (m + 1)) / (m * (m + 2))
```

after the obvious casts.

The exact local theorem needed is:

```lean
∃ h : ℂ → ℂ, ∀ z : ℂ,
  padeR n d z * exp (-z) -
      (1
        - (padePhiErrorConst n d : ℂ) * z ^ (m + 1)
        + (a₂(n,d) : ℂ) * z ^ (m + 2)) =
    z ^ (m + 3) * h z
```

or any equivalent theorem-local `O(‖z‖^(m+3))` bound after subtracting that
explicit degree-`m + 2` term.

### Why this matters

Numerical checks on small `(n,d)` match the formula above, and the coefficient
comparison becomes favorable:

```lean
|a₂(n,d)| / ((-padePhiErrorConst n d) * (m + 1)) = |n - d| / (m * (m + 2))
```

so `|a₂(n,d)|` is strictly smaller than the true-slice sine slope by a uniform
factor. This is exactly what the old `hgapTarget` was missing.

### Exact fixed-radius local statement still missing

Even if the endpoint helper is rebuilt from the second-order factorization
above, the final projection seam still needs a fixed-radius uniqueness theorem.
The sharp theorem-local target is:

```lean
∃ δmono > 0, ∀ ρ ∈ Set.Ioo (0 : ℝ) δmono,
  StrictMonoOn
    (fun s =>
      Complex.im
        (padeR n d
            ((↑ρ : ℂ) * exp (↑(oddDownArrowRadiusPhaseCenter n d + s) * I)) *
          exp (-((↑ρ : ℂ) * exp (↑(oddDownArrowRadiusPhaseCenter n d + s) * I)))))
    (Set.Icc (-ρ) ρ)
```

or any theorem-local equivalent such as “the fixed-radius slice has at most one
zero on `Set.Icc (-ρ) ρ)`”.

Without that statement, the contradiction in
`oddDownArrowRadiusPhaseFixedRadiusSlice_not_meet_clopen_both` is still
unsupported.

### Aristotle status in cycle 344

Fresh cycle-344 Aristotle jobs:

- `b58e353a-8d3b-468c-87ac-610ac57dcc10`
- `488f6dd6-71c6-4afc-907e-5207d2287a26`
- `b93eb787-fc18-41ed-ab57-992c1206a54f`
- `a3eacefb-ee5f-4e2a-ad48-ac56d4f9adb0`
- `861b766b-4677-4960-bb86-0294185f6a77`

After the cycle’s single refresh, all five remained `QUEUED`.

## Cycle 345 Addendum

### What closed locally

The denominator-side bookkeeping is no longer part of the blocker. Cycle 345
added exact local factorization lemmas in `OpenMath/PadeOrderStars.lean`:

- `exp_neg_sub_linear_factorization`
- `padeQ_sub_linear_factorization`
- `padeQ_inv_linear_factorization`
- `exp_neg_div_padeQ_linear_factorization`

So the local quotient expansion is now formalized:

```lean
exp (-z) / padeQ n d z = 1 - ((n : ℂ) / (n + d : ℂ)) * z + z ^ 2 * h z
```

whenever `padeQ n d z ≠ 0`.

### Exact analytic blocker now remaining

The true first seam is now exactly the new local theorem

```lean
private theorem padeR_exp_neg_second_order_factorization
    (n d : ℕ) (hm : 0 < n + d) :
    ∃ h : ℂ → ℂ, ∀ z : ℂ,
      padeR n d z * exp (-z) -
          (1
            - (padePhiErrorConst n d : ℂ) * z ^ (n + d + 1)
            + (padeRExpNegSecondCoeff n d : ℂ) * z ^ (n + d + 2)) =
        z ^ (n + d + 3) * h z
```

with

```lean
padeRExpNegSecondCoeff n d =
  padePhiErrorConst n d *
    ((n - d) * (n + d + 1)) / ((n + d) * (n + d + 2))
```

after the obvious casts.

Because the quotient linear term is now closed, the exact missing substatement
inside this theorem is the degree-`n + d + 2` coefficient / factorization of the
Padé defect itself, not any further denominator control.

### Exact topology blocker now remaining

The second seam is now isolated as the local uniqueness theorem

```lean
private theorem oddDownArrowRadiusPhaseFixedRadiusSlice_atMostOne_zero_of_neg_errorConst
    (n d : ℕ) (hC : padePhiErrorConst n d < 0) :
    ∃ δmono > 0, ∀ ρ ∈ Set.Ioo (0 : ℝ) δmono,
      ∀ s₁ ∈ Set.Icc (-ρ) ρ,
        ∀ s₂ ∈ Set.Icc (-ρ) ρ,
          oddDownArrowRadiusPhaseIm n d (ρ, s₁) = 0 →
          oddDownArrowRadiusPhaseIm n d (ρ, s₂) = 0 →
          s₁ = s₂
```

and `oddDownArrowRadiusPhaseFixedRadiusSlice_not_meet_clopen_both` is now
blocked only on that theorem-local at-most-one-zero statement.

### Aristotle status in cycle 345

Cycle-345 jobs submitted after canceling the stale queued jobs:

- `24895e30-89d4-4db8-8b95-d0f1001de8df`
- `9f8f8368-8414-4974-a2ff-289bc0e70588`
- `ad07f453-2f28-4cb2-bd45-b28a69adcc5f`
- `b0eaefbd-dc77-4182-aea4-6e48663c16f0`
- `5e6710c5-41f3-4122-9f2b-0e72b069a31b`

The required `sleep 1800` wait was launched. The single post-wait refresh was
still pending at the point this addendum was written.
