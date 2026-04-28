# Issue: Butcher §382 raw tableau composition is not associative on `c`

## Status (cycle 502)

Cycle 502 landed **partial** associativity for `ButcherProduct`: the
stage-coefficient matrix `A` and weight vector `b` agree on the nose
under the canonical reassociation `finReassoc s t u : Fin ((s+t)+u) ≃
Fin (s + (t+u))`. See `OpenMath/ButcherGroup.lean`:

- `ButcherProduct.assoc_A`
- `ButcherProduct.assoc_b`
- `ButcherTableau.elementaryWeight_eq_of_A` (cross-size helper)
- `ButcherProduct.bSeries_assoc`
- `QuotEquiv.product_bSeries_assoc`
- `QuotEquiv.product_weightsSum_assoc`
- `QuotEquiv.product_satisfiesTreeCondition_assoc`

The remaining obstruction is solely in the `c` (node / abscissa) field.

## Concrete `c` mismatch

For `t₁ : ButcherTableau s`, `t₂ : ButcherTableau t`,
`t₃ : ButcherTableau u`, with the current

```lean
def ButcherProduct (t₁ : ButcherTableau s) (t₂ : ButcherTableau t) :
    ButcherTableau (s + t) where
  ...
  c := fun i =>
    Fin.addCases (fun i₁ => t₁.c i₁) (fun i₂ => 1 + t₂.c i₂) i
```

we get on the third (`u`-)block:

| Bracketing             | `c` on `u`-block     |
| ---                    | ---                  |
| `(t₁ * t₂) * t₃`       | `1 + t₃.c k`         |
| `t₁ * (t₂ * t₃)`       | `1 + (1 + t₃.c k)`   |

so the on-the-nose `IsRKEquivalent` associativity (which requires `c`
agreement) fails. The `t`-block agrees: both bracketings give
`1 + t₂.c j`. The `s`-block agrees: both give `t₁.c i`.

## Why this matters

The `c` field is **not** consumed by `elementaryWeight`, `bSeries`,
`satisfiesTreeCondition`, or `hasTreeOrder` — those only depend on `A`
and `b`. So §384's elementary-weight homomorphism is **unblocked** by
the partial-associativity result that landed in cycle 502.

The `c`-mismatch only matters for invariants that explicitly read off
the abscissa values, e.g. autonomy / non-autonomous embedding diagnostics.

## Possible fixes (for a future cycle, *not* this one)

1. **Rescaling `c`.** Redefine

   ```lean
   c := fun i =>
     Fin.addCases (fun i₁ => t₁.c i₁) (fun i₂ => 1 + t₂.c i₂) i
   ```

   to use a *step-length-aware* offset, e.g. carry the explicit step
   `h₁` of the outer method so that the inner method's `c`-shift
   inherits the outer scale. Compositional consistency for
   non-autonomous problems requires this.

2. **Quotient-side `cSum`.** Absorb the offset into a derived
   `QuotEquiv.cSum`-style invariant rather than the raw `c` field.
   This is the lightest-touch option: keep `ButcherProduct` as a
   "tableau up to relabel and `c`-shift" object, and prove
   associativity at the quotient level under a coarser equivalence.

3. **Cosier equivalence.** Define
   `IsRKEquivalent_AB`-only at the type level, lift to
   `QuotEquivAB`, and land full §382 associativity there. This is
   the cleanest from a category-theoretic standpoint but doubles the
   §381 layer and is probably overkill for §38's downstream needs.

The cycle-502 partial result already covers the §384 use case
(elementary-weight homomorphism on `QuotEquiv.bSeries`), so this fix
is no longer on the critical path for advancing §38.

## What was tried

Cycle 495 attempted the raw four-parameter `ButcherProduct` route and
was reverted after it raised the sorry count from 0 to 1. The recorded
task-result mismatch was the nested weight-list disagreement
`[γ₁δ₁, γ₁δ₂, γ₂]` vs `[γ₁, γ₂δ₁, γ₂δ₂]`. Cycle 500 reverted to
plain concatenation for `b` (no nested scaling), which fixed the `b`
issue but exposed the `c` offset issue documented above.

## Pointers

- Source: `OpenMath/ButcherGroup.lean` (look for `ButcherProduct.assoc_A`
  and the `## §382 partial associativity` section header).
- Cycle-502 task result:
  `.prover-state/task_results/cycle_502.md`.
- Aristotle bundle that produced the `finReassoc` analysis:
  `.prover-state/aristotle_results/9fa101c1-3f54-428d-9bed-dfad3a0ede24/product_assoc_scratch_aristotle/FinReassoc.lean`.
