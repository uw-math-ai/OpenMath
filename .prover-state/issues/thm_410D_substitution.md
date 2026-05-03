# Issue: §410D log-form order condition — two substitution sorries

## Blocker

`OpenMath/Chapter4/Section410.lean::thm_410D` (Butcher §410D, log-form
order condition) is stated and almost fully scaffolded, but its proof
depends on two substitution sub-lemmas left as `sorry`:

1. `coeff_eq_zero_of_coeff_subst_eq_zero` (line 949) — *reverse*
   direction of "substitution by unit-leading series preserves vanishing
   of low coefficients".
2. `subst_logOnePlusPS_expNegPS` (line 969) — load-bearing identity
   `subst logOnePlusPS expNegPS = oneOverOnePlusPS`, equivalent to
   `exp(-log(1+w)) = (1+w)^{-1}` in formal power series.

Cycle 077 (this cycle) closed the §410D infrastructure
(`oneOverOnePlusPS`, `logOnePlusPS`, `genFnLog`, basic coefficient
lemmas, `(1+X) · oneOverOnePlusPS = 1`, the *forward* direction of
substitution-preserves-vanishing, and the substitution decomposition
`genFnLog M = subst logOnePlusPS (genFn M)`). The two sorries above
are the remaining work to close `thm_410D`.

## Context

### Sorry 1 — `coeff_eq_zero_of_coeff_subst_eq_zero` (reverse direction)

**Statement** (line 949, Section410.lean):

```lean
theorem coeff_eq_zero_of_coeff_subst_eq_zero
    {g : PowerSeries ℝ} (hg0 : (PowerSeries.constantCoeff (R := ℝ)) g = 0)
    (hg1 : (PowerSeries.coeff (R := ℝ) 1) g = 1)
    {f : PowerSeries ℝ} {p : ℕ}
    (h : ∀ j ≤ p, (PowerSeries.coeff (R := ℝ) j) (PowerSeries.subst g f) = 0) :
    ∀ j ≤ p, (PowerSeries.coeff (R := ℝ) j) f = 0
```

**Mathematical content**: Substitution by a unit-leading series
(constant term 0, linear coefficient 1) is a triangular automorphism
on the truncated power-series ring, so it reflects the property
"first p+1 coefficients vanish".

**Proof sketch** (by induction on `p`):
- *Base* `p = 0`: `coeff 0 (subst g f) = constantCoeff f`, since the
  only `g^d` with non-zero constant term is `g^0 = 1`. Apply the
  hypothesis at `j = 0`.
- *Step* `p = p' + 1`: assume IH for `p'`. For `j = p'+1`, use
  `PowerSeries.coeff_subst`:
  ```
  coeff (p'+1) (subst g f) = ∑ᶠ d, (coeff d f) • coeff (p'+1) (g^d).
  ```
  - `d = 0`: `coeff (p'+1) (g^0) = coeff (p'+1) 1 = 0` (since
    `p'+1 ≥ 1`).
  - `1 ≤ d ≤ p'`: by IH, `coeff d f = 0`. Term vanishes.
  - `d = p'+1`: `(g^(p'+1)).order = p'+1`, and
    `coeff (p'+1) (g^(p'+1)) = (coeff 1 g)^(p'+1) = 1` (leading
    coefficient of a unit-leading power). Term equals `coeff (p'+1) f`.
  - `d > p'+1`: `(g^d).order ≥ d > p'+1`, so `coeff (p'+1) (g^d) = 0`.
  Sum = `coeff (p'+1) f`. By hypothesis, this equals 0.

**Mathlib infrastructure available**:
- `PowerSeries.coeff_subst : (MvPowerSeries.coeff e) (PowerSeries.subst a f)
   = ∑ᶠ d, (coeff d f) • (MvPowerSeries.coeff e (a^d))` — the explicit
   coefficient formula.
- `PowerSeries.le_order_pow : n • φ.order ≤ (φ ^ n).order` — order
   inequality for powers.
- `PowerSeries.coeff_of_lt_order` and `PowerSeries.nat_le_order` —
   converting between vanishing and order bounds (already used in the
   forward direction).

**Hardness**: The challenge is the leading-coefficient claim
`coeff d (g^d) = (coeff 1 g)^d` for unit-leading `g`. Mathlib's
`Polynomial.leadingCoeff_pow` does not have an obvious power-series
analogue. A clean path may require a dedicated helper lemma proved
by induction on `d` via Cauchy product.

### Sorry 2 — `subst_logOnePlusPS_expNegPS` (load-bearing identity)

**Statement** (line 969):

```lean
theorem subst_logOnePlusPS_expNegPS :
    PowerSeries.subst logOnePlusPS expNegPS = oneOverOnePlusPS
```

**Mathematical content**: `exp(-log(1+w)) = (1+w)^{-1}` in
`PowerSeries ℝ`.

**Proof sketch** (algebraic, via uniqueness of the inverse):
1. `expPS · expNegPS = 1` (Mathlib: `PowerSeries.exp_mul_exp_neg_eq_one`,
   already bridged in this file as `expPS_mul_expNegPS_eq_one`).
2. Apply `subst logOnePlusPS` to both sides (since substitution is an
   algebra homomorphism via `PowerSeries.substAlgHom`):
   ```
   (subst log expPS) · (subst log expNegPS) = subst log 1 = 1.
   ```
3. Need `subst logOnePlusPS expPS = 1 + X` (equivalently
   `exp(log(1+w)) = 1+w`). **This is the genuinely missing piece.**
4. Combined with `(1 + X) · oneOverOnePlusPS = 1` (proved this cycle
   as `onePlusX_mul_oneOverOnePlusPS_eq_one`), uniqueness of the inverse
   gives `subst log expNegPS = oneOverOnePlusPS`.

**The genuinely missing piece**: Step 3 — `exp(log(1+w)) = 1+w`. This
identity does not appear directly in Mathlib (no `PowerSeries.log`
exists at our pinned Mathlib version, only `PowerSeries.exp`).

**Possible routes**:

(a) **Direct coefficient computation**: prove
    `subst logOnePlusPS expPS = 1 + X` by computing
    `coeff k (subst logOnePlusPS expPS)` via `PowerSeries.coeff_subst`
    and comparing with `coeff k (1 + X)`. Requires identifying the
    Bell-polynomial / exponential-of-log identity.

(b) **Inverse pair via Mathlib's `PowerSeries.invOfUnit`**: define
    `oneOverOnePlusPS := PowerSeries.invOfUnit (1 + X) 1` so that
    `(1+X) · oneOverOnePlusPS = 1` becomes definitional. Then use
    `subst log` algebra-hom property + `expPS_mul_expNegPS_eq_one` to
    derive the rest. Still needs `subst log expPS = 1 + X`.

(c) **Define a Mathlib `PowerSeries.log`**: contribute `log(1+X)` as
    a power series to Mathlib (or in OpenMath as a helper) with the
    inversion lemmas `exp(log(1+X)) = 1+X` and `log(1+(exp(X)-1)) = X`.
    Most general but most work.

(d) **Sidestep substitution entirely**: prove §410D directly via a
    triangular linear-algebra argument relating `coeff p (genFnLog M)`
    to `(C M 0, C M 1, ..., C M p)`. Avoids `PowerSeries.subst` but
    requires explicit Faà di Bruno / Bell polynomial computations.

## What was tried (cycle 077)

- **Direct algebraic chain**: traced the substitution decomposition
  `genFnLog M = subst log (genFn M)` cleanly using
  `PowerSeries.coe_substAlgHom`, `map_sub`, `map_mul`, `subst_X`. This
  works (proved as `genFnLog_eq_subst_genFn`) and isolates the issue
  to the load-bearing identity.

- **Aristotle batch** (project ID
  `18504be5-2481-4d60-9d7b-12b8a5cd2b47`, file
  `.prover-state/aristotle_submissions/cycle_077/section410d_helpers.lean`):
  submitted 5 sub-lemmas including the reverse-direction substitution
  lemma and `subst log expPS = 1 + X`. After ~80 minutes, Aristotle
  reported only 13% progress; results not yet usable. Worth checking
  in cycle 078.

- **Coefficient-direct route**: investigated computing
  `coeff p (oneOverOnePlusPS^m)` via the binomial series identity
  `(-1)^p · binom(p+m-1, m-1)`. Verified by hand on explicit Euler
  that `coeff p (genFnLog M) ≠ C M p` in general (they agree at low
  orders only when previous orders vanish — the textbook substitution
  triangular structure). Direct comparison would require Bell-polynomial
  machinery; not feasible in one cycle.

## Possible solutions for cycle 078

**Recommended priority order**:

1. **Check Aristotle results** from this cycle's submission first
   (project `18504be5-...`). If Aristotle solved any of the two
   blockers, integrate immediately.

2. **Tackle the reverse direction sorry first** (independent of the
   load-bearing identity). The proof sketch above is concrete; the
   key sub-lemma is `coeff d (g^d) = (coeff 1 g)^d` for unit-leading
   `g`. This may itself merit an Aristotle batch.

3. **For `subst_logOnePlusPS_expNegPS`**, attempt route (a) above —
   direct coefficient comparison via `PowerSeries.coeff_subst`. If
   intractable, try route (c) — define a minimal `PowerSeries.log`
   helper in OpenMath/Chapter4/PowerSeriesLog.lean with just the
   needed lemmas.

4. **Backup**: if both sorries remain stubborn, prove
   `thm_410D_forward` (the easier direction
   `M.HasOrderAtLeast p → ∀ j ≤ p, coeff j (genFnLog M) = 0`) as a
   separate one-directional lemma using only the *forward* substitution
   lemma (already proved). This gives a partial §410D and demonstrates
   non-vacuity. Mark `thm_410D` (the iff) as still open.

## Files affected

- `OpenMath/Chapter4/Section410.lean` (lines 949, 969) — the two sorry
  sites.
- `.prover-state/aristotle_submissions/cycle_077/section410d_helpers.lean`
  — Aristotle batch in progress.
- `extraction/formalization_data/lean_status.json::thm:410D` — status
  remains `unformalized` until both sorries are closed.
