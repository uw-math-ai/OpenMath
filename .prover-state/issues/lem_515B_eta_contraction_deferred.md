# Issue: `aux_515B_eta_contraction` deferred — needs M-matrix `(I − h₀L|A|)^{−1}` positivity

## Status (cycle 107) — RESOLVED

Closed in cycle 107 via the M-matrix comparison principle from cycle
106 (`Matrix.EntrywiseNonneg.nonneg_of_one_sub_mulVec_nonneg`) plus an
explicit `‖(h₀ * L) • |A|‖ < 1` Frobenius-norm hypothesis (faithfulness
divergence: textbook tacitly assumes "h₀ small enough"; we surface the
precise condition). The new hypothesis is propagated up to
`localStepError_bound`'s signature so callers must supply it. Clean
axioms (`[propext, Classical.choice, Quot.sound]`).

## Status (cycle 106) — PARTIAL: M-matrix infrastructure landed

Cycle 106 closed the **inverse-positivity** lemma (Priority 1 of cycle
106 plan):

```
Matrix.EntrywiseNonneg.inv_one_sub_of_norm_lt_one
    {M : Matrix n n ℝ} (hM : M.EntrywiseNonneg) (h_norm : ‖M‖ < 1) :
    (Ring.inverse ((1 : Matrix n n ℝ) - M)).EntrywiseNonneg
```

and the **comparison principle** lemma (Priority 2):

```
Matrix.EntrywiseNonneg.nonneg_of_one_sub_mulVec_nonneg
    {M : Matrix n n ℝ} (hM : M.EntrywiseNonneg) (h_norm : ‖M‖ < 1)
    {v : n → ℝ} (h : ∀ i, 0 ≤ ((1 - M) *ᵥ v) i) :
    ∀ i, 0 ≤ v i
```

Both proved via Mathlib's `hasSum_geom_series_inverse` (Neumann series)
plus `Pi.hasSum` to extract entrywise convergence; clean axioms
(`[propext, Classical.choice, Quot.sound]`). Live in
`OpenMath/Chapter5/MMatrix.lean`, scoped under `Matrix.Norms.Frobenius`.

Cycle 107 should close `aux_515B_eta_contraction` directly: add the
hypothesis `‖h₀ • L • A.map(|·|)‖ < 1`, reduce to the comparison lemma
above, and update the unique `localStepError_bound` caller to carry
the new hypothesis. Estimated 90 min / ~120 LOC per cycle 106 plan.

## Blocker

The auxiliary lemma `aux_515B_eta_contraction` in
`OpenMath/Chapter5/Section515.lean:931` (sorry at line 973) requires
the M-matrix monotonicity principle:

> If `x ≤ M·x + b` (entrywise) with `M ≥ 0` and `(I − M)` is an
> M-matrix (so `(I − M)^{−1} ≥ 0`), then `x ≤ (I − M)^{−1}·b`.

Specifically, with `M = h₀ L |A|` (entrywise absolute value), the
positivity of `(I − h₀ L |A|)^{−1}` follows from M-matrix theory
(Perron–Frobenius / Neumann series) under `ρ(h₀ L |A|) < 1`. This
infrastructure is multi-cycle Mathlib work.

## Context

The lemma signature (from `OpenMath/Chapter5/Section515.lean:931`):

```lean
private theorem aux_515B_eta_contraction {s r : ℕ}
    (A : Matrix (Fin s) (Fin s) ℝ)
    (U : Matrix (Fin s) (Fin r) ℝ)
    {h h₀ L M_bound δ_max : ℝ}
    (_hh : 0 ≤ h) (_hh_le : h ≤ h₀) (_h₀_pos : 0 < h₀)
    (_hL : 0 ≤ L) (_hM : 0 ≤ M_bound)
    (_hδ_max_nonneg : 0 ≤ δ_max)
    (c : Fin s → ℝ) (_hc_nonneg : ∀ i, 0 ≤ c i)
    (ell_U phi_A η : Fin s → ℝ)
    (_hell_U_nonneg : ∀ i, 0 ≤ ell_U i)
    (_hphi_A_nonneg : ∀ i, 0 ≤ phi_A i)
    (_hellU_eq : ∀ i, ell_U i - h₀ * L * (∑ j, |A i j| * ell_U j)
                    = ∑ j, |U i j|)
    (_hphiA_eq : ∀ i, phi_A i - h₀ * L * (∑ j, |A i j| * phi_A j)
                    = (1/2) * (c i)^2 + ∑ j, |A i j * c j|)
    (δ : Fin r → ℝ)
    (_hδ_max : ∀ k, |δ k| ≤ δ_max)
    (_hcontraction : ∀ j, |η j - ∑ k, U j k * δ k|
                          ≤ h * L * (∑ k, |A j k| * |η k|)
                            + h^2 * L^2 * M_bound *
                              ((1/2) * (c j)^2 + ∑ k, |A j k * c k|)) :
    ∀ j, |η j| ≤ ell_U j * δ_max + h^2 * L^2 * M_bound * phi_A j
```

The lemma is the "η contraction" core of Butcher's lem:515B
(p. 414): given a per-stage contraction estimate plus the linear
systems defining the `ell_U` and `phi_A` "ℓ-vectors", it should
produce the closed-form `|η_j|` bound.

## Textbook proof outline (Neumann-series argument)

Starting from the contraction estimate:
```
|η_j − Σ_k U_{jk}·δ_k| ≤ h L Σ_k|A_{jk}|·|η_k|
                       + h² L² M (½c_j² + Σ_k|A_{jk}·c_k|)
```

Apply triangle inequality to bound `|η_j|`:
```
|η_j| ≤ |Σ_k U_{jk}·δ_k| + h L Σ_k|A_{jk}|·|η_k|
      + h² L² M (½c_j² + Σ_k|A_{jk}·c_k|)
     ≤ Σ_k |U_{jk}|·δ_max + h L Σ_k|A_{jk}|·|η_k|
      + h² L² M (½c_j² + Σ_k|A_{jk}·c_k|)
```

Vectorially: `|η| ≤ h L |A|·|η| + (Σ_k|U_{jk}|·δ_max
                                + h² L² M·(½c² + |A·c|))`

Rearranged: `(I − h L |A|)·|η| ≤ Σ|U|·δ_max + h² L² M·(½c² + |A·c|)`

Since `h ≤ h₀` and entries are non-negative,
`(I − h L |A|)·|η| ≤ (I − h₀ L |A|)·|η|` would WORSEN the bound (wrong
direction). But the textbook actually rearranges differently — using
the *defining* equations of `ell_U` and `phi_A` (which involve `h₀`
not `h`), we have:

```
(I − h₀ L |A|)·ell_U = Σ|U|        (column = "δ_max coefficient")
(I − h₀ L |A|)·phi_A = ½c² + |A·c|  (column = "h²L²M coefficient")
```

So the *target bound* `ell_U·δ_max + h²L²M·phi_A` satisfies:
```
(I − h₀ L |A|)·(ell_U·δ_max + h²L²M·phi_A)
  = Σ|U|·δ_max + h²L²M·(½c² + |A·c|)
```

Combined with `(I − h L |A|)·|η| ≤ rhs`, we want to deduce
`|η| ≤ ell_U·δ_max + h²L²M·phi_A`.

The argument requires:

1. `(I − h₀ L |A|)·(ell_U·δ_max + h²L²M·phi_A) ≥ (I − h L |A|)·|η|`
   (from the contraction estimate, using `h ≤ h₀`).

2. `(I − h₀ L |A|)^{−1} ≥ 0` (entrywise).

Then `(I − h₀ L |A|)^{−1} · (I − h L |A|)·|η| ≤ ell_U·δ_max + h²L²M·phi_A`,
and bounding `(I − h₀ L |A|)^{−1}·(I − h L |A|) ≥ I` (since `h ≤ h₀`
means `(I − h L |A|) − (I − h₀ L |A|) = (h₀−h)L|A| ≥ 0`, and
`(I − h₀L|A|)^{−1} ≥ 0`) gives `|η| ≤ ell_U·δ_max + h²L²M·phi_A`.

The key inputs are (a) `(I − h₀ L|A|)^{−1} ≥ 0` (M-matrix theorem),
and (b) Banach-perturbation arguments to control the inverse on
non-negative cones.

## What was tried

* Direct manual proof — abandoned due to multi-cycle Mathlib
  infrastructure scope (M-matrix theorem, Perron–Frobenius for
  non-negative matrices, Neumann-series convergence, monotonicity
  of inverse). See cycle 104 strategy section "Priority 3 — TRIAGE,
  decision (b-i) DEFAULT".
* Aristotle batch (cycle 103, project
  `4688b630-d9c9-4f86-9572-7e4bd9a6b0b8`) — at 2% completion as of
  cycle 104 start (2026-05-03 18:04 UTC). Per CLAUDE.md, no
  re-poll this cycle.

## Possible solutions

### Approach 1: Build M-matrix infrastructure (recommended, multi-cycle)

Estimated: 2–3 cycles for the M-matrix skeleton, then 1 cycle to
close `aux_515B_eta_contraction`.

* Cycle N+1: Define `IsMMatrix M : Prop` (e.g., off-diagonal
  non-positive + monotone-inverse condition). Prove
  `(I − cM).IsMMatrix` for `M ≥ 0` and `c·ρ(M) < 1`.
* Cycle N+2: Prove `(I − cM)^{−1} ≥ 0` (entrywise) for non-negative
  `M`, scalar `c ≥ 0` with `c·ρ(M) < 1`. Likely via Neumann series:
  `(I − cM)^{−1} = Σ_n (cM)^n`, valid when the series converges.
* Cycle N+3: Apply the inverse-positivity to close
  `aux_515B_eta_contraction` directly.

Mathlib pointers (search via `lean_local_search "diagonally
dominant"`, `lean_loogle "Matrix _ _ _ → Matrix _ _ _"`):
* `Matrix.inv` / `Matrix.nonsing_inv` for the inverse machinery.
* `NNReal.tsum_geometric_of_lt_one` or analogous for the Neumann
  geometric-series bound.
* `Matrix.PosSemidef` for non-negativity infrastructure (note: this
  is the wrong notion — we want *entrywise* non-negativity, not
  spectral non-negativity).

### Approach 2: Re-submit a simpler decomposition to Aristotle

Decompose `aux_515B_eta_contraction` into smaller pieces:
* Specialize to `h = h₀` (eliminates the `h ≤ h₀` parameter).
* `Finset.induction_on` over `Fin s` size — works for triangular
  `A` (lower-triangular case is explicit RK; closed-form solvable
  by forward substitution).

Submit as a fresh Aristotle batch. Do not block on it; defer
evaluation to next cycle.

### Approach 3 (rejected): Manual full M-matrix proof in one cycle

Per cycle 104 strategy: the infrastructure footprint is too large
(Perron–Frobenius for non-negative matrices, Neumann-series
convergence, monotonicity of inverse) and would dwarf other
priorities.

## Cross-references

* Analogous Banach-perturbation infrastructure for §514:
  `cesaro_inverse_I_minus_V.md` (similar `(I − V)^{−1}` flavor).
* The `_hellU_eq` / `_hphiA_eq` side conditions in the lemma
  signature are *defining equations* for the `ell_U` and `phi_A`
  vectors. They are taken as hypotheses precisely BECAUSE we lack
  the inverse infrastructure to construct them. Once
  `(I − h₀ L|A|)^{−1}` is available, the construction step is one
  matrix-vector product.

## Non-vacuity status

The lemma is not vacuously stated — the proxy parameters `ell_U`,
`phi_A` with their side conditions ensure that any *witnesses*
must satisfy non-trivial linear systems. The lemma's *content*
(the inequality bound) is genuinely provable; the *gap* is
constructing `ell_U` and `phi_A` with non-negativity, which is the
M-matrix infrastructure. The downstream theorem
`localStepError_bound` (cycle 104, line 993) applies
`aux_515B_eta_contraction` as a black-box hypothesis and so its
faithfulness is unaffected by this `sorry`.
