# Cycle 332 — Strategy

## TL;DR

The §344 small-`s` direct-form D-ladder (cycles 322–331) is **saturated**
— six consecutive direct-form ships at `s ∈ {1, 2}` covering every
Radau/Lobatto subfamily that admits a small-`s` instance. Cycle 331's
task results explicitly flag diminishing returns on further mechanical
rungs.

Pivot this cycle to the **C(s)-coincidence theorem for Radau I `s = 2`**
— the audit-confirmed *first non-trivial step beyond mechanical direct-
form transcription* within §344. Mechanical port of cycle 324's
`butcherRadauII_collocationA_two` recipe (lines 1417–1614 of
`Section344.lean`) to Radau I abscissae `(0, 2/3)`, then prove the
coincidence theorem
`butcherRadauI_collocation_two = butcherRadauIDirect_two` against cycle
329's direct form.

Estimated 150–180 LOC, single cycle, axiom-clean target.

## What to ship (in order)

All deliverables append to `OpenMath/Chapter3/Section344.lean` **after
cycle 331's `butcherLobattoIIIDirect_two` block** (currently the file's
last block, ending around line 2093). Open a new Phase D.12 section
heading.

### Deliverable 1 — `butcherRadauI_collocationA_two` (def, ~6 LOC)

```lean
/-! ## Deliverable D.12 — Small-`s` RKTableau (Radau I C(s), `s = 2`,
collocation form)

Cycle 332: the *first non-trivial step beyond mechanical direct-form
transcription* in the §344 D-ladder. Mirror cycle 324's
`butcherRadauII_collocationA_two` template at the Radau I abscissae
`(0, 2/3)` and prove the coincidence theorem with cycle 329's
`butcherRadauIDirect_two`. This formalises the cycle 329 audit's
confirmed coincidence (the C(s)-variant of plain-quadrature families
agrees with plain Lagrange collocation, unlike the reflection-style /
D(s) / C(s−1) variants of cycles 326/327/328/330/331 which all diverge).

  `c = (0, 2/3)`, `b = (1/4, 3/4)`,
  `A = !![0, 0; 1/3, 1/3]`. -/

/-- **Butcher §344 — Radau I collocation A-matrix at `s = 2`**.
Entry `(i, j) = ∫₀^{c_i} L_j(x) dx`, where the Lagrange basis
polynomials `L_j` are taken over the two-leaf Radau I abscissae
`c = (c_0, c_1) = (0, 2/3)` (`butcherRadauI_zeros_two`, cycle 320). At
`s = 2` the four entries are `(0, 0, 1/3, 1/3)` — matching Butcher
Table 344(I) p. 225 (the C(s)-variant Radau I A-matrix). -/
noncomputable def butcherRadauI_collocationA_two
    (i j : Fin 2) : ℝ :=
  ∫ x in (0 : ℝ)..butcherRadauI_zeros_two i,
    (Lagrange.basis Finset.univ butcherRadauI_zeros_two j).eval x
```

### Deliverable 2 — Four `_apply` theorems (~110 LOC total)

Lagrange basis at `(0, 2/3)`:
- `L_0(x) = (x − 2/3) / (0 − 2/3) = 1 − (3/2)x`
- `L_1(x) = (x − 0) / (2/3 − 0) = (3/2)x`

Expected entries:
- **`A_{0,0} = 0`**: `∫₀^0 L_0 = 0` (upper = lower limit).
- **`A_{0,1} = 0`**: `∫₀^0 L_1 = 0`.
- **`A_{1,0} = 1/3`**: `∫₀^{2/3} (1 − (3/2)x) dx
  = 2/3 − (3/4)(4/9) = 2/3 − 1/3 = 1/3`.
- **`A_{1,1} = 1/3`**: `∫₀^{2/3} (3/2)x dx = (3/4)(4/9) = 1/3`.

#### Recipe for `A_{0,*}` (short, ~6 LOC each)

```lean
/-- The `(0, 0)` entry of `butcherRadauI_collocationA_two` is `0`.
Since `c_0 = 0`, the integral is over `[0, 0]` and vanishes. -/
theorem butcherRadauI_collocationA_two_apply_zero_zero :
    butcherRadauI_collocationA_two ⟨0, by omega⟩ ⟨0, by omega⟩ = 0 := by
  unfold butcherRadauI_collocationA_two
  have h_c0 : butcherRadauI_zeros_two ⟨0, by omega⟩ = 0 := rfl
  rw [h_c0]
  exact intervalIntegral.integral_same
```

The `_apply_zero_one` body is verbatim with `⟨0,_⟩ ⟨0,_⟩` → `⟨0,_⟩ ⟨1,_⟩`
(the integrand changes but `intervalIntegral.integral_same` doesn't care).

#### Recipe for `A_{1,*}` (port cycle 324 verbatim)

Mirror cycle 324's `_apply_one_zero` (lines 1501–1532) and `_apply_one_one`
(lines 1539–1570) with these substitutions:

1. `butcherRadauII_*` → `butcherRadauI_*` throughout.
2. `h_c1 : butcherRadauII_zeros_two ⟨1, _⟩ = 1` → `h_c1 : butcherRadauI_zeros_two ⟨1, _⟩ = 2/3`.
3. `IntervalIntegrable _ _ 0 1` → `IntervalIntegrable _ _ 0 (2/3)`.
4. `hx : ∫₀¹ x = 1/2` → `hx : ∫₀^{2/3} x = 2/9` (via `integral_pow` at
   `b = 2/3`, `pow_one`).
5. Lagrange `h_eval`: Radau II's `(3/2) - (3/2)*x` and `(3/2)*x - (1/2)`
   (basis at `(1/3, 1)`) → Radau I's `1 - (3/2)*x` and `(3/2)*x` (basis
   at `(0, 2/3)`).

Computing the `h_eval` shapes:
- **For `L_0` at Radau I**: after
  `rw [Lagrange.basis, h_erase, Finset.prod_singleton, Lagrange.basisDivisor]`,
  the body unfolds to `(x - 2/3) * ((0 - 2/3)⁻¹)`. The `simp` with
  `butcherRadauI_zeros_two, Polynomial.eval_*` should give
  `(x - 2/3) * (-3/2) = (3/2)*(2/3) - (3/2)*x = 1 - (3/2)*x`.
  Close the `h_eval` with `ring`.
- **For `L_1` at Radau I**: similarly, body unfolds to
  `(x - 0) * ((2/3 - 0)⁻¹) = x * (3/2) = (3/2)*x`. Close with `ring`.

Final closure for `_apply_one_zero`:

```lean
-- Goal after simp_rw [h_eval] + show + rw [h_c1]:
-- ∫ x in (0 : ℝ)..(2/3 : ℝ), (1 - (3/2) * x) = 1 / 3
rw [intervalIntegral.integral_sub intervalIntegrable_const
      (hi_x.const_mul (3/2)),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    hx]
norm_num
```

Final closure for `_apply_one_one`:

```lean
-- Goal: ∫ x in (0 : ℝ)..(2/3 : ℝ), ((3/2) * x) = 1 / 3
rw [intervalIntegral.integral_const_mul, hx]
norm_num
```

(Note: `_apply_one_one`'s integrand has no additive structure, so only
`integral_const_mul` is needed — slightly simpler than `_apply_one_zero`.)

### Deliverable 3 — Assembled `RKTableau` (~5 LOC)

```lean
/-- **The collocation-form Radau I `RKTableau` at `s = 2`**: assembled
from cycle 320's `butcherRadauI_zeros_two`, cycle 321's
`butcherRadauI_quadratureWeights_two`, and cycle 332's
`butcherRadauI_collocationA_two`. Equal to cycle 329's
`butcherRadauIDirect_two` by the coincidence theorem below. -/
noncomputable def butcherRadauI_collocation_two :
    OpenMath.Chapter3.Section312.RKTableau 2 where
  A := butcherRadauI_collocationA_two
  b := butcherRadauI_quadratureWeights_two
  c := butcherRadauI_zeros_two
```

### Deliverable 4 — Coincidence theorem (~14 LOC, headline)

```lean
/-- **Coincidence (the audit-confirmed C(s) variant)**: the cycle-332
collocation-assembled Radau I tableau at `s = 2` equals cycle 329's
direct Radau I tableau. Routes through the four collocation `_apply`
evaluations (`butcherRadauI_collocationA_two_apply_*`) and cycle 321's
weight `_apply` lemmas. This is the *first non-trivial coincidence
theorem* in the §344 small-`s` ladder — the reflection-style / D(s) /
C(s−1) variants (Radau IA, Radau II D(s), Lobatto IIIC, Lobatto III)
all diverge from plain collocation per audits in cycles
326/328/330/331. -/
theorem butcherRadauI_collocation_two_eq_direct :
    butcherRadauI_collocation_two = butcherRadauIDirect_two := by
  refine OpenMath.Chapter3.Section312.RKTableau.mk.injEq .. |>.mpr ⟨?_, ?_, ?_⟩
  · funext i j; fin_cases i <;> fin_cases j
    · show butcherRadauI_collocationA_two ⟨0, by omega⟩ ⟨0, by omega⟩ = _
      rw [butcherRadauI_collocationA_two_apply_zero_zero]; rfl
    · show butcherRadauI_collocationA_two ⟨0, by omega⟩ ⟨1, by omega⟩ = _
      rw [butcherRadauI_collocationA_two_apply_zero_one]; rfl
    · show butcherRadauI_collocationA_two ⟨1, by omega⟩ ⟨0, by omega⟩ = _
      rw [butcherRadauI_collocationA_two_apply_one_zero]; rfl
    · show butcherRadauI_collocationA_two ⟨1, by omega⟩ ⟨1, by omega⟩ = _
      rw [butcherRadauI_collocationA_two_apply_one_one]; rfl
  · funext i; fin_cases i
    · show butcherRadauI_quadratureWeights_two ⟨0, by omega⟩ = _
      rw [butcherRadauI_quadratureWeights_two_apply_zero]; rfl
    · show butcherRadauI_quadratureWeights_two ⟨1, by omega⟩ = _
      rw [butcherRadauI_quadratureWeights_two_apply_one]; rfl
  · funext i; fin_cases i <;> rfl
```

This is **literally** cycle 324's `butcherRadauIIA_two_eq_direct` recipe
(lines 1597–1614) with `RadauII` → `RadauI` and `RadauIIA` → cycle 332
naming. No structural change.

### Deliverable 5 — Non-vacuity `SatisfiesB 3` (~5 LOC)

```lean
/-- **Non-vacuity**: the collocation-assembled Radau I tableau at
`s = 2` satisfies the order-3 quadrature condition `B(3)` (Radau I at
`s = 2` achieves classical order `2s − 1 = 3`). Routes via the
coincidence theorem to cycle 329's direct form. -/
example : butcherRadauI_collocation_two.SatisfiesB 3 := by
  rw [butcherRadauI_collocation_two_eq_direct]
  intro k h1 hk
  interval_cases k
  · simp [butcherRadauIDirect_two, Fin.sum_univ_two]; norm_num
  · simp [butcherRadauIDirect_two, Fin.sum_univ_two]; norm_num
  · simp [butcherRadauIDirect_two, Fin.sum_univ_two]; norm_num
```

(Verbatim port of cycle 329's `SatisfiesB 3` example at lines 1934–1939
with the lead-in `rw [butcherRadauI_collocation_two_eq_direct]` added.)

## Verification checklist

1. `lake env lean OpenMath/Chapter3/Section344.lean` exits 0.
2. `lake env lean OpenMath/Chapter3.lean` exits 0 (aggregator).
3. `grep -c sorry OpenMath/Chapter3/Section344.lean` returns 0.
4. `#print axioms` on each of the 6 new public symbols
   (`butcherRadauI_collocationA_two`,
   `butcherRadauI_collocationA_two_apply_zero_zero`,
   `_apply_zero_one`, `_apply_one_zero`, `_apply_one_one`,
   `butcherRadauI_collocation_two`,
   `butcherRadauI_collocation_two_eq_direct`)
   returns `[propext, Classical.choice, Quot.sound]` only.
5. Tautology-scanner regex
   `:=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$` returns no new hits
   on Section344.lean.

## DO NOT (failure modes from prior cycles)

1. **Do NOT use `simp only [Matrix.dotProduct]`** — `dotProduct` is at
   root namespace in current Mathlib, not `Matrix.dotProduct`. Use
   `Fin.sum_univ_two` to expose the sum form directly (cycle 167
   precedent).

2. **Do NOT attempt a one-shot proof of the coincidence theorem**
   without the four `_apply` lemmas in scope. Cycle 324's recipe
   factors the four entries first because `simp` over-reduces the
   matrix-vector apply structure in the absence of named lemmas
   (cycle 166 precedent).

3. **Do NOT skip the `show ∫ x in (0 : ℝ)..butcherRadauI_zeros_two ⟨_, _⟩, ...`
   reframing** between `unfold` and the `h_c0`/`h_c1` rewrite. The bare
   `unfold` leaves the `match`-expression on `Fin 2` unreduced; the
   `show` step coerces the goal to the integral form `rw` expects
   (cycle 324 precedent, lines 1429–1431).

4. **Do NOT use `Polynomial.funext` or `Polynomial.ext` for the
   `_apply` proofs** — the goal is an `ℝ`-valued integral identity,
   not a polynomial identity. Use `intervalIntegral.integral_sub` /
   `_const_mul` / `_const` directly (cycle 324 pattern at lines
   1453–1456).

5. **Do NOT redefine `butcherRadauI_zeros_two`,
   `butcherRadauI_quadratureWeights_two`, or `butcherRadauIDirect_two`**
   — all three exist (cycles 320, 321, 329 respectively). Reuse
   verbatim.

6. **Do NOT alter cycle 331's `butcherLobattoIIIDirect_two` block** —
   it is the immediate prior content of the file. Append after, do not
   insert before.

7. **Do NOT raise `maxHeartbeats`** above the default 200000. Each
   `_apply` lemma is small enough to fit within budget; cycle 324's
   four-entry proof compiles within the default for Section344.

8. **Do NOT submit any of these to Aristotle this cycle.** The recipe
   is a verbatim mechanical port of cycle 324's already-shipped block
   — manual closure is strictly faster (≤ 30 minutes total for all
   four `_apply` lemmas) than an Aristotle round-trip.

9. **Do NOT attempt `def:422B` or `def:442A`** as a fresh-entity pivot
   this cycle. Both are non-trivial multi-cycle deliverables: `def:422B`
   needs the LMM-side group `G₁` (mappings from rooted trees to ℝ
   under a tree-convolution operation, currently not formalised) and
   the (422a) recurrence; `def:442A` needs Riemann-surface and complex-
   analytic infrastructure that doesn't exist. Both are at least 3–5
   cycles of upstream work. Stick to the audit-validated mechanical
   port.

## Recovery / fallback plan

### Fallback A (most likely): manual `intervalIntegral` chain stalls

If `_apply_one_zero` or `_apply_one_one` stalls — most likely failure
mode is the `h_eval` `simp + ring` step (Lagrange basis evaluation) or
the closure `rw [...]; norm_num` — fall back to the **minimal scope**:

- Ship Deliverables 1 + 2's two trivial `_apply` lemmas (A_{0,0} and
  A_{0,1}, ~12 LOC total).
- Ship Deliverable 5 directly on `butcherRadauIDirect_two` (cycle 329's
  existing tableau) so non-vacuity is preserved.
- File a sub-issue
  `.prover-state/issues/butcherRadauI_collocation_two_one_row_stall.md`
  documenting the exact failure point (which integrand, which tactic).
- Defer Deliverables 3 + 4 to cycle 333.
- Net cycle effect: +2 axiom-clean lemmas, sorry count unchanged at 0.
  Cycle bar is met.

### Fallback B (extreme): entire approach stalls

If the `_apply_one_zero` integrand arithmetic doesn't close even after
the cycle 324 verbatim port (very unlikely given the recipe is
identical structurally), then this cycle's deliverable is:

- File scoping doc
  `.prover-state/issues/butcherRadauI_collocation_stall.md`
  documenting the failure.
- Ship a single ladder rung `butcherLobattoIIIDirect_three` (Phase D.12
  mechanical extension, cycle 331 task results option 3) as a fallback.
  ~150 LOC, mechanical, no recovery needed beyond the cycle 331
  template extended to three abscissae `(0, 1/2, 1)` and the 9-entry
  A-matrix `!![1/6, -1/6, 1/24; 1/6, 1/3, -1/24; ...]` (verify against
  Butcher Table 344(I) p. 225 before transcription).

## Why this target (over the alternatives)

1. **First non-trivial coincidence in §344.** Cycles 326/327/328/330/331's
   reflection-style / D(s) / C(s−1) variants all *diverged* from plain
   collocation by audit. Cycle 329's Radau I C(s) variant *coincided*
   by audit (paper arithmetic at lines 1949–1956 of `Section344.lean`'s
   cycle 329 task results) but was never formally bridged. This cycle
   ships the formal bridge.

2. **Single-cycle scope.** The recipe is a verbatim port of cycle
   324's ~200-LOC block. No new mathematical content; integrals close
   by `integral_pow` + `intervalIntegral.integral_sub` +
   `integral_const_mul` + `integral_const` exactly as in cycle 324.

3. **Unlocks future C(s)-coincidence work.** Lobatto IIIA at `s = 2`
   (cycle 323) and at `s = 3` are also plain-collocation by audit;
   future cycles can mechanically extend this template if desired.

4. **No multi-cycle dependencies.** Unlike `def:422B`, `def:442A`,
   `thm:535A` (all genuinely multi-cycle per their dependency chains),
   this target uses only already-shipped infrastructure (cycles 320,
   321, 324, 329) plus standard Mathlib interval-integral hooks.

5. **No Aristotle round-trip.** Manual closure is strictly faster than
   waiting on Aristotle for a mechanical port that already has a
   working template at hand.

## Stretch goal (only if Deliverables 1–5 close in < 60 min worker time)

Add a `SatisfiesC 2` non-vacuity example on
`butcherRadauI_collocation_two`. Since the C(s)-variant is *defined*
by satisfying `C(s)`, this is the natural defining certificate:

```lean
example : butcherRadauI_collocation_two.SatisfiesC 2 := by
  rw [butcherRadauI_collocation_two_eq_direct]
  intro i k h1 hk
  fin_cases i <;> interval_cases k <;>
    simp [butcherRadauIDirect_two, Fin.sum_univ_two] <;> norm_num
```

(Body verbatim from cycle 329 lines 1952–1955 with the
`rw [butcherRadauI_collocation_two_eq_direct]` lead-in added.)

This adds one more axiom-clean lemma to the coverage matrix at trivial
LOC cost. **Do not pursue if any earlier deliverable stalled.**

## Cycle 333 outlook (NOT this cycle)

After Deliverables 1–5 land, the next planner has clean options:

1. Extend the collocation template to **Lobatto IIIA `s = 3`**
   (Simpson's rule abscissae `(0, 1/2, 1)`; 9 collocation entries; ~3×
   cycle 332 LOC, may span 2 cycles).
2. **Pivot to a fresh entity** (cycle 331 task results option 1
   restated): `def:422B`, `def:442A`, `thm:535A`, or `thm:541A`. Each
   is genuinely multi-cycle but a scoping-doc-only cycle is feasible.
3. **Phase B.2 of `thm:344A`** (polynomial-exactness `2s − 2` /
   `2s − 3` headline; deferred from cycle 318). Multi-cycle work.

Cycle 332's job is to close the C(s)-coincidence bridge.
Cycle 333's job is to decide.
