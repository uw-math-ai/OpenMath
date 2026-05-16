# Cycle 310 Strategy — §342 Phase 3 of 3 (cor:342D): C(n) interpolation condition

## §A — Target

Per cycle 309's "Suggested next approach" §F: ship the `C(n)` half of
the four-pronged Gauss–Legendre order-2n proof (`cor:342D`), via the
**upper-limit-parametrised quadrature exactness theorem** plus the
`butcherGaussLegendreRK_satisfiesC` corollary.

Currently shipped (status: §342 cluster, cycle 309 HEAD):

* `butcherGaussLegendreRK (n : ℕ) : RKTableau n` — the general-`n`
  Gauss–Legendre tableau (cycle 309).
* `butcherGaussLegendreRK_satisfiesB (n) (hn : 0 < n) : SatisfiesB (2*n)` — B(2n) closed
  (cycle 309).
* `butcherShiftedLegendre_collocationA (n : ℕ) (i j : Fin n) : ℝ :=
  ∫ x in (0 : ℝ)..butcherShiftedLegendre_zeros n i, (Lagrange.basis ... j).eval x` —
  the canonical A-matrix (cycle 308, `Section342.lean:6846`).
* `butcherShiftedLegendre_quadrature_exact_lt_n (n) (φ) (hdeg : φ.natDegree < n)` —
  the [0, 1] version (cycle 303, `Section342.lean:6249`).

Missing: the `[0, cᵢ]` analog. Once shipped, `C(n)` falls out by
specialising to `φ = X^(k-1)`.

## §B — Priority deliverables (all in `OpenMath/Chapter3/Section342.lean`)

### P1 — `butcherShiftedLegendre_collocation_exact_lt_n` (~80 LOC)

**Statement** (mirror cycle 303's signature exactly, with one extra
`(i : Fin n)` parameter and the upper bound swapped to `_zeros n i`):

```lean
theorem butcherShiftedLegendre_collocation_exact_lt_n
    (n : ℕ) (i : Fin n) (φ : Polynomial ℝ) (hdeg : φ.natDegree < n) :
    (∫ x in (0 : ℝ)..butcherShiftedLegendre_zeros n i, φ.eval x)
      = ∑ j : Fin n,
          butcherShiftedLegendre_collocationA n i j *
          φ.eval (butcherShiftedLegendre_zeros n j)
```

**Proof recipe** (verbatim port of cycle 303's
`butcherShiftedLegendre_quadrature_exact_lt_n`,
`Section342.lean:6249-6281`):

1. `set v : Fin n → ℝ := butcherShiftedLegendre_zeros n` and `hv :
   Function.Injective v` from `butcherShiftedLegendre_zeros_injective n`
   (cycle 302).
2. `hdecomp : φ = ∑ j, C (φ.eval (v j)) * Lagrange.basis univ v j`
   via `Lagrange.eq_interpolate` with degree side condition
   `φ.degree < (Finset.univ : Finset (Fin n)).card` discharged by
   `Finset.card_univ + Fintype.card_fin + Polynomial.degree_eq_natDegree`.
3. `conv_lhs => rw [hdecomp]`; `simp_rw [Polynomial.eval_finset_sum,
   eval_mul, eval_C]`.
4. `rw [intervalIntegral.integral_finset_sum]` to swap integral and
   sum (integrability witness:
   `Continuous.intervalIntegrable (continuous_const.mul (Polynomial.continuous _)) _ _`).
5. `Finset.sum_congr rfl; intro j _; rw [intervalIntegral.integral_const_mul,
   butcherShiftedLegendre_collocationA]; ring`.

**Key adaptation from cycle 303**: the integration bounds are now
`(0 : ℝ)..butcherShiftedLegendre_zeros n i` instead of `(0 : ℝ)..1`.
This propagates verbatim through the `intervalIntegral.integral_*`
API — none of those lemmas care about the specific bounds, only that
the integrand satisfies the named regularity conditions. The
`butcherShiftedLegendre_collocationA` definition unfolds to exactly
the per-`j` `∫₀^{cᵢ} Lⱼ` factor needed for the final `ring` step.

**Placement**: insert as a new public theorem in a new `/-! ### Phase
3.1 — collocation A-matrix exactness on `[0, cᵢ]` -/` block. Place
after the cycle 308/309 Phase 2 block (i.e. after the cycle 309
`butcherGaussLegendreRK_satisfiesB` headline, plus its non-vacuity
witnesses, but before any §342 trailing closure remarks). Do NOT
modify the existing cycle 303 / 304 / 308 / 309 declarations.

### P2 — `butcherGaussLegendreRK_satisfiesC` (~40 LOC)

**Statement**:

```lean
theorem butcherGaussLegendreRK_satisfiesC (n : ℕ) :
    (butcherGaussLegendreRK n).SatisfiesC n
```

Note: `SatisfiesC` quantifies over `∀ i : Fin s, ∀ k : ℕ, 1 ≤ k →
k ≤ ξ`; for `n = 0` the universal-on-`Fin 0` `∀ i` clause is vacuous,
so **no `0 < n` hypothesis is required** (unlike the B(2n) case at
cycle 309 §A.3, which only has `∀ k`). This is a strengthening over
the cycle 309 B(2n) corollary's signature; verify by attempting the
bare statement first.

**Proof recipe**:

1. `intro i k h1 hk`. Goal:
   `∑ j, _collocationA n i j * _zeros n j ^ (k - 1) = _zeros n i ^ k / k`.
2. `show ∑ j : Fin n, butcherShiftedLegendre_collocationA n i j *
   butcherShiftedLegendre_zeros n j ^ (k - 1) = _zeros n i ^ k / k`
   (mirror cycle 309 §A.3 — `M.A` / `M.c` projections unfold
   definitionally for `M := butcherGaussLegendreRK n`).
3. Set `φ := Polynomial.X ^ (k - 1) : Polynomial ℝ`. Apply P1 with
   this `φ`:
   `have h_exact := butcherShiftedLegendre_collocation_exact_lt_n n i φ ?_`
   where the side condition `φ.natDegree < n` is discharged via
   `Polynomial.natDegree_X_pow + omega` (gives `k - 1 < n`, which holds
   since `k ≤ n` and `k ≥ 1`).
4. The LHS of `h_exact` is `∫ x in (0 : ℝ)..(_zeros n i), x^(k-1)`.
   Compute via `intervalIntegral.integral_pow` (Mathlib gives
   `∫ x in a..b, x^k = b^(k+1)/(k+1) - a^(k+1)/(k+1)`).
   At `a = 0`, `b = _zeros n i`, exponent `k - 1`:
   `∫ x in 0..(_zeros n i), x^(k-1) = (_zeros n i)^((k-1)+1) / ((k-1)+1)
                                       - 0^((k-1)+1) / ((k-1)+1)`.
   Need `Nat.sub_add_cancel h1` to bridge `(k - 1) + 1 = k` (cycle 307
   precedent: `Section342.lean:6755`).
5. The RHS of `h_exact`'s sum: per-`j` term is `_collocationA n i j *
   φ.eval (_zeros n j)`; `φ.eval (_zeros n j) = (_zeros n j)^(k-1)`
   via `Polynomial.eval_pow + Polynomial.eval_X`.
6. The `0^k = 0` simplification on the LHS (need `k ≥ 1`); use
   `Nat.zero_pow (by omega : 0 < k)` or `pow_succ`-based simp.
7. Combine LHS = RHS via `linarith` (or a final `linear_combination
   h_exact` after the LHS/RHS rewrites). The outcome is exactly the
   `_zeros n i ^ k / k` shape on the RHS of the goal.

### P3 (stretch, only if P1+P2 close cleanly) — non-vacuity witnesses

* **P3.a**: `(butcherGaussLegendreRK 1).SatisfiesC 1` round-trip
  through cycle 308's `butcherGaussLegendreRK_one_eq_gaussLegendre1Stage`,
  then `interval_cases k; simp [gaussLegendre1Stage]` (mirror cycle 308
  `B(2)` example at `Section342.lean:6907`). Confirms the `n = 1`
  case matches §321's hand-built `gaussLegendre1Stage` SatisfiesC 1
  example. Or simpler: `exact butcherGaussLegendreRK_satisfiesC 1`.
* **P3.b**: `(butcherGaussLegendreRK 2).SatisfiesC 2` (the n=2
  non-vacuity witness, mirroring cycle 309 §A.4's B(4) at n=2).
  Discharged by `exact butcherGaussLegendreRK_satisfiesC 2`. Or, for
  a more substantive sanity check, expand at one specific `(i, k)`
  pair and verify by direct computation.

### P4 — bookkeeping (mandatory after P1+P2 land)

* `extraction/formalization_data/lean_status.json`: leave `cor:342D`
  as `unformalized` (still no end-to-end statement of cor:342D is
  shipped — only B(2n) and C(n) infrastructure).
* `plan.md`: update the §342 cluster log paragraph (the verbose
  multi-line entry under `lem:342A`) with the cycle 310 progress
  note; the `cor:342D` row stays `[ ]`.
* `task_results/cycle_310.md`: standard format, document any P3
  outcomes.

## §C — Pre-flight verification (do this first, ~5 min)

1. `Read OpenMath/Chapter3/Section342.lean` lines 6249-6281 (cycle 303's
   recipe — the canonical template).
2. `Read OpenMath/Chapter3/Section342.lean` lines 6840-6862 (cycle 308's
   `_collocationA` def + `_one_apply` example).
3. `lean_local_search "intervalIntegral.integral_pow"` to confirm the
   exact lemma name and signature (Mathlib API may differ between
   `0..b` and `a..b` forms).
4. `lean_local_search "Polynomial.natDegree_X_pow"` to confirm
   (alternative: `Polynomial.natDegree_pow` plus `Polynomial.natDegree_X`).

## §D — Risk register

### R1 (LOW): `intervalIntegral.integral_finset_sum` over generic upper bound

The cycle 303 recipe uses this for `[0, 1]`. The lemma's signature
is *bound-agnostic*; verify by reading
`Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`. If for any
reason the lemma is restricted, the workaround is `Finset.induction`
with `intervalIntegral.integral_add` per step.

### R2 (LOW): integrability witness for the swap step

Cycle 303 uses `Continuous.intervalIntegrable (continuous_const.mul
(Polynomial.continuous _)) _ _`. Same form should work; bounds are
arbitrary reals. If issues: verify `Polynomial.continuous` produces
a `Continuous` (not `ContinuousOn`) instance — yes per
`Mathlib.Topology.Algebra.Polynomial`.

### R3 (LOW): `Lagrange.eq_interpolate` degree side condition

Cycle 303's recipe uses
`((Finset.univ : Finset (Fin n)).card : WithBot ℕ)` after
`Finset.card_univ + Fintype.card_fin`. Same form here; identical
universe / type plumbing. Should port verbatim.

### R4 (MEDIUM): `0^k = 0` for `k ≥ 1` in the RHS evaluation

When evaluating `(0 : ℝ)^k / k - 0` where `k = (k_orig - 1) + 1`,
the `0^k` term needs `k ≥ 1` to evaluate to 0. Use
`Nat.zero_pow (by omega)` or `pow_zero`-aware simp lemma. Confirm
behaviour: `(0 : ℝ)^0 = 1`, `(0 : ℝ)^(succ _) = 0`. Be careful that
the cast handling doesn't trip on `(k : ℝ)` vs `(k : ℕ)` in the
exponent.

### R5 (MEDIUM): `(k - 1) + 1 = k` cast bridging

In Lean 4, `Nat.sub_add_cancel h1` (where `h1 : 1 ≤ k`) gives
`(k - 1) + 1 = k`. Cycle 307's precedent at line 6755 uses this
exactly. May need to thread through `pow_succ` / `Polynomial.eval_pow`
carefully. **Memory hint**: from
`feedback_fin_sum_univ_succ_coerce.md`, similar cast issues are
resolved by prepending `show` to coerce the binder type
definitionally — apply if needed.

### R6 (LOW): `SatisfiesC`'s nested `∀ i, ∀ k` quantifier order

Cycle 309 §A.3's `B(2n)` recipe used `intro k h1 hk; show ...;
exact ...`. The `C(n)` predicate adds `∀ i` first:
`intro i k h1 hk; show ...; ...`. Don't forget the `i` binder.

### R7 (LOW, but real): no `0 < n` hypothesis on `SatisfiesC`

Note that for `n = 0`, the `∀ i : Fin 0` quantifier is empty, so
`SatisfiesC 0` is vacuous regardless of `n` value. Cycle 309's B(2n)
needed `0 < n` to exclude the degenerate case in cycle 307's bridge.
The C(n) version may NOT need it (since `Fin 0` is empty), but if P1
turns out to need `0 < n` (because cycle 304's analog at line 6332
requires it), then P2 will need it too. Safe move: try without
`0 < n` first; add if needed. If P1 needs `0 < n`, P2's signature
becomes `(n : ℕ) (hn : 0 < n) : SatisfiesC n`.

## §E — What NOT to do

* **Do NOT pivot to D(n) or E(n,n) this cycle.** Per the cycle 309
  task results §F bullet 3, the textbook B(2n) + C(n) ⇒ D(n)
  derivation routes through a *separate* algebraic argument that
  needs its own cycle. Do not attempt as a stretch.
* **Do NOT attempt `cor:342D` directly this cycle.** It needs all of
  B(2n), C(n), D(n), and the §314A elementary-weight argument. C(n)
  is one step in a longer chain.
* **Do NOT modify cycle 303's
  `butcherShiftedLegendre_quadrature_exact_lt_n`** — duplicate the
  proof body for the new theorem, do not refactor (a parametric
  abstraction over the upper bound is tempting but complicates cycle
  304's downstream consumer; defer that refactor).
* **Do NOT attempt to close the cycle 301 upstream `sorryAx` leak**
  this cycle. The leak is pre-existing and propagates through all
  §342 theorems consuming `_zeros`; cleanup is a separate audit cycle
  per cycle 309 §G.
* **Do NOT use `Polynomial.ext` or `funext` skeletons** for any of
  the polynomial identities — the cycle 308/309 pattern of `show ...;
  exact ...` against named lemmas is the canonical recipe and should
  port directly.
* **Do NOT introduce `axiom` / `constant` declarations**.
* **Do NOT raise `maxHeartbeats` above 200000**. Per CLAUDE.md.
  Cycle 303's recipe was ~30 LOC and compiled within default budget;
  the verbatim port should too.
* **Do NOT submit to Aristotle this cycle.** P1 is a verbatim port of
  cycle 303 (~80 LOC) and P2 is a 40-LOC corollary; both are well
  within manual cycle budget. Aristotle's slot is better reserved for
  the multi-cycle D(n) / `cor:342D` work later.
* **Do NOT introduce `sorry`.** Sorry-first scaffolds for multi-cycle
  closures get rolled back by precedent (cycles 138/139, 149/150,
  200/201). Cycle 310's deliverables P1 and P2 must close axiom-clean
  in a single cycle, or be deferred entirely with no scaffold left
  behind.
* **Do NOT pivot to a fresh entity** (e.g. `thm:351B`, `lem:359A`)
  without strong reason. The §342 cluster has 12 cycles of momentum
  and one more clean ship gets us most of the way to `cor:342D`.

## §F — Single-cycle close-criteria

Cycle 310 ships if:

* P1 lands axiom-clean (`[propext, Classical.choice, Quot.sound]`
  modulo the cycle 301 upstream `sorryAx` leak — same profile as
  cycles 307/308/309).
* P2 lands axiom-clean.
* Sorry count remains 0 in committed code.
* `lake env lean OpenMath/Chapter3/Section342.lean` exits 0.

P3 stretch (a or b or both) is a bonus, not gating.

## §G — Why this is the right cycle 310 target

* **Highest-leverage**: closes another quarter of `cor:342D`,
  bringing the §342 ↔ §321 lift to ~67% complete. After cycle 310
  only D(n) and E(n,n) remain, which together close `cor:342D`
  modulo the §314A elementary-weight argument (a separate, planned
  multi-cycle effort).
* **Mechanical port**: the proof is literally cycle 303's recipe
  with one parameter changed. Risk profile is LOW across the board
  (R1–R7 above all rated LOW or MEDIUM, with concrete mitigations).
* **Independent of multi-cycle blockers**: does NOT need the cycle
  301 sorryAx cleanup, does NOT need any other §342 infrastructure
  beyond what's already shipped.
* **Sets up D(n)**: with C(n) in hand, the standard B(2n)+C(n)⇒D(n)
  derivation (Hairer–Wanner I.7.5 / Butcher §342) becomes a
  one-cycle algebraic argument in cycle 311+.

## §H — Mandatory closing actions for cycle 310

1. `task_results/cycle_310.md` — standard format, document P1 + P2
   axiom verification, P3 status, faithfulness checks for both new
   theorems, and any pitfalls hit.
2. Update `plan.md` `lem:342A` follow-up paragraph (the verbose
   §342 cluster log) with cycle 310 progress entry.
3. Verify cycle-309 landmark theorems still axiom-clean
   (`butcherGaussLegendreRK_satisfiesB`, `butcherGaussLegendreRK`,
   `_one_eq`) via `lean_verify` — no regression.
4. Commit with message `Cycle 310 — §342 collocation exactness on
   [0, cᵢ] + cor:342D Phase 3.1 (C(n)).`
