# Cycle 323 Strategy — §344 Phase D.3: Lobatto IIIA `s = 2` `RKTableau`

## §A. Pre-flight: state of the work

Cycle 322 closed Phase D.2 (Radau IIA `s = 1` `RKTableau`): three new
public symbols (`butcherRadauII_collocationA_one`,
`butcherRadauIIA_one`, `butcherBackwardEulerRK`) + one coincidence
theorem (`butcherRadauIIA_one_eq_backwardEuler`) + one `SatisfiesB 1`
non-vacuity example, all axiom-clean. Section344.lean: 1158 → 1247
LOC, **0 explicit sorries**.

The cycle 322 task results explicitly recommend **Lobatto IIIA `s = 2`
(trapezoidal rule)** as the cycle 323 target. This is the natural
two-stage extension of the Radau IIA `s = 1` ship and exercises the
collocation-A-matrix machinery at multiple entries for the first time.

## §B. Cycle 323 target — Lobatto IIIA `s = 2` `RKTableau`

### Textbook tableau (Butcher §344, Table 344(III))

Lobatto IIIA at `s = 2` is the **trapezoidal rule**:
- `c = (0, 1)` — already shipped as `butcherLobatto_zeros_two` (cycle 320).
- `b = (1/2, 1/2)` — already shipped as `butcherLobatto_quadratureWeights_two` (cycle 321).
- `A = !![0, 0; 1/2, 1/2]` — to be computed in this cycle.

### §B.1 — define the collocation A-matrix

```lean
/-- The Lobatto IIIA collocation A-matrix at `s = 2`. Entry `(i, j)` is
the integral of the j-th Lagrange basis polynomial (over the two-leaf
abscissae `c = (0, 1)`) over `[0, c_i]`. -/
noncomputable def butcherLobatto_collocationA_two
    (i j : Fin 2) : ℝ :=
  ∫ x in (0 : ℝ)..butcherLobatto_zeros_two i,
    (Lagrange.basis Finset.univ butcherLobatto_zeros_two j).eval x
```

Place immediately after `butcherLobatto_quadratureWeights_two_apply_one`
in Section344.lean (the natural sequel to the cycle 321 weight machinery).

### §B.2 — close the four entries

Four cases via a single `fin_cases` theorem:

| `(i, j)` | upper limit `c_i` | integrand | value |
|---|---|---|---|
| `(0, 0)` | `0` | `1 - x` | `0` (vacuous: `∫₀⁰`) |
| `(0, 1)` | `0` | `x` | `0` (vacuous) |
| `(1, 0)` | `1` | `1 - x` | `1/2` |
| `(1, 1)` | `1` | `x` | `1/2` |

Recommended shape: ship **four separate `_apply` theorems** for clarity
and downstream reusability, mirroring cycle 321's
`butcherLobatto_quadratureWeights_two_apply_zero/_one` split:

```lean
theorem butcherLobatto_collocationA_two_apply_zero_zero :
    butcherLobatto_collocationA_two 0 0 = 0 := by
  unfold butcherLobatto_collocationA_two
  show ∫ x in (0 : ℝ)..butcherLobatto_zeros_two 0,
        (Lagrange.basis Finset.univ butcherLobatto_zeros_two 0).eval x = 0
  simp [butcherLobatto_zeros_two, intervalIntegral.integral_same]

theorem butcherLobatto_collocationA_two_apply_zero_one : ... -- analogous

theorem butcherLobatto_collocationA_two_apply_one_zero :
    butcherLobatto_collocationA_two 1 0 = 1/2 := by
  unfold butcherLobatto_collocationA_two
  -- upper limit = c_1 = 1
  -- integrand = L_0(x) = (x - 1) / (0 - 1) = 1 - x
  -- ∫₀¹ (1 - x) dx = 1 - 1/2 = 1/2
  -- Use cycle 321's recipe: unfold Lagrange.basis on the singleton erase,
  -- close via integral_sub/integral_one/integral_id/norm_num.
  sorry  -- to be filled in following the cycle 321
         -- _quadratureWeights_two_apply_zero pattern

theorem butcherLobatto_collocationA_two_apply_one_one : ... -- analogous, value 1/2
```

For the `i = 0` cases, `intervalIntegral.integral_same` closes
directly. For the `i = 1` cases, follow cycle 321's pattern exactly
(the integrands are identical to those used in the `_quadratureWeights_two`
proofs since `c_1 = 1` matches the standard `[0, 1]` integration range).

### §B.3 — assemble the `RKTableau 2`

```lean
noncomputable def butcherLobattoIIIA_two : RKTableau 2 where
  A := butcherLobatto_collocationA_two
  b := butcherLobatto_quadratureWeights_two
  c := butcherLobatto_zeros_two
```

### §B.4 — direct trapezoidal `RKTableau` for cross-validation

Following the cycle 322 `butcherBackwardEulerRK` precedent:

```lean
noncomputable def butcherTrapezoidalRK : RKTableau 2 where
  A := !![0, 0; 1/2, 1/2]
  b := ![1/2, 1/2]
  c := ![0, 1]
```

**Verify field shapes first** by reading cycle 322's `butcherBackwardEulerRK`
in Section344.lean — the `b` and `c` fields are `Fin s → ℝ`, not column
matrices. Use `![a, b]` (Mathlib's `Matrix.of` notation) for `Fin 2 → ℝ`
or the more explicit `fun i => match i with | 0 => a | 1 => b` form.

### §B.5 — coincidence theorem

```lean
theorem butcherLobattoIIIA_two_eq_trapezoidal :
    butcherLobattoIIIA_two = butcherTrapezoidalRK := by
  apply RKTableau.mk.injEq.mpr
  refine ⟨?_, ?_, ?_⟩
  · -- A field: four-entry match
    ext i j
    fin_cases i <;> fin_cases j
    · show butcherLobatto_collocationA_two 0 0 = _
      rw [butcherLobatto_collocationA_two_apply_zero_zero]; rfl
    · show butcherLobatto_collocationA_two 0 1 = _
      rw [butcherLobatto_collocationA_two_apply_zero_one]; rfl
    · show butcherLobatto_collocationA_two 1 0 = _
      rw [butcherLobatto_collocationA_two_apply_one_zero]; norm_num
    · show butcherLobatto_collocationA_two 1 1 = _
      rw [butcherLobatto_collocationA_two_apply_one_one]; norm_num
  · -- b field: cite cycle 321's weight applies
    funext i; fin_cases i
    · exact butcherLobatto_quadratureWeights_two_apply_zero
    · exact butcherLobatto_quadratureWeights_two_apply_one
  · -- c field: pattern-matched _zeros_two reduces by rfl
    funext i; fin_cases i <;> rfl
```

### §B.6 — `SatisfiesB 2` non-vacuity example

```lean
example : butcherLobattoIIIA_two.SatisfiesB 2 := by
  rw [butcherLobattoIIIA_two_eq_trapezoidal]
  intro k h1 hk
  interval_cases k
  · -- k = 1: ∑ⱼ bⱼ · cⱼ^0 = ∑ⱼ bⱼ = 1
    simp [butcherTrapezoidalRK, Fin.sum_univ_two]; norm_num
  · -- k = 2: ∑ⱼ bⱼ · cⱼ^1 = (1/2)·0 + (1/2)·1 = 1/2
    simp [butcherTrapezoidalRK, Fin.sum_univ_two]; norm_num
```

## §C. LOC budget

| Block | Estimate |
|---|---|
| `butcherLobatto_collocationA_two` def | ~5 LOC |
| Four `_apply` theorems | ~60 LOC (15 each, the `i=1` cases dominate) |
| `butcherLobattoIIIA_two` def | ~5 LOC |
| `butcherTrapezoidalRK` def | ~10 LOC |
| Coincidence theorem | ~30 LOC |
| `SatisfiesB 2` example | ~10 LOC |
| **Total** | **~120 LOC** (Section344: 1247 → ~1370) |

Cycle 322 came in at +89 LOC for a one-entry tableau. The four-entry
A-matrix is the dominant addition; the rest scales linearly.

## §D. Fallback — if §B over-budget

If the four `_apply` proofs eat the cycle budget, ship only:
1. `butcherLobatto_collocationA_two` def.
2. The four `_apply` theorems.

Defer §B.3–B.6 (assembly + coincidence + non-vacuity) to cycle 324.
This is the cycle 321/322 split pattern: definition + apply theorems
first, RKTableau assembly second.

LOC for fallback: ~65 LOC.

## §E. Verification protocol

1. `lake env lean OpenMath/Chapter3/Section344.lean` — clean exit.
2. `lake env lean OpenMath/Chapter3.lean` — aggregator clean.
3. `grep -c sorry OpenMath/Chapter3/Section344.lean` → 0.
4. `#print axioms` on each new public symbol → `[propext, Classical.choice, Quot.sound]`.
5. Update `plan.md` thm:344A row to record cycle 323 closure.
6. **No** `lean_status.json` change this cycle — `thm:344A` remains
   `partial` since Phase B.2 (polynomial-exactness) is still open
   and the Phase D ladder is not exhaustive.

## §F. Faithfulness checklist

For each new `def`/`theorem`:

### `butcherLobatto_collocationA_two`
- Textbook reference: Butcher §344 Table 344(III), Lobatto IIIA at `s = 2`.
- Definition matches `∫₀^{c_i} L_j(x) dx` exactly (the canonical collocation
  recipe used at cycle 308 for Gauss–Legendre and cycle 322 for Radau IIA).
- No definition smuggling: the recipe is the literal textbook one.

### Each `_apply` theorem
- Tautology check: hypothesis-free; conclusion `... = 0` or `... = 1/2`
  is not a hypothesis re-export.
- Identity check: proofs route through `intervalIntegral.integral_same`
  (`i = 0` cases) or substantive integration computations (`i = 1` cases),
  not `exact h` or single rewrites.
- Hypothesis strength: no hypotheses; minimal signatures.

### `butcherTrapezoidalRK`
- Faithful to the textbook trapezoidal rule. Implicit stage equation
  `Y₀ = y₀`, `Y₁ = y₀ + (h/2)·(f(Y₀) + f(Y₁))`. Output
  `y₁ = y₀ + (h/2)·(f(Y₀) + f(Y₁)) = Y₁`. Recovers
  `y₁ = y₀ + (h/2)·(f(y₀) + f(y₁))`, the standard trapezoidal rule.

### `butcherLobattoIIIA_two_eq_trapezoidal`
- Tautology check: structure equality across two independently-defined
  tableaux, not a hypothesis re-export.
- Identity check: proof routes through four substantive `_apply` calls
  + two cycle-321 weight applies + four `rfl` reductions; no single
  `exact h`.
- Faithfulness: textbook identification of Lobatto IIIA `s = 2` with
  the trapezoidal rule (Butcher §344 Table 344(III); Hairer–Wanner
  Vol. II §IV.5).

## §G. What NOT to attempt

- **Do NOT** generalize to Lobatto IIIA `s = 3` (Simpson). The cycle 320
  `_zeros_three` + cycle 321 `_quadratureWeights_three` data IS
  available, but a 9-entry A-matrix is multi-cycle scope. Save for
  cycle 326+.
- **Do NOT** start Radau IIA `s = 2` in parallel. Keep the cycle focused
  on one tableau.
- **Do NOT** revisit Phase B.2 polynomial-exactness clauses
  (`2s − 2` for Radau, `2s − 3` for Lobatto). Blocked on
  polynomial-division infrastructure; multi-cycle scope.
- **Do NOT** touch §441 (43+ consecutive GPFS timeouts since cycle 182).
- **Do NOT** attempt the deferred `lem:310B` infrastructure path.
- **Do NOT** raise `maxHeartbeats` above 200000.
- **Do NOT** introduce `axiom`/`constant` declarations.
- **Do NOT** introduce sorries. Cycles 200/201, 138/139, 149/150
  rollback precedent: sorry-first scaffolds without single-cycle close
  get rolled back.

## §H. Failed approaches to avoid

From recent attempts.md / memory entries:

- **`Polynomial.ext + simp + ring`** for `Polynomial ℝ` constant
  arithmetic — `ring` cannot fold `Polynomial.C` operations. Use
  `Polynomial.funext + ring` instead (cycle 180 pattern). Not directly
  relevant this cycle (no polynomial equalities), but keep in mind
  for any future small-`s` exactness-check work.
- **`simp only [Matrix.dotProduct]`** does not fire — `dotProduct`
  lives at the root namespace, not `Matrix.dotProduct`. Use `show ∑ i, _`
  to expose the sum form (cycle 167 pattern). Not directly relevant
  this cycle.
- **`linarith` on large-rational hypotheses without `clear`** — only
  matters at extreme denominators (cycle 299's `_eleven_roots` IVT
  brackets had 76-quintillion denominators). The trapezoidal-rule
  rationals (`1/2`, `1`) are tiny; not relevant.
- **`Fin.sum_univ_succ` on `Fin s` sums where `s` doesn't reduce**
  (memory: `feedback_fin_sum_univ_succ_coerce.md`) — at concrete
  `s = 2` this is not an issue, but prepend `show (∑ i : Fin 2, …) = …`
  if the `simp` chain fails to unfold.

## §I. Confidence assessment

- **Risk: low.** The cycle 322 Radau IIA `s = 1` template is a direct
  precedent; the only structural change is scaling from 1×1 to 2×2.
  All prerequisites (`_zeros_two`, `_quadratureWeights_two`,
  `_quadratureWeights_two_apply_*`) are shipped and axiom-clean.
- **Risk: medium on the `i = 1` integration proofs.** The cycle 321
  pattern for `butcherLobatto_quadratureWeights_two_apply_zero/_one`
  is the exact precedent (same integrand, same integration range).
  Worker should open Section344.lean and read those proofs directly
  before writing the `_apply_one_zero`/`_apply_one_one` cases — they
  should be near-verbatim ports.

## §J. Cycle 324+ outlook

Successful cycle 323 closure unlocks:
- **Cycle 324**: Radau IIA `s = 2` (`c = (1/3, 1)`, `b = (3/4, 1/4)`,
  4-entry A-matrix). Same shape as cycle 323 but with non-trivial
  abscissa `1/3` requiring fractional-denominator integration.
- **Cycle 325**: Radau IA `s = 1` (forward Euler analogue) for left-
  endpoint symmetry.
- **Cycle 326+**: Lobatto IIIA `s = 3` (Simpson's rule, 9-entry A) or
  pivot to Phase B.2 polynomial-exactness if motivated by downstream
  consumers.

If cycle 323 ships only the §D fallback (def + applies, no assembly):
- **Cycle 324**: complete the Lobatto IIIA `s = 2` assembly +
  coincidence + non-vacuity. Then cycle 325 starts Radau IIA `s = 2`.

## §K. Quick-reference Mathlib hooks

| Goal | Hook | Notes |
|---|---|---|
| `∫_a^a f = 0` | `intervalIntegral.integral_same` | direct |
| `∫₀¹ x dx = 1/2` | `integral_id` (or cycle 321 ladder) | `cycle 321 pattern` |
| `∫₀¹ 1 dx = 1` | `intervalIntegral.integral_const` + `smul_eq_mul` | `cycle 321 pattern` |
| `∫₀¹ (1-x) dx = 1/2` | `integral_sub` + `integral_one` + `integral_id` | follow cycle 321 |
| Lagrange basis at singleton | `Lagrange.basis_singleton` | for the `i = 0` cases the basis pre-collapses |
| Lagrange basis with one erase | `Lagrange.basisDivisor` decomposition | cycle 321 pattern |
| `RKTableau` field equality | `RKTableau.mk.injEq` | cycle 322 pattern |
| `Matrix.of` via `!![..]` | `Matrix.of_apply` | for `A` field of `butcherTrapezoidalRK` |

## §L. Concrete first actions for the worker

1. **Read** `OpenMath/Chapter3/Section344.lean` around the cycle 321
   `butcherLobatto_quadratureWeights_two_apply_zero` proof to learn the
   exact tactic chain for `∫₀¹ (1-x) dx = 1/2` style integrals.
2. **Read** the cycle 322 `butcherRadauIIA_one_eq_backwardEuler` proof
   for the `RKTableau.mk.injEq` decomposition pattern.
3. Ship §B.1 (def) + §B.2 (four `_apply`s).
4. Verify the def + applies compile clean before proceeding to §B.3–B.6.
5. Ship §B.3 (Lobatto IIIA tableau) + §B.4 (trapezoidal direct form).
6. Ship §B.5 (coincidence) + §B.6 (`SatisfiesB 2` example).
7. Run §E verification protocol.
8. Write `task_results/cycle_323.md` documenting deliverables + axioms
   + non-vacuity + faithfulness check.
9. Update `plan.md` thm:344A row.
10. Commit and push.
