# Strategy — Cycle 317

## State entering this cycle

- §342 `lem:342A` fully closed (cycles 271–301; seven properties (342a)–(342g)).
- §342 `thm:342C` "purely algebraic" cluster fully shipped: (342m), (342n), (342o), (342p) closed in cycles 313/316/314/315. All axiom-clean.
- §342 `cor:342D` partial: §321 simplifying assumptions B(2n)/C(n)/D(n)/E(n,n) for the canonical Gauss–Legendre tableau all shipped (cycles 309–312). Full end-to-end iff still blocked on remaining (342j/k/l) G(2s) clauses, which require `thm:314A` elementary-differential infrastructure (multi-cycle).
- §342 has been the predominant focus for **46 consecutive cycles** (271–316).
- No sorries anywhere, no Aristotle pending, no blockers escalated.
- Cycle 316 worker explicitly recommended `thm:344A` as next.

## Decision: pivot to `thm:344A` Phase A (open §344)

Rationale:
1. `thm:344A` directly extends the §342 Gaussian quadrature work to Radau and Lobatto quadrature families — natural continuation that reuses cycles 271–316 infrastructure heavily.
2. Phase A scope mirrors cycle 271's successful opening of §342 (polynomial def + basic endpoint property + small-n witnesses) — known-good template.
3. Clean dependencies: only `lem:342A` properties (342a)/(342b)/(342c)/(342e), all shipped.
4. Single-cycle ship achievable; multi-cycle follow-up plan is straightforward (cycles 318+: degree exactness, weights, RKTableau lifts, mirroring §342's cycle 281+/308+ trajectory).
5. Continuing in §342 has no remaining tractable single-cycle work (G(2s) blocked on `thm:314A`).

## Target deliverables (this cycle)

Open new file `OpenMath/Chapter3/Section344.lean` (namespace `OpenMath.Chapter3.Section344`) with the following axiom-clean deliverables.

### Deliverable A — Polynomial family definitions (~50 LOC)

Three `noncomputable def`s:

```lean
/-- The Radau I polynomial `P_s^* + P_{s-1}^*` whose roots in [0,1] are the
Radau I quadrature abscissae. Has `s` as `natDegree` and `0` as one root
for `s ≥ 1`. -/
noncomputable def butcherRadauI (s : ℕ) : Polynomial ℝ :=
  butcherShiftedLegendre s + butcherShiftedLegendre (s - 1)

/-- The Radau II polynomial `P_s^* - P_{s-1}^*` whose roots in [0,1] are
the Radau II quadrature abscissae. Has `s` as `natDegree` and `1` as one
root for `s ≥ 1`. -/
noncomputable def butcherRadauII (s : ℕ) : Polynomial ℝ :=
  butcherShiftedLegendre s - butcherShiftedLegendre (s - 1)

/-- The Lobatto polynomial `P_s^* - P_{s-2}^*` whose roots in [0,1] are
the Lobatto quadrature abscissae. Has `s` as `natDegree` (for `s ≥ 2`)
and both `0` and `1` as roots. -/
noncomputable def butcherLobatto (s : ℕ) : Polynomial ℝ :=
  butcherShiftedLegendre s - butcherShiftedLegendre (s - 2)
```

Notes:
- `s - 1` and `s - 2` use ℕ truncated subtraction. Theorems below carry
  `0 < s` (Radau) or `2 ≤ s` (Lobatto) hypotheses to rule out degenerate
  cases.
- At `s = 1`: `butcherRadauI 1 = P_1^* + P_0^* = (2X - 1) + 1 = 2X`. Has
  root at 0. ✓
- At `s = 1`: `butcherRadauII 1 = P_1^* - P_0^* = (2X - 1) - 1 = 2X - 2`.
  Has root at 1. ✓
- At `s = 2`: `butcherLobatto 2 = P_2^* - P_0^* = (6X² - 6X + 1) - 1 = 6X² - 6X = 6X(X - 1)`.
  Has roots at 0 and 1. ✓

### Deliverable B — Endpoint vanishing (~80 LOC, four theorems)

Each follows a 3–7 line template: unfold + `Polynomial.eval_add` / `eval_sub` + cycle 271's `butcherShiftedLegendre_eval_one` and cycle 273's `butcherShiftedLegendre_eval_zero` + parity collapse.

```lean
/-- Radau I polynomial vanishes at 0: `(P_s^* + P_{s-1}^*)(0) = 0` for `s ≥ 1`.
Computation: `P_s^*(0) = (-1)^s` and `P_{s-1}^*(0) = (-1)^{s-1}`, sum to 0. -/
theorem butcherRadauI_eval_zero (s : ℕ) (hs : 0 < s) :
    (butcherRadauI s).eval 0 = 0

/-- Radau II polynomial vanishes at 1: `(P_s^* - P_{s-1}^*)(1) = 0` for `s ≥ 1`.
Computation: `P_s^*(1) = 1` and `P_{s-1}^*(1) = 1`, subtract to 0. -/
theorem butcherRadauII_eval_one (s : ℕ) (hs : 0 < s) :
    (butcherRadauII s).eval 1 = 0

/-- Lobatto polynomial vanishes at 0: `(P_s^* - P_{s-2}^*)(0) = 0` for `s ≥ 2`.
Computation: `P_s^*(0) = (-1)^s` and `P_{s-2}^*(0) = (-1)^{s-2} = (-1)^s`,
subtract to 0. -/
theorem butcherLobatto_eval_zero (s : ℕ) (hs : 2 ≤ s) :
    (butcherLobatto s).eval 0 = 0

/-- Lobatto polynomial vanishes at 1: `(P_s^* - P_{s-2}^*)(1) = 0` for `s ≥ 2`.
Computation: `P_s^*(1) = 1` and `P_{s-2}^*(1) = 1`, subtract to 0. -/
theorem butcherLobatto_eval_one (s : ℕ) (hs : 2 ≤ s) :
    (butcherLobatto s).eval 1 = 0
```

**Critical parity-collapse helpers** (the only non-trivial proof step):

For Radau I's `(-1)^s + (-1)^(s-1) = 0`: use
`obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hs)`
to write `s = k + 1`, then `s - 1 = k`, and the sum becomes
`(-1)^(k+1) + (-1)^k = -(-1)^k + (-1)^k = 0`. Close with `pow_succ` + `ring`.

For Lobatto's `(-1)^s - (-1)^(s-2) = 0`: use
`obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs` (where `hs : 2 ≤ s`)
to write `s = 2 + k`, then `s - 2 = k`, and the difference becomes
`(-1)^(2+k) - (-1)^k = (-1)^k - (-1)^k = 0`. Close with `pow_add` +
`neg_one_sq` + `ring`.

**If `obtain` shape doesn't fire cleanly**, the backup recipe is
`Nat.sub_add_cancel hs` + `← pow_succ` + manual case-split, OR
`Nat.even_or_odd s` + `Nat.even_sub` + `Nat.even_pow` (longer but
mechanical).

### Deliverable C — Small-n explicit forms (~80 LOC)

Concrete witnesses at `s ∈ {1, 2, 3}` verifying the formulas algebraically:

```lean
theorem butcherRadauI_one : butcherRadauI 1 = Polynomial.C 2 * Polynomial.X
theorem butcherRadauI_two : butcherRadauI 2 = -- compute via _two/_one
theorem butcherRadauII_one : butcherRadauII 1 = Polynomial.C 2 * Polynomial.X - Polynomial.C 2
theorem butcherRadauII_two : butcherRadauII 2 = -- compute
theorem butcherLobatto_two : butcherLobatto 2 = -- compute (= 6X² - 6X)
theorem butcherLobatto_three : butcherLobatto 3 = -- compute
```

Proof recipe (cycle 282+ template): `unfold butcherRadauI` (or others) +
`rw [butcherShiftedLegendre_zero, butcherShiftedLegendre_one, ...]` +
`ring` or `Polynomial.funext + ring`. Each closes in 3–5 lines.

Also include `example` non-vacuity blocks confirming the endpoint
theorems fire on the small-n explicit forms:

```lean
example : (butcherRadauI 1).eval 0 = 0 := by
  rw [butcherRadauI_one]; simp
```

### Deliverable D — Degree bounds (~30 LOC, three theorems)

```lean
/-- Radau I polynomial has `natDegree = s` for `s ≥ 1` (leading
coefficient comes from `P_s^*` since `P_{s-1}^*` has degree `s - 1 < s`). -/
theorem butcherRadauI_natDegree (s : ℕ) (hs : 0 < s) :
    (butcherRadauI s).natDegree = s

theorem butcherRadauII_natDegree (s : ℕ) (hs : 0 < s) :
    (butcherRadauII s).natDegree = s

theorem butcherLobatto_natDegree (s : ℕ) (hs : 2 ≤ s) :
    (butcherLobatto s).natDegree = s
```

Proof recipe: `Polynomial.natDegree_add_eq_left_of_natDegree_lt`
(or `_sub_` variant; verify name with `lean_local_search "natDegree_sub"`)
+ cycle 273's `butcherShiftedLegendre_natDegree`. If the sub-variant
doesn't exist directly, use `natDegree_add_eq_left_of_natDegree_lt` on
`P_s^* + (-P_{s-1}^*)` after `sub_eq_add_neg` rewrite, plus
`natDegree_neg`.

## Required imports for `Section344.lean`

```lean
import OpenMath.Chapter3.Section342
```

The `butcherShiftedLegendre` infrastructure (and its `Polynomial`
machinery from Mathlib) is the only dependency. No new Mathlib imports
expected.

## What NOT to attempt this cycle

1. **Do NOT** attempt the full `thm:344A` statement. The homotopy
   argument for `c_i ∈ [0, 1]` and `b_i > 0` is multi-cycle and requires:
   - Continuous-deformation arguments via `IntermediateValue` on the
     polynomial root multiset.
   - The "no weight vanishes" optimality contradiction using cycle
     292's `butcherShiftedLegendre_orthogonal_to_lower_degree`
     (basis-span lemma).
   - The Lobatto-specific s-odd middle-weight argument that uses
     (342f) recurrence (cycle 293's `butcherShiftedLegendre_recurrence`).
   This is genuinely multi-cycle — defer to cycle 320+ after Phase B
   (degree exactness) ships.

2. **Do NOT** attempt the polynomial-exactness theorems
   ("exact for polynomials of degree up to 2s - 2"). That's Phase B,
   requires polynomial division + orthogonality of the quotient `Q`
   against the Radau/Lobatto polynomial. Cycle 318+ target.

3. **Do NOT** attempt to build a `RKTableau` from these polynomials
   (the Radau IA / IIA, Lobatto IIIA/IIIB/IIIC tables from
   Table 344(I)). That requires defining Radau abscissae as roots, then
   constructing the collocation A-matrix and weights — mirrors cycles
   308–312 for Gauss–Legendre, multi-cycle.

4. **Do NOT** attempt `cor:342D` end-to-end iff. Still blocked on the
   G(2s) clauses requiring `thm:314A`. Document only.

5. **Do NOT** attempt `lem:359A` (V and W transformations). Requires
   orthonormal polynomial matrix `W` infrastructure not yet in repo —
   multi-cycle.

6. **Do NOT** attempt `lem:351A` (stability function determinant
   formula). Requires `RKTableau.stabilityFunction` rational-function
   definition not yet in repo. Worth doing in a future cycle but needs
   its own scoping document for the `R(z)` rational-function
   representation question (`Polynomial`-quotient vs `RatFunc` vs
   conditional `det(...)/det(...)` evaluation).

7. **Do NOT** raise `maxHeartbeats` above 200000. Each small theorem
   should close in well under the default; if any theorem stalls,
   factor into named per-coefficient helpers (cycle 274–278 pattern).

8. **Do NOT** introduce `sorry`/`axiom`/`constant`. Phase A
   deliverables must be axiom-clean
   (`[propext, Classical.choice, Quot.sound]`).

9. **Do NOT** submit anything to Aristotle this cycle. Each endpoint
   theorem is a 3–7 line manual proof, well within the cycle budget.
   Reserve Aristotle for Phase B/C (degree exactness, homotopy
   weight-positivity).

10. **Do NOT** name the Lobatto polynomial `butcherLobattoIII` or
    similar — Table 344(I) reserves "Lobatto III/IIIA/IIIB/IIIC" for
    the various RKTableau families built FROM Lobatto quadrature, not
    for the quadrature polynomial itself. Use `butcherLobatto` for the
    polynomial; reserve the suffixed names for the future tableau
    constructions (cycle 322+).

## Pitfalls to avoid (cycle 273+ learned lessons)

- **`Polynomial.ext` over rationals fails** when `ring` cannot fold
  `Polynomial.C` arithmetic. Use `Polynomial.funext + ring` instead
  (cycle 282 pattern, working at the evaluated-polynomial level).
- **`simp` over `Polynomial.coeff` for explicit small-n forms** is
  the cycle 273+ pattern; do NOT mix it with `ring`-on-`Polynomial`
  (cycle 276 dead end).
- **Nat-cast in `(-1)^(s-1)`**: Lean tries to interpret `s - 1` as
  ℕ truncated subtraction first; if `s = 0`, `s - 1 = 0` and the
  formula degenerates. Always guard with `hs : 0 < s` (Radau) or
  `2 ≤ s` (Lobatto).

## Pre-commit faithfulness checklist (mandatory)

For each new `def` (`butcherRadauI`, `butcherRadauII`, `butcherLobatto`):
- [ ] Open `extraction/formalization_data/entities/thm_344A.json` and confirm the textbook definitions match (Butcher §344 p. 244):
  > "x = 0 is a zero of P_s^* + P_{s-1}^* ... x = 1 is a zero of P_s^* − P_{s-1}^* ... x = 0 and x = 1 are zeros of P_s^* − P_{s-2}^*"
- [ ] Confirm the Lean type matches the textbook (a `Polynomial ℝ`).
- [ ] **Definition smuggling check**: each polynomial IS the literal
  sum/difference per the textbook recipe, NOT a stipulative definition
  of "the polynomial whose roots are the Radau/Lobatto abscissae".

For each new `theorem`:
- [ ] Tautology check: each endpoint theorem makes a non-trivial claim
  about polynomial evaluation, not an identity-of-hypothesis closer.
- [ ] Hypothesis strength: `0 < s` (Radau) and `2 ≤ s` (Lobatto) are
  minimal; weaker hypotheses make the statement degenerate or false.
- [ ] Absent theorem check: every theorem named in this strategy ships
  with a real body (no promised sorries).

For each small-n explicit form:
- [ ] Cross-check the closed form against textbook conventions.
  E.g. `butcherRadauI 1 = 2X` matches "Radau I quadrature with 1 stage
  at c_1 = 0" (the single root of 2X is 0). ✓
  `butcherLobatto 2 = 6X² - 6X = 6X(X-1)` matches "Lobatto quadrature
  with 2 stages at c_1 = 0, c_2 = 1". ✓

## Files to update at end of cycle

1. `OpenMath/Chapter3.lean` — add `import OpenMath.Chapter3.Section344` to the aggregator.
2. `extraction/formalization_data/lean_status.json` — bump `thm:344A` row from `unformalized` to `partial`, set `lean_file` to `OpenMath/Chapter3/Section344.lean`, set `lean_symbol` to one of the endpoint-vanishing theorems (e.g. `butcherRadauI_eval_zero`), and add a cycle 317 entry to the changelog.
3. `plan.md` — update `[ ] thm:344A` row to `[~]` with a one-line cycle 317 closure note: "Cycle 317 ships Phase A — polynomial definitions for Radau I, Radau II, Lobatto + endpoint vanishing + small-n explicit forms + degree bounds. Full theorem (homotopy for `c_i ∈ [0,1]` and `b_i > 0`) deferred."
4. `.prover-state/task_results/cycle_317.md` — full deliverable record per CLAUDE.md template, including the faithfulness check section quoting the textbook definitions for all three new polynomial defs.
5. If any deliverable stalls or the LOC budget overflows, write `.prover-state/issues/thm_344A_phase_A_scoping.md` documenting the remaining work for cycle 318+.

## LOC budget

Total estimate: ~240 LOC for the file (50 def + 80 endpoint + 80 small-n + 30 degree). Well within single-cycle scope.

**Abort threshold**: if the file exceeds ~350 LOC, ship only Deliverables A + B and defer C + D to cycle 318. The endpoint-vanishing theorems (Deliverable B) are the load-bearing Phase A content; small-n explicit forms (Deliverable C) and degree bounds (Deliverable D) are stretch.

## Cycle 318+ outlook (if Phase A lands cleanly)

Continuation plan for the §344 cluster (Phase B onward):
- **Cycle 318** (Phase B.1): more endpoint properties + cycle-292-style
  `butcherRadauI_orthogonal_to_lower_degree` basis-span lemma
  (analogous to cycle 292's shifted-Legendre version).
- **Cycle 319** (Phase B.2): polynomial-exactness theorem ("exact for
  polynomials of degree up to 2s - 2 for Radau, 2s - 3 for Lobatto") —
  uses Phase B.1 + polynomial-division decomposition.
- **Cycle 320** (Phase C.1): start the homotopy argument for `c_i ∈ [0, 1]`
  and `b_i > 0`. Multi-cycle; scope first via a dedicated
  `thm_344A_homotopy_plan.md` issue file.
- **Cycle 322+**: construct `butcherRadauIA_RKTableau`,
  `butcherRadauIIA_RKTableau`, `butcherLobattoIIIA_RKTableau`,
  `butcherLobattoIIIB_RKTableau`, `butcherLobattoIIIC_RKTableau` per
  Table 344(I) — mirrors cycles 308–312 for Gauss–Legendre.

This plan is not committed; cycle 318+'s planner re-scopes based on
cycle 317's actual outcome.
