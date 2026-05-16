# Cycle 318 Strategy — thm:344A Phase B.1 (Radau/Lobatto orthogonality)

## Target

`thm:344A` Phase B.1 — extend the §344 Radau/Lobatto polynomial families
(shipped cycle 317) with orthogonality properties analogous to cycle 292's
`butcherShiftedLegendre_orthogonal_to_lower_degree`. This is the natural
next step per cycle 317's "Suggested next approach" and unblocks Phase
B.2 (polynomial exactness) downstream.

## Why this target

* Cycle 317 just shipped clean infrastructure (3 polynomial defs, 4
  endpoint theorems, 6 small-s explicit forms, 3 degree bounds — all
  axiom-clean, ~280 LOC).
* The natural next step is orthogonality, which directly extends cycle
  292's basis-span machinery and uses exactly the cycle 317
  infrastructure.
* High infrastructure value: orthogonality + cycle 317's degree bounds
  set up the polynomial-exactness theorem of Phase B.2 cleanly via
  polynomial division.
* Single-cycle scope: ~150 LOC for three orthogonality theorems plus
  non-vacuity witnesses.

## Concrete deliverables

All three theorems live in `OpenMath/Chapter3/Section344.lean`,
appended after the cycle 317 content. They live in namespace
`OpenMath.Chapter3.Section344` (already opened by cycle 317).

### Deliverable 1 — `butcherRadauI_orthogonal_to_lower_degree`

```lean
theorem butcherRadauI_orthogonal_to_lower_degree (s : ℕ) (hs : 1 ≤ s)
    (q : Polynomial ℝ) (hq : q.natDegree < s - 1) :
    ∫ x in (0 : ℝ)..1, (butcherRadauI s).eval x * q.eval x = 0
```

**Proof recipe:**

1. Unfold `butcherRadauI s = P_s^* + P_{s-1}^*` via `simp only
   [butcherRadauI]` (or `show` rewrite, whichever is cleaner).
2. Distribute the integrand: `(P_s^* + P_{s-1}^*).eval x * q.eval x =
   P_s^*.eval x * q.eval x + P_{s-1}^*.eval x * q.eval x` via
   `Polynomial.eval_add` and `add_mul`.
3. Split the integral via `intervalIntegral.integral_add` (need
   integrability of each summand — both polynomials are continuous,
   so `Polynomial.continuous _ |>.mul (Polynomial.continuous _) |>.intervalIntegrable`).
4. Each summand is `0` by `butcherShiftedLegendre_orthogonal_to_lower_degree`
   (cycle 292) at `m := s` (with `hq : q.natDegree < s - 1 < s`) and
   `m := s - 1` (with `hq : q.natDegree < s - 1` directly).
5. `0 + 0 = 0` closes.

The `q.natDegree < s - 1` hypothesis discharges:
* `q.natDegree < s` for the `P_s^*` summand: via `Nat.lt_of_lt_of_le
  hq (Nat.sub_le s 1)` or `omega` (Nat truncated subtraction:
  `s - 1 ≤ s`).
* `q.natDegree < s - 1` for the `P_{s-1}^*` summand: directly.

### Deliverable 2 — `butcherRadauII_orthogonal_to_lower_degree`

```lean
theorem butcherRadauII_orthogonal_to_lower_degree (s : ℕ) (hs : 1 ≤ s)
    (q : Polynomial ℝ) (hq : q.natDegree < s - 1) :
    ∫ x in (0 : ℝ)..1, (butcherRadauII s).eval x * q.eval x = 0
```

**Proof recipe:** verbatim copy of Deliverable 1's recipe, swapping
`add` → `sub` everywhere:
* `Polynomial.eval_sub`, `sub_mul`
* `intervalIntegral.integral_sub`
* `0 - 0 = 0`

### Deliverable 3 — `butcherLobatto_orthogonal_to_lower_degree`

```lean
theorem butcherLobatto_orthogonal_to_lower_degree (s : ℕ) (hs : 2 ≤ s)
    (q : Polynomial ℝ) (hq : q.natDegree < s - 2) :
    ∫ x in (0 : ℝ)..1, (butcherLobatto s).eval x * q.eval x = 0
```

**Proof recipe:** same as Deliverable 2 but with `s - 2` instead of
`s - 1`, applying cycle 292 at `m := s` and `m := s - 2`. The
`q.natDegree < s` discharge needs `hq : q.natDegree < s - 2` and
`s - 2 ≤ s` (via `Nat.sub_le` or `omega`).

### Deliverable 4 — Non-vacuity witnesses

Three concrete `example`s exercising the new lemmas with a constant
polynomial (the simplest non-trivial test case):

```lean
example : ∫ x in (0:ℝ)..1, (butcherRadauI 2).eval x * (Polynomial.C (1:ℝ)).eval x = 0 :=
  butcherRadauI_orthogonal_to_lower_degree 2 (by norm_num) (Polynomial.C 1)
    (by simp [Polynomial.natDegree_C])
-- (s = 2, q = 1, natDegree q = 0 < 1 = s - 1)

example : ∫ x in (0:ℝ)..1, (butcherRadauII 2).eval x * (Polynomial.C (1:ℝ)).eval x = 0 :=
  butcherRadauII_orthogonal_to_lower_degree 2 (by norm_num) (Polynomial.C 1)
    (by simp [Polynomial.natDegree_C])

example : ∫ x in (0:ℝ)..1, (butcherLobatto 3).eval x * (Polynomial.C (1:ℝ)).eval x = 0 :=
  butcherLobatto_orthogonal_to_lower_degree 3 (by norm_num) (Polynomial.C 1)
    (by simp [Polynomial.natDegree_C])
```

If `simp [Polynomial.natDegree_C]` doesn't close the `0 < s - 1` goal
directly (Nat literals can be finicky), fall back to `decide` or
`omega` after the simp step.

## Mathlib hooks (verified at HEAD)

* `butcherShiftedLegendre_orthogonal_to_lower_degree` —
  `OpenMath/Chapter3/Section342.lean`, cycle 292. Signature:
  `(m : ℕ) (q : Polynomial ℝ) (hq : q.natDegree < m) :
   ∫ x in (0:ℝ)..1, (butcherShiftedLegendre m).eval x * q.eval x = 0`.
* `intervalIntegral.integral_add` — splits `∫ (f + g)` into `∫ f + ∫ g`
  with integrability hypotheses.
* `intervalIntegral.integral_sub` — analogous for difference.
* `Polynomial.continuous` — every polynomial is continuous on ℝ.
* `Continuous.mul` + `Continuous.intervalIntegrable` — closure under
  multiplication for integrability.
* `Polynomial.eval_add`, `Polynomial.eval_sub`, `Polynomial.eval_mul`
  — pointwise evaluation distributes.
* `Polynomial.natDegree_C` — `(C a).natDegree = 0`.
* `add_mul`, `sub_mul` — distributivity at the real level after `eval`.

## What NOT to try

### Do NOT pursue Phase B.2 (polynomial exactness) this cycle

The Phase B.2 polynomial-exactness theorem (Butcher's claim that
Radau quadrature is exact for polynomials of degree `< 2s - 1`)
requires:
* This cycle's Phase B.1 orthogonality (the input).
* Polynomial division `φ = Q · butcherRadauI s + R` with `Q.natDegree
  < s - 1`.
* Mathlib hooks for `Polynomial.divByMonic` and friends.
* A non-trivial setup mirroring cycle 304's Phase B.1
  `butcherShiftedLegendre_quadrature_exact_lt_two_n`.

This is genuinely a separate cycle (~150–200 LOC); attempting to
bundle it with Phase B.1 will overflow the LOC budget.

### Do NOT attempt the full RKTableau lift this cycle

The Phase C / Phase D Radau/Lobatto `RKTableau` construction
(analogous to cycles 308–312 for Gauss-Legendre) is multi-cycle work
requiring abscissae + quadrature weights + A-matrix infrastructure.
Out of scope for cycle 318.

### Do NOT use `ring` directly on `Polynomial ℝ` expressions

Cycle 317 confirmed this pitfall: `ring` treats `Polynomial.C n` as
opaque atoms and cannot fold constant arithmetic. This cycle's
deliverables don't need `ring` on polynomial expressions (all
manipulation happens at the `eval` level via integration), but stay
alert if a sub-step looks like it needs polynomial-level `ring`.

### Do NOT attempt to weaken the hypotheses

The `1 ≤ s` (Radau) and `2 ≤ s` (Lobatto) hypotheses are minimal:
* For `s = 0` (Radau), `s - 1 = 0` in Nat truncated subtraction, so
  `q.natDegree < 0` is vacuous (no `q` satisfies it). The polynomial
  `butcherRadauI 0 = P_0^* + P_0^* = 2` (constant), so non-vacuous
  orthogonality fails. Keeping `1 ≤ s` aligns with the textbook's
  `s ≥ 1` convention.
* For `s = 1` (Lobatto), `butcherLobatto 1 = P_1^* - P_{-1}^*` —
  truncated subtraction makes `s - 2 = 0`, vacuous as above.
  Cycle 317 already required `s ≥ 2` for the Lobatto endpoint
  theorem; staying consistent.

## LOC budget and abort threshold

* **Target**: ~150 LOC (three orthogonality theorems × ~30 LOC each
  + three non-vacuity examples + docstrings).
* **Abort threshold**: 250 LOC. If any single theorem exceeds 80 LOC,
  stop and re-scope — the recipe should be mechanical.
* **Time budget**: ≤ 90 min of focused work; if the integrability
  arguments for `intervalIntegral.integral_add` start to drag, factor
  them out as a private helper:
  ```lean
  private lemma intervalIntegrable_polyMul (p q : Polynomial ℝ) :
      IntervalIntegrable (fun x => p.eval x * q.eval x) MeasureTheory.volume 0 1 :=
    ((Polynomial.continuous p).mul (Polynomial.continuous q)).intervalIntegrable _ _
  ```
  and reuse it three times.

## Faithfulness checklist (apply to all three new theorems)

* **Same content as textbook?** The textbook's §344 proof of
  `thm:344A` uses orthogonality of Radau/Lobatto polynomials
  implicitly when deriving the polynomial-exactness degree
  (`2s - 1` for Radau, `2s - 2` for Lobatto). The orthogonality
  statements are direct corollaries of the Legendre orthogonality
  and are textbook-standard. No divergence.
* **Tautology check?** None of the three conclusions appear as
  hypotheses. Each closes by a genuine algebraic collapse
  (`0 + 0 = 0` / `0 - 0 = 0`).
* **Hypothesis strength check?** The `1 ≤ s` / `2 ≤ s` hypotheses
  are the minimal requirements for non-vacuous content (see "Do NOT
  attempt to weaken the hypotheses" above).
* **Definition smuggling check?** No new definitions introduced —
  pure consequences of cycle 317's `butcherRadauI`, `butcherRadauII`,
  `butcherLobatto` plus cycle 292's
  `butcherShiftedLegendre_orthogonal_to_lower_degree`.

## Verification checklist

After landing the theorems:

1. `lake env lean OpenMath/Chapter3/Section344.lean` — clean exit.
2. `lake env lean OpenMath/Chapter3.lean` — aggregator builds (no
   downstream regressions).
3. `grep -c sorry OpenMath/Chapter3/Section344.lean` → 0.
4. For each new theorem, `#print axioms`:
   ```
   #print axioms OpenMath.Chapter3.Section344.butcherRadauI_orthogonal_to_lower_degree
   #print axioms OpenMath.Chapter3.Section344.butcherRadauII_orthogonal_to_lower_degree
   #print axioms OpenMath.Chapter3.Section344.butcherLobatto_orthogonal_to_lower_degree
   ```
   Expected: `[propext, Classical.choice, Quot.sound]` for each.

## Housekeeping

* **`lean_status.json`**: bump `thm:344A` cycle reference from 317
  to 318. Status remains `partial` (Phase B.1 only — Phase B.2/C/D
  still open).
* **`plan.md`**: append "Cycle 318 — Phase B.1 (orthogonality)
  shipped for Radau I, Radau II, Lobatto" to the `[~] thm:344A` row.
* **`task_results/cycle_318.md`**: standard format per CLAUDE.md.

## Suggested cycle 319 entry point

If Phase B.1 ships cleanly, cycle 319 should attempt Phase B.2
(polynomial exactness via polynomial division). The recipe mirrors
cycle 304's `butcherShiftedLegendre_quadrature_exact_lt_two_n`:
* Given a polynomial `φ` of natDegree `< 2s - 1` (Radau I), divide
  `φ = Q · butcherRadauI s + R` with `natDegree Q < s - 1` and
  `natDegree R < s`.
* Apply orthogonality (cycle 318) to vanish the `Q ·
  butcherRadauI s` integral.
* Reduce the `∫ R` integral to a Lagrange-interpolation sum at the
  `s` Radau abscissae (which requires the abscissae being defined,
  which is its own Phase C deliverable).

The full Phase B.2 ship may need to interleave with Phase C
(abscissae) infrastructure. Cycle 319 planner can decide.

## If Phase B.1 stalls

Fallback options (in priority order):

1. **Ship just one of the three theorems** (most likely Radau I, the
   simplest). Sorry count remains 0; partial progress documented.
2. **Pivot to small-`s` abscissae** for Radau/Lobatto (analogous to
   cycle 295's `butcherShiftedLegendre_one_root`). At `s = 1`:
   `butcherRadauI` has a single zero at `0`, `butcherRadauII` at
   `1`, `butcherLobatto 2` has zeros at `0, 1`. Each is a small
   `example` or `theorem` directly evaluating the cycle 317
   explicit forms.
3. **Pivot to a fresh §344-adjacent target** — e.g. start scoping
   `lem:351A` (criteria for A-stability) or `thm:351B` (RK
   A-stability criterion) which are §35x infrastructure independent
   of §344.

Do NOT introduce sorries. Do NOT raise `maxHeartbeats`. If a proof
attempt looks like it needs >80 LOC for a single orthogonality
theorem, the issue is likely a missing intermediate simp lemma —
factor it out rather than fight the elaborator.
