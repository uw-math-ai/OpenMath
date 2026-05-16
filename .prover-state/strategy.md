# Cycle 303 Strategy — Phase A.2 of lem:342B (Lagrange quadrature weights + exactness)

## State summary

* HEAD = `d511f55` (cycle 302). 0 sorries. 71/175 entities done.
* Cycle 302 SHIPPED Phase A.1 of `lem:342B`: `butcherShiftedLegendre_zeros`
  (`Fin n → ℝ` enumeration via `Finset.orderEmbOfFin` on cycle 301's
  concrete root finset) plus four spec lemmas
  (`_mem_Ioo`, `_isRoot`, `_injective`, `_card_eq`). All axiom-clean.
  `Section342.lean` is now 6200 LOC.
* `lem:342A` fully closed cycle 301 (all seven clauses (342a)–(342g)).
* Aristotle queue empty.
* No active blockers in `.prover-state/issues/` for §342.

## Priority 0 — Health checks (sanity, ≤5 min)

1. Confirm HEAD = `d511f55` via `git log -1 --format='%h %s'`.
2. `lake env lean OpenMath/Chapter3/Section342.lean` exits 0.
3. Sorry count 0: `grep -c sorry OpenMath/Chapter3/Section342.lean`.
4. `#print axioms OpenMath.Chapter3.Section342.butcherShiftedLegendre_zeros`
   returns `[propext, Classical.choice, Quot.sound]` only.

If any check fails, stop and file an issue. Do NOT touch unrelated files.

## Priority 1 — Phase A.2: Lagrange quadrature weights (~120–180 LOC)

**Target**: define quadrature weights `bⱼ` indexed by the cycle 302
`butcherShiftedLegendre_zeros n j` nodes, and prove exactness on
polynomials of degree `< n` (Butcher §342 p. 237 — half of `lem:342B`;
the full `2n`-degree exactness is Phase B and uses both Phase A.2's
exactness-up-to-`n−1` and the (342a) orthogonality).

### Deliverable D1 — `butcherShiftedLegendre_quadratureWeights`

```lean
noncomputable def butcherShiftedLegendre_quadratureWeights
    (n : ℕ) (j : Fin n) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    (Lagrange.basis Finset.univ (butcherShiftedLegendre_zeros n) j).eval x
```

(Adjust the Mathlib hook name to whatever fires — see the §"Mathlib
hooks" subsection below for verification steps.)

### Deliverable D2 — `butcherShiftedLegendre_quadrature_exact_lt_n`

```lean
theorem butcherShiftedLegendre_quadrature_exact_lt_n
    (n : ℕ) (φ : Polynomial ℝ) (hdeg : φ.natDegree < n) :
    (∫ x in (0 : ℝ)..1, φ.eval x)
      = ∑ j : Fin n,
          butcherShiftedLegendre_quadratureWeights n j *
          φ.eval (butcherShiftedLegendre_zeros n j)
```

Proof recipe (textbook standard):
1. Let `L_j` be the Lagrange basis polynomial at node `j` over the
   `butcherShiftedLegendre_zeros n` family.
2. Since `n` distinct nodes interpolate any polynomial of degree
   `< n` uniquely, `φ = ∑ j, φ(c_j) • L_j` as polynomials.
3. Integrate both sides over `[0, 1]`:
   `∫ φ = ∑ j, φ(c_j) · ∫ L_j = ∑ j, φ(c_j) · b_j`.

Distinctness of the nodes for the Lagrange basis construction comes
from cycle 302's `butcherShiftedLegendre_zeros_injective`.

### Deliverable D3 (P3 stretch) — n=2 non-vacuity witness

If LOC budget allows, ship an `example` exercising D2 at `n = 2` on
a concrete polynomial (e.g. `φ = X` to test `b₁ + b₂ = 1/2`, which
is the integral of `x` over `[0,1]`). Use cycle 294's
`butcherShiftedLegendre_two_roots` to get the explicit nodes
`(3 ± √3)/6`. The closed-form Gauss-2 weights are both `1/2`.

This anchor is NOT required for Phase A.2 closure; ship if Phase A.2
proper closes within budget.

## Mathlib hooks to verify EARLY (before writing any proof body)

The Mathlib Lagrange API has had name churn over the past year.
Verify the following with `lean_local_search` and `lean_loogle` BEFORE
committing to D1's signature:

| Concept | Candidate name | Verification |
|---|---|---|
| Lagrange basis polynomial | `Lagrange.basis Finset.univ ν j` or `Polynomial.Lagrange.basis` | `lean_local_search "Lagrange.basis"` |
| Lagrange interpolation polynomial | `Lagrange.interpolate Finset.univ ν φ` | `lean_local_search "Lagrange.interpolate"` |
| Interpolation = identity for low-degree polys | `Lagrange.eq_interpolate_of_eval_eq` or `Polynomial.eq_of_degree_lt_of_eval_finset_eq` | `lean_loogle "Polynomial _ = Polynomial.Lagrange.interpolate _ _ _"` |
| Polynomial → integrable | `Polynomial.continuous` + `Continuous.intervalIntegrable` | (already used cycle 277/281) |
| `intervalIntegral.integral_finset_sum` | for swapping integral and `∑ j : Fin n` | std |
| Lagrange node injectivity → distinct values | `Function.Injective.injOn` lift to `Set.InjOn ν Finset.univ` | std |

If `Lagrange.basis` doesn't fire on `Fin n → ℝ` directly, the
adapter is `Finset.univ.image (butcherShiftedLegendre_zeros n)` —
a `Finset ℝ` of size `n` (cardinality preserved by injectivity from
cycle 302). Switch to the `Finset`-indexed Lagrange API as needed.

If the cleanest path is `Finset`-indexed, build a small adapter:
```lean
noncomputable def butcherShiftedLegendre_quadratureWeights_finset
    (n : ℕ) (c : ℝ) (hc : c ∈ butcherShiftedLegendre_rootsInIoo n) : ℝ
```
indexed by membership in `butcherShiftedLegendre_rootsInIoo n` rather
than `Fin n`. Choose the indexing scheme that minimises Mathlib churn.

## Approach (concrete)

1. (10 min) Run Priority 0 health checks.
2. (15 min) `lean_local_search` / `lean_loogle` audit of the Lagrange
   API names above. Verify on a small `#check Lagrange.basis ...`
   stub before committing to D1's signature.
3. (30 min) Ship D1 + a small `_eq` helper if needed (unfolding the
   weight as the integral of the basis polynomial). Run
   `lake env lean OpenMath/Chapter3/Section342.lean`; confirm
   axiom-clean.
4. (45 min) Ship D2. The proof body should be ~20–40 LOC:
   * `have hφ_interp : φ = Lagrange.interpolate ... φ.eval := …`
     (via the degree-`< n` characterisation).
   * `rw [hφ_interp]`, expand the interpolation as a sum, swap
     integral and sum via `intervalIntegral.integral_finset_sum`,
     `intervalIntegral.integral_const_mul` (or `integral_smul`),
     fold back into `quadratureWeights`.
5. (15 min, optional) Ship D3 (n=2 witness) if Phase A.2 closed
   within budget.
6. (10 min) `#print axioms` on D1, D2 (and D3 if shipped) — confirm
   `[propext, Classical.choice, Quot.sound]` only. Write
   `task_results/cycle_303.md`.
7. (5 min) Update `plan.md` `lem:342B` row from `[ ]` to `[~]`,
   `lean_status.json` `lem:342B` row from `unformalized` to
   `partial` with a Phase A.2 closure note.
8. Commit, push.

LOC budget: 150 ± 30. If at 60 min the audit/D1 is still stalled,
fall back to the **Backup B** plan below.

## Backup B — if Lagrange API churn blocks D1/D2

If Mathlib's Lagrange interpolation API doesn't compose cleanly with
the `Fin n → ℝ` enumeration (e.g. unification failures, namespace
issues, or unavailable interpolation-identity lemma), pivot to
**direct construction** of `bⱼ`:

```lean
noncomputable def butcherShiftedLegendre_quadratureWeights
    (n : ℕ) (j : Fin n) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    ∏ k ∈ Finset.univ.filter (· ≠ j),
      (x - butcherShiftedLegendre_zeros n k) /
      (butcherShiftedLegendre_zeros n j - butcherShiftedLegendre_zeros n k)
```

Prove D2 via direct induction on the basis polynomials. The
denominators are nonzero by `butcherShiftedLegendre_zeros_injective`
(cycle 302) plus `sub_ne_zero.mpr`. This is more LOC (~200) but
avoids Mathlib API guessing.

If even Backup B looks shaky after 90 min total, ship D1 only
(definition + non-vacuity that the integral is a real number), defer
D2 to cycle 304, and fire Aristotle on D2 with the cycle 302
infrastructure as cited axioms.

## What NOT to try

* **Do NOT** attempt the full `lem:342B` headline (`2n`-degree
  exactness) in cycle 303. That is Phase B and requires (342a)
  orthogonality composed with the polynomial-division argument
  `φ = q · P_n^* + r` with `deg q, deg r < n`. Multi-cycle scope.
* **Do NOT** introduce sorries. If D2 stalls past 90 min, ship D1
  only with a non-vacuity witness, NOT a sorry-first D2.
* **Do NOT** redefine `butcherShiftedLegendre_zeros` — cycle 302's
  `orderEmbOfFin`-based definition is what downstream Phase A.2/A.3
  consume. Build adapters if Mathlib hooks want a different shape.
* **Do NOT** edit cycle 301/302 deliverables. The Phase A.1
  infrastructure is settled.
* **Do NOT** retry Aristotle batches for §342 — `lem:342A` is closed,
  no live jobs to incorporate.
* **Do NOT** raise `maxHeartbeats`. If the D2 proof times out,
  decompose into a per-basis-polynomial helper.
* **Do NOT** attempt to compile `OpenMath/Chapter4/Section441.lean`
  (43+ consecutive GPFS timeouts since cycle 182; skip per
  `cycle_182_gpfs_slowness.md`).
* **Do NOT** edit `scripts/autonomous_loop.py` — supervisor scoring
  bugs are loop-maintainer territory (see
  `tautology_scanner_false_positives.md`).
* **Do NOT** treat the prompt's "consultant_advice_cycle_263" issue
  reference as actionable on §342 work — it's a §300/§310
  labelled-tree plan, orthogonal to this cycle's §342 target.

## Faithfulness notes

* `butcherShiftedLegendre_quadratureWeights` is Butcher's `b_j` from
  §342 p. 237 ("there exist positive numbers `b_1, …, b_s` such that
  ∫₀¹ φ(x) dx = ∑ b_i φ(c_i) for polynomials of degree `< 2s`"). The
  positivity claim (`0 < b_j`) is a separate clause that Phase B
  proves; we are NOT required to ship it in cycle 303.
* The textbook lemma (`lem:342B`) is the full `2n`-degree exactness
  + positivity + uniqueness. Phase A.2 (this cycle) ships only the
  `n`-degree half. `lean_status.json` should reflect `partial`, not
  `formalized`, until Phase B lands.
* Definition smuggling check: `b_j := ∫₀¹ L_j` is the canonical
  textbook formula, NOT a smuggling of the exactness conclusion.
  The exactness theorem D2 is genuine work — Phase B's `2n`-degree
  extension is the substantive content of `lem:342B`.

## Decision tree

```
Health checks pass (P0)?
├── No → File issue, stop.
└── Yes → Lagrange API audit
    ├── Clean → Ship D1 + D2 (Priority 1)
    │   ├── Time remaining → Ship D3 (n=2 witness)
    │   └── Done → Update plan/status, commit
    └── Stalls past 60 min → Backup B (direct construction)
        ├── Closes in 60 min → Ship D1 + D2, commit
        └── Stalls past 90 min total → Ship D1 only, defer D2 to
            cycle 304, fire Aristotle on D2 if you have budget for
            a single submission
```

## Files touched (expected)

* `OpenMath/Chapter3/Section342.lean` (add ~150 LOC after cycle 302's
  Phase A.1 block; `end` of namespace stays at file bottom).
* `extraction/formalization_data/lean_status.json` — bump `lem:342B`
  row to `partial`, cycle 303, lean_symbol set to
  `butcherShiftedLegendre_quadrature_exact_lt_n`.
* `plan.md` — `lem:342B` row `[ ]` → `[~]`.
* `.prover-state/task_results/cycle_303.md` — standard format.

No other files should change.
