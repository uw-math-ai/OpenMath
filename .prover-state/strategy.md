# Cycle 328 Strategy — §344 Phase D.8: Radau II `s = 2` direct-form `RKTableau` (D(s) variant)

## §A. State summary

* **Sorry count**: 0 (clean).
* **Open blockers**: none.
* **Aristotle pending**: none.
* **Branch tip**: `9b7e49f Cycle 327 — §344 Phase D.7: Lobatto IIIB s=3 direct-form RKTableau shipped.`
* **Section344.lean LOC**: 1807 (post-cycle 327).
* **Recent §344 momentum**: cycles 322–327 have shipped six consecutive
  `s ≤ 3` small-`s` Radau / Lobatto `RKTableau` deliverables (Radau IIA
  s=1, Lobatto IIIA s=2, Radau IIA s=2, Radau IA s=1, Radau IA s=2,
  Lobatto IIIB s=3). The mechanical-template pattern is well-confirmed
  across the cycles 326/327 direct-form ships.

## §B. Cycle 328 target

**Ship `butcherRadauIIDirect_two : RKTableau 2`** — the `s = 2` Radau II
tableau in the D(s)-choice variant. Per Butcher Table 344(I) p. 244 the
Radau II family uses `Choice of A = D(s)` (the matrix satisfying the
D(s) simplifying assumption), whereas cycle 324's `butcherRadauIIA_two`
uses the plain Lagrange-collocation A-matrix (which corresponds to
Butcher's Radau **IIA** = `Choice of A = "the reflections of Radau I"`).

The deliverable closes a coverage gap: Butcher distinguishes
**Radau II** (D(s)) from **Radau IIA** (collocation/reflections) in
Table 344(I), but the project so far has only the IIA variant.

### Expected shape

Per Butcher Table 344(II) p. 245 (one of the four printed tables in
Section 344):

```
Radau II   (s = 2, p = 3)
                     c           A
                     1/3        Something
                     1          Something
                                b
```

`c` and `b` agree with Radau IIA (both use the Radau II quadrature
choice at `c = (1/3, 1)`, so by uniqueness of the quadrature weights
`b = (3/4, 1/4)`). The two families differ **only in A**.

### Mandatory audit step (per the cycle 326 protocol)

**BEFORE writing any Lean code**, read `extraction/raw_text/ch03.txt`
around the Radau II `s = 2` printed table. Search for the literal
string `Radau II` and then the literal `(s = 2, p = 3)`. Quote the
exact numerical values from the printed table verbatim in the cycle
328 task results §"Faithfulness check".

If the printed Radau II `s = 2` `A`-matrix matches cycle 324's
`butcherRadauIIA_two` A-matrix (`!![5/12, -1/12; 3/4, 1/4]`), then
**Radau II and Radau IIA coincide at `s = 2`** — in that case, ship a
short `theorem butcherRadauII_two_eq_butcherRadauIIA_two :
butcherRadauIIDirect_two = butcherRadauIIA_two` (rfl or by
componentwise injectivity) instead of a fresh tableau definition.
Document the coincidence in Section344's section docstring.

If the printed values **differ** from cycle 324, ship as a fresh
`butcherRadauIIDirect_two : RKTableau 2` with the printed values.
This is the more interesting outcome — it would mirror cycle 326's
Radau IA/IIA divergence and confirm that the D(s)-vs-C(s) distinction
is non-trivial at small `s`.

## §C. Concrete plan

### §C.1. Audit (≤ 10 minutes)

Grep for "Radau II" in `extraction/raw_text/ch03.txt`. Locate the
printed Radau II `s = 2` table. Quote it verbatim in the cycle 328
task results §"Faithfulness check". Confirm `c = (1/3, 1)`,
`b = (3/4, 1/4)`, and read the four A-entries.

Cross-check by computing what D(s) at `s = 2` should produce
algebraically: D(s) requires
`∑ᵢ bᵢ · cᵢ^(k-1) · Aᵢⱼ = bⱼ/k · (1 − cⱼ^k)` for `k = 1, …, s`,
`j = 1, …, s`. At `s = 2` with `b = (3/4, 1/4), c = (1/3, 1)`, this is
four linear equations in the four `Aᵢⱼ` — solvable by hand for a
spot-check.

### §C.2. Ship

After the audit, write the `RKTableau 2` declaration immediately after
`butcherLobattoIIIBDirect_three` in `OpenMath/Chapter3/Section344.lean`
(approximately line 1807+, following the cycle 327 anchor block). Use
the cycle 326/327 direct-form template literally:

```lean
/--
Butcher §344 Table 344(II) p. 245 — Radau II at `s = 2` (D(s) choice).

…docstring documenting the audit + faithfulness divergence vs Radau IIA…
-/
noncomputable def butcherRadauIIDirect_two : RKTableau 2 where
  A := !![A₀₀, A₀₁; A₁₀, A₁₁]  -- values from audit
  b := ![3/4, 1/4]
  c := ![1/3, 1]
```

Where `A₀₀, A₀₁, A₁₀, A₁₁` are the audited values (likely involving
`1/4`, `-1/4`, `3/4`, `5/12` or similar simple rationals).

### §C.3. Non-vacuity witness

Ship a `SatisfiesB 3` example (Radau II at `s = 2` has classical order
`p = 2s − 1 = 3`, matching the cycle 324 Radau IIA example):

```lean
example : butcherRadauIIDirect_two.SatisfiesB 3 := by
  intro k h1 hk
  interval_cases k <;>
    simp [butcherRadauIIDirect_two, Fin.sum_univ_two] <;> norm_num
```

Three arms `k ∈ {1, 2, 3}`. Each arm: `∑ⱼ bⱼ · cⱼ^(k-1) = 1/k`.
Mechanical close per cycle 324's recipe in Section344.lean.

### §C.4. Optional stretch — D(s) certificate

If the audit confirms a divergence from Radau IIA, ship a tiny stretch
theorem documenting the divergence:

```lean
theorem butcherRadauIIDirect_two_satisfiesD_two :
    butcherRadauIIDirect_two.SatisfiesD 2 := by
  …four-arm Fin.sum_univ_two + norm_num close…
```

This makes explicit that the D(s) construction was used (vs cycle
324's IIA which satisfies `C(s)` but not `D(s)` in general). Skip if
the audit shows coincidence or if LOC budget is tight.

## §D. Verification

Per the cycle 326/327 protocol:

```
lake env lean OpenMath/Chapter3/Section344.lean
lake build OpenMath.Chapter3.Section344
lake env lean OpenMath/Chapter3.lean
```

All three should exit 0. Sorry count must stay 0.

Axiom-clean spot-check on the new `def` and any new theorems:

```
#print axioms OpenMath.Chapter3.Section344.butcherRadauIIDirect_two
```

Expected: `[propext, Classical.choice, Quot.sound]` only.

## §E. LOC budget

* Audit + docstring: ~15 LOC
* `butcherRadauIIDirect_two` def: ~10 LOC
* `SatisfiesB 3` example: ~5 LOC
* Optional D(2) certificate: ~10 LOC
* **Total**: ~30–40 LOC if coincidence; ~50 LOC if divergence with
  D(2) stretch.

Within the cycle 326/327 ~50 LOC small-cycle pattern.

## §F. What NOT to do

* **Do NOT skip the audit.** Cycle 326 caught the Radau IA collocation
  divergence precisely *because* the audit ran first. Skipping the
  audit risks shipping incorrect values. If the worker writes A-matrix
  entries before quoting Butcher's table, abort and restart with the
  audit.
* **Do NOT compute the D(s) solution from scratch as the primary
  deliverable.** The audit-from-printed-table path is mechanical;
  re-deriving D(s) from the simplifying-assumption equations is
  multi-cycle infrastructure. If the audit fails to surface usable
  printed values, ship a deferral issue and pivot to a different §344
  target (Lobatto IIIC s=2 or Radau I s=2 direct forms).
* **Do NOT pursue the "reflections of X" canonical bridge.** Per
  `.prover-state/issues/radau_ia_collocation_divergence.md`, this is
  multi-cycle work. The direct-form pattern sidesteps it cleanly.
* **Do NOT attempt the Phase B.2 polynomial exactness `thm:344A`
  headline.** Multi-cycle. Stay with small-`s` direct-form ships.
* **Do NOT touch GPFS-blocked Section441.lean work.** 43+ consecutive
  timeouts per `cycle_182_gpfs_slowness.md`. Skip.
* **Do NOT submit to Aristotle.** The cycles 326/327 direct-form ships
  closed in single cycles without Aristotle; this cycle should too.
* **Do NOT introduce sorries.** Per the cycle 200/201 rollback
  precedent.
* **Do NOT raise `maxHeartbeats`.** The `Fin.sum_univ_two` + `simp` +
  `norm_num` close fits under the default 200000 budget at `s = 2`.

## §G. Risk register

* **R1 — Audit shows Radau II = Radau IIA at s = 2.** Mitigation: ship
  the coincidence theorem (cycle 328 §C alt path); still a valid
  cycle deliverable (closes the open question about D(s) vs C(s)
  divergence at small `s`).
* **R2 — Negative literals in `!![...]`.** Confirmed safe by cycles
  324/326/327. Use `-(1/12)` or `-(1/4)` syntax directly.
* **R3 — `Fin.sum_univ_two` not in default simp set.** Per cycle 324
  precedent, must be passed explicitly to `simp`. The example
  template above already includes it.
* **R4 — D(s) constraints algebraically incompatible at `s = 2`
  (over-determined system).** Mitigation: trust the printed Butcher
  table; if its values fail D(2), that's a typo to document via an
  issue file, not a Lean problem.

## §H. Faithfulness anchors

For the new `def butcherRadauIIDirect_two`:

* **Source**: `extraction/raw_text/ch03.txt` — Radau II `s = 2`,
  `p = 3` printed table from §344. Worker must quote verbatim in task
  results.
* **Coverage gap closed**: Butcher Table 344(I) p. 244 lists Radau II
  with `Choice of A = D(s)` distinct from Radau IIA's
  `Choice of A = "reflections of Radau I"`. Cycle 324 shipped the IIA
  (plain Lagrange collocation) variant; this cycle ships the D(s)
  variant.

For the `SatisfiesB 3` example:

* **Source**: Radau II `s = 2` has classical order `p = 2s − 1 = 3`
  (Butcher Table 344(I) col 3); the maximal `B(η)` quadrature
  condition is `η = p = 3`.

## §I. Cycle 329+ outlook

If cycle 328 ships cleanly:

* **Cycle 329**: Radau I `s = 2` direct form (cycle 326's Radau IA is
  *not* the plain collocation form, but Radau I per Butcher Table
  344(I) col 4 uses `Choice of A = C(s)` — straightforward direct
  ship, may coincide with plain collocation at small `s`).
* **Cycle 330**: Lobatto IIIC `s = 2` direct form (Butcher Table
  344(IV) p. 246). Per `ch03.txt:5224`, Lobatto IIIC = "reflections of
  Lobatto III". Audit Butcher's printed table first.
* **Cycle 331+**: Lobatto IIIA `s = 3` (Simpson's-rule extension,
  multi-cycle since the `A`-matrix at `s = 3` is no longer trivial) or
  pivot to a fresh entity (Chapter 5 §550, def:442A, def:422B, etc).

Each remaining direct-form ship is a ~50 LOC mechanical template
deliverable. The mechanical-template hypothesis has been confirmed
across cycles 326/327 — pattern continuation is the highest-confidence
single-cycle work available.
