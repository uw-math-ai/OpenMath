# Cycle 338 Results

## Worked on

`def:422B` Phase A.0.2 — higher-order vanishing of `D_element`'s
elementary weight + Phase A.0.2 capstone (full on-tree signature) +
`D_phi` congruence simp lemma.

Per cycle 338 strategy §B, the priority-1 ships are:

* **B.1** `D_element_elementaryWeight_higher_order : ∀ t, 2 ≤ t.order →
  elementaryWeightQ_phi D_element t = 0`
* **B.2** `D_element_elementaryWeight : ∀ t, elementaryWeightQ_phi
  D_element t = if t = vertex then 1 else 0` (Phase A.0.2 capstone,
  packages B.1 + cycle 337's `_vertex`).

Plus the stretch §C ship:

* **C.1** `D_phi_mul : ∀ η η', D_phi (η * η') = η * D_phi η'` (simp
  lemma, associativity of group multiplication).

All shipped in `OpenMath/Chapter4/Section422.lean` (cycle 337 anchor
file). C.2 (`D_phi` non-vacuity at `paddedEuler`) was correctly ruled
out by the strategy: `elementaryWeightQ_phi` has no multiplicativity
bridge over `composeQ_phi` in `Section381.lean` (grep confirmed
absent), so a non-vacuity at `D_phi ⟦paddedEuler⟧` would require
multi-cycle infrastructure.

## Approach

### B.1 — higher-order vanishing

Per the strategy's recipe (cycle 338 §B.1 step 1–7):

1. Destructure `t = RootedTree.mk children` via `match t, h with`.
2. Show `children ≠ []`: from `h : 2 ≤ (mk children).order` and the
   `mk []` reduction `order = 1 + orderSum [] = 1` via
   `simp [RootedTree.order, RootedTree.orderSum] at h`.
3. `show RKTableau.explicitEuler.elementaryWeight (mk children) = 0`
   to unfold `elementaryWeightQ_phi` via cycle 239's `_mk` definitional
   equality.
4. `rw [elementaryWeight_eq, Fin.sum_univ_one, derivativeWeight_mk]`
   to expose `explicitEuler.b 0 * ((c :: rest).map (fun c' =>
   internalWeight c' 0)).prod`.
5. Inner `match children, hne with | c :: rest, _` + `simp [List.map_cons,
   List.prod_cons, explicitEuler_internalWeight_zero]` collapses the
   product to `0` via the helper that every `explicitEuler.internalWeight
   c i = 0`.

The private helper `explicitEuler_internalWeight_zero (c : RootedTree)
(i : Fin 1) : explicitEuler.internalWeight c i = 0` follows from
`explicitEuler.A = 0` via `simp [RKTableau.explicitEuler]`, the
established pattern from cycle 323's `explicitEuler_hasInternalOrder_one`
(`OpenMath/Chapter3/Section323.lean:101–104`).

### B.2 — composite signature

`by_cases h : t = vertex`. Vertex branch reduces to cycle 337's
`D_element_elementaryWeight_vertex`. Non-vertex branch reduces to B.1
via the private helper `RootedTree_two_le_order_of_ne_vertex` (proves
`t ≠ vertex → 2 ≤ t.order` by destructuring `children`: `nil` case
contradicts `t ≠ vertex`; `cons c rest` case uses `0 < c.order` from
`Section301.RootedTree.order_pos` + `omega`).

This required adding `import OpenMath.Chapter3.Section301` to
`Section422.lean` (was implicit-transitive via Section312/381 before
but `order_pos` lives in Section301 specifically).

### C.1 — `D_phi_mul` simp

One-liner: `show (η * η') * D_element = η * (η' * D_element); exact
mul_assoc _ _ _`. Uses cycle 236's `instGroup_phi` mul associativity.

## Result

SUCCESS — three new public theorems + two private helpers shipped in
`Section422.lean`, axiom-clean (`[propext, Classical.choice, Quot.sound]`
expected). Section422.lean grew from 133 LOC (cycle 337) → ~210 LOC
(cycle 338), in line with the strategy estimate of "~180–210 LOC for
B.1 + B.2 + C.1".

Build verified via `lake env lean OpenMath/Chapter4/Section422.lean`
(see commit log for the lean_verify axiom checks).

## Faithfulness check

For each new `def` or `theorem` introduced this cycle:

### `D_element_elementaryWeight_higher_order` (B.1)

* Entity ID: derived from `thm:387A` / `def:422B` § Phase A.0
  textbook content. Butcher §387 (`extraction/raw_text/ch03.txt:9392`):
  > "the differentiation operation, scaled by the unit stepsize h, is
  > a member of G and corresponds to (385b)"
  i.e. the §385b generalized one-stage RK with `A = 0, b = [1], c = [0],
  b₀ = 0`. Its elementary weights are: `Φ_D(τ) = 1`, `Φ_D(t≥2) = 0`.
* Lean statement captures: **same content** — `2 ≤ t.order` is exactly
  the textbook condition `t ≠ τ` (equivalently `r(t) ≥ 2`, since
  `r(τ) = 1` and no tree in `T` has `r = 0`).
* b₀-invisibility note from cycle 337 carries forward: we use
  `RKTableau.explicitEuler` (which has `b₀ = 1` implicit) as the
  `Quotient PhiEquivalent.setoidSigma` representative of Butcher's `D
  ∈ G` (which has `b₀ = 0`). The on-tree elementary weights are
  identical because `PhiEquivalent` does not see `b₀` (see
  `feedback_phi_equivalent_b0_invisibility.md`).

### `D_element_elementaryWeight` (B.2)

* No new textbook content; this is a repackaging of B.1 + cycle 337's
  `_vertex`. The `if t = vertex then 1 else 0` form matches Butcher
  §387's `Φ_D` exactly on `T` (modulo the b₀-collapse).

### `D_phi_mul` (C.1)

* No textbook content (a derived simp lemma about group
  multiplication); follows from `mul_assoc` in cycle 236's
  `instGroup_phi`.

### Tautology check

* B.1's conclusion `= 0` does NOT match any hypothesis. PASS.
* B.2's conclusion `= if … then 1 else 0` does NOT match any
  hypothesis. PASS.
* C.1's conclusion `D_phi (η * η') = η * D_phi η'` does NOT match any
  hypothesis. PASS.

### Identity check

* B.1's proof is a `match`/`rw`/`simp` chain, NOT `exact h`. PASS.
* B.2's proof is a `by_cases` + `exact …` chain calling B.1 + cycle
  337's `_vertex`. PASS.
* C.1's proof is `mul_assoc _ _ _`, NOT `exact h`. PASS.

### Definition smuggling check

No new `structure`/`class` introduced this cycle. PASS.

### Hypothesis strength check

* B.1's `2 ≤ t.order` is the minimal condition (equivalent to `t ≠
  vertex` modulo `RootedTree.order_pos`). NOT stronger than textbook.
  PASS.
* B.2 has no hypothesis. PASS.
* C.1 has no hypothesis. PASS.

### Absent theorem check

No comment promises a future `sorry` that is not present. PASS.

## Dead ends

None this cycle — the B.1 proof recipe from the strategy worked
verbatim modulo the obvious adjustments (using
`Fin.sum_univ_one` mid-`rw` to collapse the singleton sum before
applying `derivativeWeight_mk`).

One minor adjustment: I initially attempted to reuse
`RootedTree.order_pos` from `Section301` without importing it, but
`Section422`'s import chain (`Mathlib + Section381 + Section404`) did
NOT transitively expose it. Added an explicit `import
OpenMath.Chapter3.Section301` line.

## Discovery

* **Section301 vs Section310 namespace split.** `RootedTree.order_pos`
  lives in `Section301` (the §301 *isomorphism / density / symmetry*
  layer), not in `Section310` (the `RootedTree` definition layer).
  This is because `order_pos` is a *theorem*, not part of the
  recursive `order` definition. Future Chapter 4 sections that need
  positivity of order on `RootedTree` should explicitly import
  `Section301`.

* **`Fin.sum_univ_one` as a `rw`-style lemma.** It rewrites `∑ i :
  Fin 1, f i = f 0` cleanly mid-`rw` chain, which is useful for
  proofs over 1-stage tableaux like `explicitEuler`. The cycle 323
  pattern used pure `simp [RKTableau.explicitEuler]` to handle this,
  but the granular `rw [Fin.sum_univ_one]` form is more explicit and
  composes well with `rw [derivativeWeight_mk]`.

* **Phase A.0.2 closes the elementary-weight signature of
  `D_element`.** Combined with cycle 337's `_vertex`, the new B.2
  capstone gives the full on-tree signature `Φ_D(t) = if t = τ then 1
  else 0`, which is the form Butcher §387 implicitly uses when
  manipulating `D ∈ G` in subsequent §388+ algebra.

## Suggested next approach

Per `.prover-state/issues/def_422B_path.md` §5 phase decomposition:

* **Cycle 339 (recommended)**: **Phase B** — `Group.zpow` API
  non-vacuity on the §383 quotient group. Verify Mathlib's
  `Group.zpow_natCast`, `Group.zpow_neg`, etc., fire correctly on
  `Quotient PhiEquivalent.setoidSigma`, and ship 1–2 non-vacuity
  sanity theorems (e.g. `D_element^(0) = 1`, `D_element^(1) =
  D_element`, plus a `D_element^(-1)` computation on the
  `paddedEuler` witness if tractable). Estimated 30–60 LOC. Low risk
  per the scoping doc.

* **Cycle 340+ (Phase C)**: introduce the `Eq422a` predicate
  capturing equation (422a) at the `Quotient PhiEquivalent.setoidSigma`
  level. Requires Phase B's zpow API in place.

* **Cycle 341+ (Phase D)**: inductive solver for `η : RootedTree → ℝ`
  via well-founded recursion on `RootedTree.order`. Must be planned
  with a proper sub-phase decomposition (cycle 149/150 and 200/201
  rollback precedents apply — no sorry-first scaffold without a
  credible single-cycle close).

* **Optional Phase A.0.3 (defer)**: if a downstream consumer
  (Phase C/D) needs an `elementaryWeightQ_phi`-multiplicativity bridge
  over `composeQ_phi`, ship it as a separate infrastructure cycle.
  Currently NOT a blocker for cycle 339's Phase B work.
