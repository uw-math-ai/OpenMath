# Cycle 497 Results

## Worked on

§422 Phase γ — `inversePolyTree_eq_of_subtree_agreement` (recursive
closed-subtree agreement for `inversePolyTree`) plus three private
cross-term helpers (`monochildCrossTerm_eq_of_subtree_agreement`,
`bichildCrossTerm_eq_of_subtree_agreement`,
`trichildCrossTerm_eq_of_subtree_agreement`). Mirrors cycle 376's
`inversePolynomial_eq_of_subtree_agreement` at the recursive-def
level.

Also flagged the R6.B obstacle in cycle 495's scoping doc
(`.prover-state/issues/def_422B_phase_beta_gamma_scoping.md`):
Phase β.2 as scoped is structurally blocked and cannot close cycle
365's grandfathered sorry without prior Phase α'.5.2/3 work (extending
`inversePolyTree` to k ≥ 4 children).

## Approach

Per the cycle 497 strategy §B–C:

1. **Three cross-term helpers** (one per dispatch table):
   * `monochildCrossTerm_eq_of_subtree_agreement c f g (h_closed
     : ∀ s, s.order ≤ (mk [c]).order → f s = g s)` —
     `unfold monochildCrossTerm` then `by_cases` cascade over the
     3 named branches (`c = broom₃`, `c = cherry`, `c = mk [cherry]`)
     + default. Each non-default branch `subst`s `c` to the concrete
     value, then discharges each `f vertex / f cherry / f (mk [cherry])`
     occurrence via `h_closed _ (by decide)`.
   * `bichildCrossTerm_eq_of_subtree_agreement c₁ c₂ f g h_closed` —
     same pattern, three named branches (`(cherry, cherry)`,
     `(broom₃, cherry)`, `(vertex, cherry)`). Conjunctive conditions
     `c₁ = X ∧ c₂ = Y` destructured via `obtain ⟨h₁, h₂⟩` + double
     `subst`.
   * `trichildCrossTerm_eq_of_subtree_agreement c₁ c₂ c₃ f g h_closed`
     — same pattern, five named branches (`(v,v,v)`, `(v,v,c)`,
     `(v,c,c)`, `(v,v,mk[c])`, `(v,v,b₃)`). Triple-conjunctive
     conditions destructured via `obtain ⟨h₁, h₂, h₃⟩` + triple
     `subst`.

2. **Main theorem `inversePolyTree_eq_of_subtree_agreement`** —
   strong induction on `t.order` via `Nat.strong_induction_on`
   (mirroring `Section381.lean:811` / `Section404.lean:1594` etc.):
   * Generalize over `t, f, g` and the bound `n ≥ t.order` (via the
     standard `suffices ∀ n, ∀ t f g, t.order ≤ n → ... `).
   * `rcases t with ⟨children⟩`, then `match children with`:
     - `[]` arm: `inversePolyTree (mk []) f = -f vertex`; closure
       via `h_closed vertex (le_refl _)`.
     - `[c]` arm: 5 ingredients (`hv`, `hIH` via IH at `c` with
       `c.order < (mk [c]).order` from `RootedTree.order_lt_of_mem_children
       (List.mem_singleton.mpr rfl)`, `hmono` via the monochild helper,
       `hself` via `h_closed _ (le_refl _)`). `rw` chain closes.
     - `[c₁, c₂]` arm: analogous with 2 IHs + bichild helper +
       `hmkt₁/₂` (intermediate `f (mk [cᵢ]) = g (mk [cᵢ])` proved
       by an `omega` calc on `(mk [cᵢ]).order ≤ (mk [c₁, c₂]).order`).
     - `[c₁, c₂, c₃]` arm: analogous with 3 IHs + trichild helper +
       `hmkt₁/₂/₃`.
     - `_ :: _ :: _ :: _ :: _` arm: both sides reduce to `0`; `rfl`
       closes.

3. **Order side-conditions**: For named small-tree comparisons
   inside the helpers, `by decide` discharges since all referenced
   subtrees and the parent `(mk […]).order` are concrete after
   `subst`. For `vertex.order ≤ t.order` inside the main theorem,
   `RootedTree.order_pos t : 0 < t.order` (Section301.lean:159)
   suffices (since `vertex.order = 1`, `0 < t.order` definitionally
   equals `1 ≤ t.order` on ℕ).

## Result

SUCCESS — Phase γ shipped. Three private helpers + one public
theorem, all axiom-clean ([propext, Classical.choice, Quot.sound]).

Pre-cycle sorry count: 5 (4 docstring + 1 grandfathered cycle 365
code sorry). Post-cycle sorry count: 5 (unchanged — Phase γ adds
no `sorry`s).

§422 axiom-clean streak: 69 substantive + 5 doc → **70 substantive
+ 5 doc** (cycles 336–497).

LOC added: ~430 (helpers ~290 + main theorem ~140), within the
cycle 495 scoping doc §5.3 budget (200–350 LOC estimate, slightly
over due to extra `omega` arithmetic for `(mk [cᵢ]).order ≤ (mk
[c₁, c₂]).order` etc.).

## Faithfulness check

The four new theorems are **infrastructure** — they assert
structural properties of `monochildCrossTerm`, `bichildCrossTerm`,
`trichildCrossTerm`, and `inversePolyTree` qua functions (not
Butcher textbook entities). Faithfulness checks apply to the
infrastructure standard:

- **Entity ID**: N/A (infrastructure, mirroring cycle 376's
  `inversePolynomial_eq_of_subtree_agreement` precedent at the
  recursive-def level).
- **Tautology check**: each conclusion (`<crossTerm> c f = <crossTerm> c g`
  or `inversePolyTree t f = inversePolyTree t g`) is NOT a hypothesis
  — hypotheses are the closure condition `h_closed : ∀ s, s.order ≤
  <bound> → f s = g s`. PASS.
- **Identity check**: each proof is a non-trivial case split with
  `subst` + `rw` chains (helpers) or strong induction (main); not a
  single `exact h` or `id`. PASS.
- **Hypothesis strength check**: `h_closed`'s closed-subtree-agreement
  form matches cycle 376's `inversePolynomial`-flavoured precedent.
  The closure bound is tight: `s.order ≤ (mk [c]).order` (not
  `< `; the helpers reference `f` at the parent tree itself in some
  branches, e.g. `f (mk [cherry])` in the `c = mk [cherry]` branch
  of monochild). NOT strengthened beyond necessity. PASS.
- **Definition smuggling**: no new `def`/`structure` introduced;
  only `theorem`s. PASS.

## Dead ends

None encountered in cycle 497 directly.

**Cycle 495 scoping doc R6.B obstacle**: the strategy explicitly
warned (cycle 497 strategy §A) that Phase β.2 as scoped in cycle
495 is impossible — `Φ_{η⁻¹}(t)` on quadchild+ trees is generically
nonzero per cycle 358's `elementaryWeightQ_phi_inv_mk` formula
(`Section422.lean:582`), but `inversePolyTree`'s default arm on
k ≥ 4 children returns `0`. The cycle 365 sorry closure plan in
cycle 495's scoping doc §5.2 is structurally flawed. Worker did
NOT attempt Phase β.2; this cycle ships Phase γ only, and the
scoping doc has been updated with a §12 "Cycle 497 closure update"
documenting the R6.B falsity.

## Discovery

**Discovery #1 (lockable into a memory entry, if surprising):** the
`Nat.strong_induction_on` pattern transfers cleanly from
ℕ-indexed contexts (cycles 197, 269, 277, 287, 312, etc.) to a
`RootedTree.order`-indexed strong induction by an explicit
`suffices ∀ n, ∀ t : RT, t.order ≤ n → P t` reformulation. This
sidesteps the memory note `feedback_rootedtree_nested_induction.md`
(which warns that `induction t` and `RootedTree.recOn` fail on
nested inductives) without needing the `WellFoundedRelation` /
`WellFounded.induction` machinery the strategy initially suggested.
The pattern is well-precedented (cf. `Section381.lean:811`,
`Section404.lean:1594/1982/2711`, `Section410.lean:905/942`,
`Section441B.lean:417`, `Section451.lean:316`).

**Discovery #2:** the `obtain ⟨h₁, h₂, h₃⟩ := h_vvv` + triple
`subst` pattern works for triple-conjunctive `c₁ = X ∧ c₂ = Y ∧ c₃ = Z`
conditions, mirroring the bichild double `subst`. No special handling
needed beyond chaining; the `if_pos ⟨rfl, rfl, rfl⟩` introduction
of the conjunction witness fires correctly.

**Discovery #3 (R6.B falsity):** cycle 358's
`elementaryWeightQ_phi_inv_mk` formula is the **decisive structural
evidence** that the cycle 495 scoping doc's R6.B claim is false.
This was already noted in the cycle 497 strategy §A; reconfirmed by
worker. The proper resolution is Phase α'.5.2/3 (extend
`inversePolyTree` to k ≥ 4), which is a multi-cycle effort.

## Suggested next approach

**Option A (recommended for cycle 498)**: Phase α'.5.2 scoping doc
— `tetrachildPolynomial` + `tetrachildCrossTerm` infrastructure
design. Markdown only, ~600 LOC. Mirror the cycle 402 scoping
precedent (Phase α'.5 scoping → 5-witness ladder ship). This is the
prerequisite for any eventual cycle 365 sorry closure (per §12 of
the now-updated cycle 495 scoping doc).

**Option B (alt — Phase α'.5.1 continuation)**: ship one more k=3
witness extending the cycle 491–494 ladder (mechanical, ~250–500
LOC). Useful only if cycle 498's planner judges that more
k=3 surface area is needed before scoping α'.5.2.

**Option C (alt — fresh entity pivot)**: per
`cycle_336_pivot_options.md`, pivot to def:451A, def:442A,
thm:535A, or thm:541A. Useful if the §422 cluster's marginal value
is diminishing and a fresh chapter would re-balance the streak.

The cycle 497 worker recommends Option A: it advances the §422
cluster's strategic direction toward eventual cycle 365 sorry
closure, while remaining within the standard "scoping doc as
markdown-only ship" precedent.
