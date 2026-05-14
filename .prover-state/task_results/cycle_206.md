# Cycle 206 Results

## Worked on

§380 `Equivalent.trans` — primary deliverable closing the
equivalence-relation triple (refl + symm + trans) for the def:381A
`Equivalent` predicate. Companion change: added `[CompleteSpace N]`
to the implicit instance binders of the `Equivalent` definition
itself, with the three downstream proofs that intro those binders
(`equivalent_self`, `Equivalent.symm`, `equivalent_explicitEuler_self`)
extended with one extra `_` in their `intro` patterns.

## Approach

### Planner option (b) is structurally incoherent — pivoted to option (a)

The strategy adopted option (b) — "side-hypothesis `[CompleteSpace N]`
on `trans` only, NOT by strengthening the `Equivalent` definition."
The planner's sketch was:

```lean
theorem Equivalent.trans.{u}
    {s : ℕ} {N : Type u} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [CompleteSpace N]
    {M M' M'' : RKTableau s}
    (h₁ : Equivalent.{u} (N := N) M M')
    ...
```

This presupposes `N` is a parameter of `Equivalent`, addressable
via the named-argument syntax `(N := N)`. But the actual definition
(line 968) has `N` *universally quantified inside* the proposition:

```lean
def Equivalent {s s' : ℕ} (M : RKTableau s) (M' : RKTableau s') : Prop :=
  ∀ {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (f : N → N) (L : ℝ≥0) (_hL : LipschitzWith L f) (y₀ : N), ...
```

Adding `[CompleteSpace N]` as an *outer* typeclass binder on trans is
therefore vacuous — N at the outer level is unrelated to the N bound
inside the conclusion `M.Equivalent M''`. The only path to actually
making the trans proof work (because it must invoke
`IsRKOneStep_exists` on the inner-bound N) is to attach
`[CompleteSpace N]` to that inner universal — i.e. strengthen the
`Equivalent` definition. That is option (a).

### Minimal-disruption execution of option (a)

The cost of option (a) in practice turned out to be just one extra
underscore in each of the three downstream proofs that `intro` over
Equivalent's universal binders:

* `equivalent_explicitEuler_self` (line 1153): `intro N _ _ _ f L _hL y₀`
* `equivalent_self` (line 1784): `intro N _ _ _ f L hL y₀`
* `Equivalent.symm` (line 1820): `intro N _ _ _ f L hL y₀`

`paddedEuler_equivalent_self` (line 1936) requires no change — it
just calls `paddedEuler.equivalent_self`, and the instance binder is
introduced internally. All four theorems remain axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

### Equivalent.trans body recipe

The proof body (~30 LOC) follows cycle 203's `equivalent_self`
threshold-construction recipe verbatim, applied to the middle
method `M'`:

1. After `intro N _ _ _ f L hL y₀`, obtain
   `⟨h₀₁, h₀₁_pos, hConcl₁⟩` from `h₁ f L hL y₀` and
   `⟨h₀₂, h₀₂_pos, hConcl₂⟩` from `h₂ f L hL y₀`.
2. Set `C_M' := ∑ᵢⱼ |M'.A i j|`, `h₀_M' := 1 / (2 * (L * C_M' + 1))`.
3. Refine the existential with `min h₀₁ (min h₀₂ h₀_M')`.
4. After intro of `h, hh_pos, hh_le, y₁, y₃, hY₁, hY₃`, derive
   `hh_le_M' : h ≤ h₀_M'` via two `min_le_right`/`min_le_left`
   chain hops, then `h_small_M' : |h| * L * C_M' < 1` via
   `abs_of_pos + le_div_iff₀ + nlinarith` (the cycle 203 recipe).
5. Apply `M'.IsRKOneStep_exists h hL y₀ h_small_M'` to obtain a
   middle output `y₂` with `hY₂ : M'.IsRKOneStep f y₀ h y₂`.
6. Close `y₁ = y₃` via `calc`:
   * `y₁ = y₂` from `hConcl₁ h hh_pos hh_le_₁ y₁ y₂ hY₁ hY₂`
   * `y₂ = y₃` from `hConcl₂ h hh_pos hh_le_₂ y₂ y₃ hY₂ hY₃`

Universe annotation `.{u}` applied to the theorem and to every
`@Equivalent.{u}` reference (per cycle 204's discovery that
`Equivalent` is universe-polymorphic and auto-bound universes pick
fresh levels per reference).

## Result

**SUCCESS** — `Equivalent.trans` shipped, axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

Verification status across the relevant theorems:

| Theorem | Axioms | Status |
| --- | --- | --- |
| `Equivalent.trans` (new, cycle 206) | propext / Classical.choice / Quot.sound | ✓ axiom-clean |
| `Equivalent.symm` (cycle 204) | propext / Classical.choice / Quot.sound | ✓ unchanged |
| `equivalent_self` (cycle 203) | propext / Classical.choice / Quot.sound | ✓ unchanged |
| `equivalent_explicitEuler_self` (cycle 030) | propext / Classical.choice / Quot.sound | ✓ unchanged |
| `paddedEuler_equivalent_self` (cycle 204) | propext / Classical.choice / Quot.sound | ✓ unchanged |

`lake env lean OpenMath/Chapter3/Section381.lean` exits 0 with only
two pre-existing `unused variable` warnings (lines 577, 1979 —
unrelated to this cycle). Sorry count remains 0. Tautology scanner
clean. Equivalence-relation triple (refl + symm + trans) for
`Equivalent` now complete.

## Faithfulness check

### Modified def: `Equivalent` (Section381.lean:968)

* Entity ID: `def:381A`
* Textbook statement (quoted from `extraction/formalization_data/entities/def_381A.json`):
  > Two Runge–Kutta methods are *equivalent* if, given any
  > differential equation [...] satisfying a Lipschitz condition,
  > and given a value for h sufficiently small, they yield identical
  > results for any initial value y₀.
* Lean statement captures: **same content with one extra
  implementation hypothesis `[CompleteSpace N]`** on the universal
  over `N`.
* Justification for divergence: Butcher §380 works informally over
  ℝⁿ (or implicitly any complete normed space) and does not
  explicitly impose completeness. The Banach fixed-point existence
  step (`IsRKOneStep_exists`, cycle 205) used inside `trans` is
  vacuous without completeness — the implicit-stage system has no
  solutions in an incomplete normed space at non-trivial `h`. Every
  concrete RK method of interest over ℝⁿ has `CompleteSpace`
  automatic via Mathlib's instance database (`Real.instCompleteSpace`,
  `Pi.completeSpace`, finite-dim instances), so this is a no-op
  caller burden. Documented inline in the `Equivalent` docstring.

### New theorem: `Equivalent.trans` (Section381.lean:1825+)

* Entity ID: no direct `thm:` ID — closes the trans direction of
  the def:381A equivalence-relation closure (a textbook-implicit
  property: §380 talks about equivalence informally as an
  equivalence relation).
* Statement: `Equivalent M M' → Equivalent M' M'' → Equivalent M M''`.
* Lean statement captures: textbook-content trans of equivalence.
* Hypothesis strength check: takes only the two equivalences as
  inputs (and the `[CompleteSpace N]` built into Equivalent). No
  extra hypotheses beyond what is mathematically required.
* Tautology check: conclusion `M.Equivalent M''` is not among
  the hypotheses `M.Equivalent M'` and `M'.Equivalent M''`. ✓
* Identity check: proof is NOT `exact h₁` or `exact h₂` — it
  constructs the chain through a middle existence witness via
  `IsRKOneStep_exists`. ✓
* Absent theorem check: no promised content is unwritten. ✓

## Dead ends

### Attempt to interpret option (b) literally

I spent significant analysis on whether the planner's option (b)
could be implemented without modifying the Equivalent def:

1. **Outer `[CompleteSpace N]` typeclass on trans only**: N at the
   outer level is unrelated to the N introduced by the conclusion's
   `intro N _ _ ...`. The outer instance is not in scope when we
   need to invoke `IsRKOneStep_exists`. **Vacuous.**
2. **Universal propositional hypothesis `∀ {N : Type*} [...],
   CompleteSpace N`**: would technically work, but the hypothesis
   is a strong universal claim that is *false in general* (incomplete
   normed spaces exist). The trans theorem would be unusable in
   practice. **Rejected.**
3. **Restate trans's conclusion as per-N**: `∀ f L y₀, ∃ h₀, ...`
   restricted to a specific N satisfying `[CompleteSpace N]`. This
   works but does NOT give `M.Equivalent M''` as the conclusion —
   it gives a weaker per-N statement, so it does NOT close the
   equivalence-relation triple for `Equivalent`. **Rejected.**

Pivoted to option (a). See "Approach" section above.

## Discovery

### Planner option (b) was structurally incoherent

When a planner strategy proposes adding `[CompleteSpace N]` as a
side-hypothesis to a theorem whose conclusion universally quantifies
over `N`, the side-hypothesis is vacuous unless `N` is a *parameter*
of the conclusion (e.g. by lifting the universal out of the
proposition). The planner sketch wrote `Equivalent.{u} (N := N) M M'`
— this syntax requires Equivalent to take N as a named parameter,
which it does not. Future planner cycles should verify the
parameter/quantifier structure of the predicate before specifying
side-hypothesis strategies.

### CompleteSpace addition was structurally cheap

Adding `[CompleteSpace N]` to Equivalent's internal instance binders
cost only one extra `_` per downstream `intro` site (3 sites total),
preserved all existing axiom-clean witnesses, and unblocked trans.
The planner's concern about "multi-cycle risk if a downstream witness
inadvertently relies on the un-strengthened def" did not materialise
— Mathlib's instance database picks up `CompleteSpace ℝ` and
`CompleteSpace (Fin n → ℝ)` automatically, so concrete witnesses
like `equivalent_explicitEuler_self` and `paddedEuler_equivalent_self`
synthesize through transparently.

### `Equivalent` is now a proper equivalence relation on complete spaces

With refl (cycle 203) + symm (cycle 204) + trans (cycle 206) all
axiom-clean and matching the textbook def:381A predicate up to
the `[CompleteSpace N]` implementation hypothesis, `Equivalent` is
formally an equivalence relation on `Σ s, RKTableau s` over
complete normed ℝ-spaces. Cycle 207+ can promote this to a Setoid
instance if useful.

## Suggested next approach

### Cycle 207 (primary candidate): `PReducesTo → Equivalent`

This is the deferred direction (2) of `thm:381H`. With cycle 205's
`IsRKOneStep_exists` and cycle 206's `Equivalent.trans` in hand, the
load-bearing prerequisites are complete. The remaining work is the
iteration-invariant "Yᵢ⁽ᵏ⁾ = Yⱼ⁽ᵏ⁾ for `i, j` in the same partition
block under fixed-point iteration of the stage map", which is likely
2–3 cycles.

### Alternative pivots (lower priority)

* **Setoid promotion**: write `Equivalent.setoid : Setoid (Σ s, RKTableau s)`
  (over a fixed complete-normed-space context) to make the
  equivalence-relation structure available to typeclass machinery.
  Trivial (~5 LOC) but mostly cosmetic value.
* **`paddedEuler` non-vacuity for `IsRKOneStep_exists`**: cycle
  205/206 stretch deliverable, skipped this cycle. ~5 LOC.
* **`thm:382A`, `thm:382B`, `thm:384A`, `thm:386A`**: fresh §380/§382
  entities to open new sub-clusters.

### §441 Phase C.2

Loop-maintainer territory; 26th consecutive cycle skipped. No worker
action.
