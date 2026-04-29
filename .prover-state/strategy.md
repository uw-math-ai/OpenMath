# Cycle 031 Strategy

## Status going in

* No pending Aristotle results.
* No sorry's anywhere in `OpenMath/`.
* Cycle 030 closed `def:381A` (`OpenMath/Chapter3/Section381.lean`,
  commit `79da1db`). Branch tip is clean.
* Cycle 030's "Suggested next approach" was `def:381F`. **We are
  overriding that suggestion** — see §"Why not def:381F" below.

## Target this cycle

**`def:323A` — *internal order q* (Butcher §323, page 203).**

Entity file: `extraction/formalization_data/entities/def_323A.json`.
Textbook statement (quoted verbatim from the JSON):

> Consider a Runge–Kutta method given by the tableau c A / b. For a
> tree `t` and stage `i`, let `Φᵢ(t)` denote the elementary weight
> associated with `t` for the tableau `[c A / eᵢ A]`. Stage `i` has
> 'internal order `q`', if for all trees such that `r(t) ≤ q`,
> `Φᵢ(t) = cᵢ^{r(t)} / γ(t)`.

This is a clean predicate over an existing tableau, reusing the
§312 `internalWeight`, the §301 `density`, and the §310/§301
`order`. No new infrastructure required; no analysis (no Lipschitz,
no inner product). One cycle should comfortably deliver definition
+ witness + axiom check.

### Where to put it

New file: `OpenMath/Chapter3/Section323.lean`.

Imports needed:
* `OpenMath.Chapter3.Section301` (for `RootedTree.density`)
* `OpenMath.Chapter3.Section312` (for `RKTableau`, `internalWeight`)

Use the namespace pattern of `Section381.lean` — definitions in
`namespace OpenMath.Chapter3.Section312.RKTableau` so
`M.HasInternalOrder i q` works via dot notation. Look at
`Section357.lean` and `Section381.lean` for the prevailing
convention.

### Notational clarification (do this BEFORE writing code)

Butcher uses two clashing notations for `Φᵢ(t)`. In §312 it is the
*internal weight* (`Σⱼ aᵢⱼ (Φⱼ D)(t)`, our
`RKTableau.internalWeight t i`). In §323 the textbook re-introduces
`Φᵢ(t)` via "the elementary weight of the auxiliary tableau
`[c A / eᵢ A]`", which expands to `Σⱼ (eᵢ)ⱼ (Φⱼ D)(t) = (Φᵢ D)(t)`
of the *original* tableau (`derivativeWeight`).

These two would normally disagree, but Butcher's textbook line
(`extraction/raw_text/ch03.txt:2465`)

> internal order 1 is equivalent to `cᵢ = Σⱼ aᵢⱼ`

settles which one §323 means. `cᵢ = Σⱼ aᵢⱼ = M.internalWeight τ i`,
so **Butcher's Φᵢ(t) in §323 is `M.internalWeight t i`**. This
matches §312's primary use of the symbol, even if the
auxiliary-tableau phrasing is confusing.

Document this notational decision explicitly in the file's `/-! -/`
docstring with a quote of `extraction/raw_text/ch03.txt:2465` as
justification. This is the kind of subtle reading that the
faithfulness checklist exists to catch.

### Lean signature

```lean
namespace OpenMath.Chapter3.Section312.RKTableau

open OpenMath.Chapter3.Section310 OpenMath.Chapter3.Section312

/-- Butcher §323 Definition 323A — stage `i` of the Runge–Kutta
method `M` has *internal order* `q` if for every rooted tree `t`
with `t.order ≤ q`, the internal weight `Φᵢ(t)` equals
`(M.c i)^t.order / t.density`. -/
def HasInternalOrder {s : ℕ} (M : RKTableau s) (i : Fin s) (q : ℕ) :
    Prop :=
  ∀ t : RootedTree, t.order ≤ q →
    M.internalWeight t i = (M.c i) ^ t.order / (t.density : ℝ)

end OpenMath.Chapter3.Section312.RKTableau
```

Notes:
* Verify the type of `RootedTree.density` with `lean_hover_info`
  *before* writing the cast. If it is `ℕ`, the `(t.density : ℝ)`
  coercion is needed; if it is already `ℝ`, drop it.
* `(M.c i) ^ t.order` is `ℝ`-valued; `t.order : ℕ`, so this is
  natural-number power on `ℝ` (via `HPow.hPow` / `Monoid.npow`).
* `M.c i : ℝ` already (from `Section312`'s `RKTableau` definition).

### Witness — explicit Euler at stage 0 has internal order 1

Reasoning:
* For `t.order = 1` (only tree of order ≤ 1, since `order ≥ 1` for
  every rooted tree): `internalWeight t 0 = Σⱼ A 0 j * derivativeWeight j t`.
  For explicit Euler, `A = 0`, so this is `0`.
  `(c 0)^t.order / γ(t) = 0^1 / γ(t) = 0`. So both sides are `0`. ✓

```lean
/-- Witness — stage 0 of explicit Euler has internal order 1. -/
theorem explicitEuler_hasInternalOrder_one :
    RKTableau.explicitEuler.HasInternalOrder 0 1 := by
  intro t ht
  simp [RKTableau.explicitEuler, internalWeight]
  -- both sides reduce to `0` because `A = 0` and `c 0 = 0`
  ...
```

For the proof, prefer the "no case-analysis" path: show the LHS is
`0` (because explicit Euler has `A = 0`), show the RHS is `0`
(because `c 0 = 0` and `0^k = 0` for `k ≥ 1`), close. Use
`Section381.lean`'s `equivalent_explicitEuler_self` (lines 496–512)
as the style template — unfold via
`simp [RKTableau.explicitEuler, ...]`, then close arithmetic.

If the `0^t.order = 0` step needs `t.order ≥ 1`, you can either:

(a) Use `Nat.pos_of_ne_zero` from `RootedTree.order_pos` if a lemma
    of that name exists in `Section301.lean` or `Section310.lean`
    (search with `lean_local_search "order_pos"` or
    `lean_local_search "RootedTree.order"`).
(b) Prove a small inline helper:
    `have hpos : 0 < t.order := by ...` using whatever recursive
    structure `order` has (it returns `1 + sum_of_children` so it
    is always ≥ 1).

### Optional extension if time permits

If the witness above is fast, also provide the *vacuous* `q = 0`
witness for arbitrary `M`:

```lean
theorem hasInternalOrder_zero {s : ℕ} (M : RKTableau s) (i : Fin s) :
    M.HasInternalOrder i 0 := by
  intro t ht
  -- `t.order ≥ 1` and `t.order ≤ 0` are contradictory
  ...
```

This is a free lemma if you've already discovered the
`t.order ≥ 1` lemma above. Skip if it slows you down.

### Faithfulness checklist (run before commit)

* Open `extraction/formalization_data/entities/def_323A.json` —
  quote the textbook in the docstring.
* Confirm the Lean predicate matches: "for all trees with
  `r(t) ≤ q`, `Φᵢ(t) = cᵢ^{r(t)} / γ(t)`". We are using
  `internalWeight t i` for `Φᵢ(t)`, justified by the §323 line at
  `extraction/raw_text/ch03.txt:2465`. Document this.
* Tautology check: conclusion is the equation
  `internalWeight = …`, which is **not** a hypothesis (the
  hypothesis is just `t.order ≤ q`). Pass.
* Hypothesis-strength check: textbook quantifies over "all trees
  such that `r(t) ≤ q`" — we do the same. Pass.
* Witness identity check: `explicitEuler_hasInternalOrder_one` is
  not vacuous (it requires showing `0 = 0^1 / γ(τ) = 0`).

### Commit checklist

1. `lake env lean OpenMath/Chapter3/Section323.lean` clean.
2. `lake build` clean.
3. Add `import OpenMath.Chapter3.Section323` to `OpenMath.lean` (the
   project root) so the new file participates in `lake build`. Read
   `OpenMath.lean` first to see the existing import list.
4. Update `extraction/formalization_data/lean_status.json` —
   `def:323A` → `formalized`, with `lean_file` and `lean_symbol`
   pointing to the new file.
5. Update `plan.md` — flip `def:323A` row from `[ ]` to `[x]`,
   bump progress counter `31 → 32`.
6. Axiom check on the witness:
   ```
   #print axioms OpenMath.Chapter3.Section312.RKTableau.explicitEuler_hasInternalOrder_one
   ```
   Expect `[propext, Classical.choice, Quot.sound]` only.
7. Write `.prover-state/task_results/cycle_031.md` per CLAUDE.md
   format.
8. Commit with message "Formalize def:323A — internal order q for
   Runge-Kutta stages" and push.

## Why not `def:381F` (despite cycle 030's suggestion)

The cycle 030 worker proposed encoding "P-equivalent" as "their
P-reduced methods are Φ-equivalent". This is **not** the textbook
definition. Butcher def:381F (`def_381F.json`) reads:

> Two Runge–Kutta methods are 'P-equivalent' if each of them
> reduces to the same reduced method.

"Reduced method" is the def:381E construction (P-reduction
followed by 0-reduction, possibly iterated), which is **deferred**
per `.prover-state/issues/reduced_method_deferred.md`. That issue
explicitly identifies def:381F as the first consumer that
"genuinely requires" the deferred construction.

The cycle 030 paraphrase (P-reduced + Φ-equivalent) is a
*non-trivial reformulation*, not a faithful definition. It would
either need:

* A proved equivalence lemma between the two formulations
  (substantial — requires reasoning about the iterated reduction
  fixpoint), or
* Treating it as "definition smuggling" — encoding the cycle 030
  paraphrase as the definition and claiming it is faithful, which
  it is not without a proof.

CLAUDE.md is explicit:

> If you use an equivalent formulation, add an explicit equivalence
> lemma.

The proper resolution of def:381F is the multi-cycle plan in
`.prover-state/issues/reduced_method_deferred.md`:

1. (Cycle X+0) Resolve Q1 (irreducible base case) and Q2 (single
   step vs iterate) by re-reading `extraction/raw_text/ch03.txt`
   §380.
2. (Cycle X+1) Build `reducedMethod : RKTableau s → Σ s', RKTableau s'`
   via well-founded recursion on stage count. Likely needs
   `Classical.choose`-based partition extraction and a
   strict-decrease lemma per reduction step.
3. (Cycle X+2) Formalize `def:381F` as
   `reducedMethod M = reducedMethod M'` (modulo dependent-pair
   equality / Φ-equivalence on the result).

This is not a one-cycle deliverable. **Defer def:381F until a
dedicated multi-cycle plan is queued. Do not attempt the cycle 030
paraphrase.**

## What NOT to try this cycle

* **Do NOT formalize `def:381F`** via any single-step encoding. See
  above; the textbook says "reduced method", not "P-reduced
  method".
* **Do NOT build the `reducedMethod` construction** as a side
  effort to def:323A. It is multi-cycle infrastructure deserving
  its own dedicated cycle(s).
* **Do NOT attempt `def:357A` (BN-stability) this cycle.** It is a
  reasonable alternative target but it requires (a) a non-autonomous
  one-step predicate (new infrastructure parallel to `IsRKOneStep`
  from §381), (b) an inner-product-space witness (implicit midpoint
  via `‖y₁‖² - ‖y₀‖² = 2h ⟨f(m), m⟩`), and (c) deciding whether to
  anchor on `Equivalent`-style predicate quantification or build a
  multi-step iterate. Feasible in one cycle but riskier than
  def:323A and has more design decisions. Park for cycle 032 if
  def:323A finishes early — see "After def:323A" below.
* **Do NOT** attempt `lem:383C` (existence of left/right inverses).
  It depends on the Runge–Kutta group infrastructure (`thm:382A`,
  `thm:382B`, `lem:383A`) which is not yet built.
* **Do NOT** raise `maxHeartbeats` above 200000 (CLAUDE.md rule).
* **Do NOT** introduce `axiom` or `constant` declarations.
* **Do NOT** edit `extraction/raw_text/` or
  `extraction/formalization_data/entities/`. Both are regenerated.
* **Do NOT** edit `scripts/autonomous_loop.py`. The tautology
  scanner false-positive issue
  (`.prover-state/issues/tautology_scanner_false_positives.md`)
  remains the loop maintainer's responsibility.

## After def:323A (stretch goal, only if main target lands ahead of schedule)

If def:323A is committed and clean with time to spare:

1. Generalised `hasInternalOrder_zero {s} (M : RKTableau s) (i : Fin s) :
   M.HasInternalOrder i 0` if not done inline.
2. Internal order is downward-closed:
   `M.HasInternalOrder i (q+1) → M.HasInternalOrder i q`.
3. *(Exploratory only — do NOT commit half-finished)* — sketch
   `def:357A` (BN-stability) in a new
   `OpenMath/Chapter3/Section357A.lean` (separate from the existing
   `Section357.lean` which holds def:357B). Define a non-autonomous
   one-step predicate `IsRKOneStepNonauto M f x₀ y₀ h y₁` mirroring
   `IsRKOneStep` from `Section381.lean`. If you write any sorry's,
   do NOT commit them; either close them or revert the file.

Submit each as a separate Aristotle job from the project root with
`mcp__aristotle__submit_prompt` (or `submit_file` if you've
written a sorry stub). Sleep 30 min, check results, incorporate.
**Do not poll repeatedly.**

## Aristotle batch (this cycle)

If def:323A's witness proof stalls beyond ~10 minutes of focused
attempts, batch-submit to Aristotle:

* The witness `explicitEuler_hasInternalOrder_one`, stated with
  `sorry` (sub-lemmas if useful: "0^t.order = 0 when t.order ≥ 1",
  "internalWeight t i = 0 when M.A = 0").
* The `hasInternalOrder_zero` general lemma if you sketched it.

Use `mcp__aristotle__submit_file` against the file with the
`sorry`'s in place. Sleep 30 min. Check via
`mcp__aristotle__list_projects` once. Do not poll.

If the witness proof is closing cleanly by hand (likely — it's a
short `simp` after unfolding explicit Euler), skip Aristotle for
this cycle.

## Open issue audit (do NOT pick these up this cycle)

Reviewed the issue files in `.prover-state/issues/`:

* `AN_stability_deferred.md` — needs complex matrix resolvent
  infrastructure. Multi-cycle. Park.
* `equivalent_self_general_deferred.md` — needs Banach contraction
  for implicit-stage uniqueness. Multi-cycle. Park.
* `reduced_method_deferred.md` — see "Why not def:381F" above.
  Multi-cycle. Park.
* `picard_lindelof_bound_strengthening.md` — Chapter 1 leftover;
  not on the §3 critical path. Park.
* `jordan_canonical_form_missing.md` — Chapter 1 §142 leftover;
  not on the §3 critical path. Park.
* `symmetry_group_equivalence.md` — faithfulness divergence on σ;
  not blocking. Park.
* `tautology_scanner_false_positives.md` — loop maintainer
  responsibility, NOT worker. Do not edit `scripts/`.
* `consultant_advice_cycle_009.md`, `consultant_advice_cycle_014.md`,
  `consultant_advice_cycle_015.md` — historical consultant notes;
  no actions needed.

Each parked issue should remain parked until either (a) a
downstream theorem we are about to formalize *genuinely* requires
it, or (b) a dedicated multi-cycle plan is scheduled. None apply
to this cycle.
