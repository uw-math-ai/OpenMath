# Cycle 082 Strategy

## Context — what just happened

Cycle 081 closed `lem:383C` cleanly (existence of convolution inverse in
G₁). Five new theorems landed in `OpenMath/Chapter3/Section383.lean`,
all on baseline axioms only. Progress 52 → 53/175.

The cycle 081 worker also **escalated** a faithfulness concern in
[`.prover-state/issues/convolution_vertex_vs_multiset.md`](issues/convolution_vertex_vs_multiset.md):
our `convProduct` (cycle 077–078) uses *multiset sub-selection*, while
Butcher §383 (page 287) uses *vertex-subset partition*. The two
diverge on single-tree forests of order > 1. The worker's
`convInverse` is a closed-form witness in our (multiset-graded)
algebra; Butcher's α⁻¹ would involve a sum over vertex-subset
partitions (lem:383D). The worker explicitly asked the planner to
decide whether to refactor `convProduct` before further §383 work.

## Priority 0 — Planner decision on the convolution divergence (5 min)

**Decision: Option (b) from the issue file — defer the refactor and
document the divergence.**

Rationale:
* Option (a) (refactor `convProduct` to use vertex-subset partition)
  is multi-cycle and invalidates cycles 077–081's work. It would
  unblock `lem:383D` and `thm:386A` but cost the entire group-axiom
  chain we just built.
* Our current convolution defines a valid graded-multiplicative
  algebra. The cycle 077–081 lemmas (multiplicativity preservation,
  associativity, identity, inverse existence) are all sound *in this
  algebra* — they are not a faithful encoding of Butcher's exact
  Hopf-algebra structure, but they are mathematically correct
  statements about a related algebra.
* `lem:383D` and `thm:386A` are explicitly **out of scope** for the
  next several cycles per this decision. Do not attempt them.
* `thm:382A` (the Runge–Kutta group theorem) is about RK tableaux
  and equivalence classes, *not* about forest mappings. It is
  **not** blocked by the convolution divergence — but it is blocked
  by missing infrastructure (RK composition, equivalence-class
  quotient, Lipschitz arguments). Out of scope this cycle.

**Worker actions for Priority 0**:

1. Add a file-level docstring at the very top of
   `OpenMath/Chapter3/Section383.lean` (in the existing `/-! ... -/`
   block — extend it; do not start a new block) summarising:
   * Our convolution `convProduct` uses *multiset sub-selection*
     `R ≤ S` on `Multiset RootedTree`, not Butcher's *vertex-subset*
     `R ⊑ S`.
   * The two agree only when every tree in `S` has order 1
     (no edges).
   * Lemmas 383A, 383B, 383C are proved here in the multiset-graded
     algebra; they hold also in Butcher's true convolution but the
     cycle 077–081 proofs do not constitute a faithful encoding of
     Butcher's argument for the latter.
   * `lem:383D`, `thm:386A`, and any partition-sum / Hopf-algebra
     content require the vertex-subset refactor and are deferred.
   * Cross-link to `.prover-state/issues/convolution_vertex_vs_multiset.md`.

2. Append a **"Status (cycle 082)"** subsection to
   `.prover-state/issues/convolution_vertex_vs_multiset.md` recording
   the planner decision: "Option (b) adopted; refactor deferred until
   `lem:383D`/`thm:386A` becomes blocking."

## Priority 1 — Identity laws + `inverse_unique` (~60 min total)

These three lemmas finish the §383 group-axiom infrastructure. Each
is short (<20 lines) and the chain unblocks any future Group
packaging.

### 1a. `convProduct_one_left` and `convProduct_one_right` (~30 min)

**Statement** (append to `Section383.lean` after
`convProduct_convInverse_symm`, before `exists_inverse_of_isMultiplicative`):

```lean
/-- The convolution-product identity is a left identity: `1 · α = α`. -/
theorem convProduct_one_left (α : Forest → ℝ) :
    convProduct convOne α = α := by
  funext S
  -- convProduct convOne α S = ∑ R ≤ S, convOne (S - R) * α R
  -- convOne (S - R) is 1 when S - R = 0 (i.e. R = S), else 0.
  -- So the sum reduces to convOne 0 * α S = 1 * α S = α S.
  sorry

/-- The convolution-product identity is a right identity: `α · 1 = α`. -/
theorem convProduct_one_right (α : Forest → ℝ) :
    convProduct α convOne = α := by
  funext S
  -- convProduct α convOne S = ∑ R ≤ S, α (S - R) * convOne R
  -- convOne R is 1 when R = 0, else 0.
  -- So the sum reduces to α S * convOne 0 = α S * 1 = α S.
  sorry
```

**Proof strategy** (mechanical):

* `convOne` is defined as the indicator of the empty multiset
  (`if F = 0 then 1 else 0` or equivalent — read the source at
  `Section383.lean:357` and consult the existing `simp` unfolds in
  `isMultiplicative_convOne` proof at line 378).
* For the **right** identity: the sum
  `∑ R ∈ S.powerset, α (S - R) * convOne R` has only the `R = 0`
  summand non-zero (since `convOne R = 0` for `R ≠ 0`). At `R = 0`:
  `α (S - 0) * convOne 0 = α S * 1 = α S`. Use
  `Multiset.sum_eq_zero_iff` or pick out the unique non-zero summand
  with `Finset.sum_eq_single` / `Multiset.sum_map_eq_single`
  (whichever fits the underlying iteration).
* For the **left** identity: same shape, but the unique non-zero
  summand is `R = S` (so that `S - R = 0`).
* If you find Mathlib doesn't have the right "sum-eq-single" lemma
  for `Multiset.powerset`, the cleanest path is to manually split
  `S.powerset` as `{S} + (S.powerset.erase S)` (or `{0} + ...` for
  the right identity) and use `Multiset.sum_cons` /
  `Multiset.sum_erase`. Look at how cycle 080's
  `convProduct_assoc_lhs_eq` (Section383.lean:307) and cycle 081's
  `convProduct_singleton_eq_zero` (Section383.lean:414) crack open
  the powerset — those are the precedents for the same shape of
  unfold.

**Hypothesis note**: the `(hα : IsMultiplicative α)` hypothesis is
NOT needed — these are pure unfolding lemmas (the convolution-product
formula reduces by `convOne`'s indicator behaviour without needing
multiplicativity of `α`). Statements above already drop the
hypothesis.

### 1b. `inverse_unique` (~15 min, mechanical)

**Statement** (append after the identity laws):

```lean
/-- Uniqueness of two-sided inverses in the convolution algebra.

If `β` and `γ` are both two-sided inverses of `α` (with respect to
`convOne`), then `β = γ`. The standard group-theoretic argument
`γ = γ · 1 = γ · (α · β) = (γ · α) · β = 1 · β = β`. -/
theorem inverse_unique {α β γ : Forest → ℝ}
    (hαβ : convProduct α β = convOne)
    (hγα : convProduct γ α = convOne) :
    β = γ := by
  calc β = convProduct convOne β := (convProduct_one_left β).symm
    _ = convProduct (convProduct γ α) β := by rw [hγα]
    _ = convProduct γ (convProduct α β) := convProduct_assoc γ α β
    _ = convProduct γ convOne := by rw [hαβ]
    _ = γ := convProduct_one_right γ
```

No multiplicative hypotheses needed (matches §1a).

### 1c. `convInverse_convInverse` corollary (stretch; ~10 min)

```lean
/-- Inverse is involutive: `(α⁻¹)⁻¹ = α` for multiplicative α. -/
theorem convInverse_convInverse {α : Forest → ℝ}
    (hα : IsMultiplicative α) :
    convInverse (convInverse α) = α := by
  -- α and convInverse (convInverse α) are both two-sided inverses
  -- of convInverse α; uniqueness forces them equal.
  refine inverse_unique ?_ ?_
  · -- convProduct (convInverse α) (convInverse (convInverse α)) = convOne
    exact convProduct_convInverse (convInverse_isMultiplicative α)
  · -- convProduct α (convInverse α) = convOne
    exact convProduct_convInverse hα
```

**Orientation check** (do verify this on paper before encoding):
`inverse_unique hαβ hγα : β = γ`. We want to conclude
`convInverse (convInverse α) = α`. Set
* `α := convInverse α` (the "α" in `inverse_unique`),
* `β := convInverse (convInverse α)`,
* `γ := α`.
Then `hαβ` is
`convProduct (convInverse α) (convInverse (convInverse α)) = convOne`
(right-inverse property applied to `convInverse α`), and `hγα` is
`convProduct α (convInverse α) = convOne` (right-inverse property of
`α`). Both hold; the conclusion `β = γ` is
`convInverse (convInverse α) = α`. ✓

If the orientation comes out reversed, the fix is `(... ).symm` on
the conclusion.

Faithfulness check for all three: pure algebraic consequences of
existing theorems; tautology check passes (conclusions don't appear
verbatim in hypotheses); identity check passes (proofs do real
algebraic work via `calc` / `inverse_unique`).

## Priority 2 — Verify and commit (~15 min)

* Run `lake env lean OpenMath/Chapter3/Section383.lean` — must be
  clean.
* Run `lake build OpenMath.Chapter3.Section383` — must succeed.
  (Reminder from cycle 072: `lake env lean <file>` does NOT update
  the .olean cache, so use `lake build` before `#print axioms` to
  avoid stale-cache `sorryAx` false positives.)
* `#print axioms convProduct_one_left convProduct_one_right
  inverse_unique` (and `convInverse_convInverse` if landed) — must
  show only `[propext, Classical.choice, Quot.sound]`.
* No `sorry`s anywhere in the file.
* `extraction/formalization_data/lean_status.json`: no entity status
  changes (these are helper lemmas, not textbook entities). No edit
  needed.
* Commit with message:
  `Cycle 082 — convolution algebra identity + inverse uniqueness; document multiset/partition divergence`

## Priority 3 — DO NOT submit Aristotle this cycle

Per cycle 080 + 081 discoveries (recorded in their task results),
manual proofs of small algebraic identity lemmas (~20 lines each)
finish faster than an Aristotle round-trip. The Priority 1 lemmas
are all in this category.

If Priority 1 stalls badly (e.g., the multiset-powerset
sum-eq-single argument can't be cleanly assembled in 30 min), only
*then* batch-submit `convProduct_one_right` to Aristotle and pivot
to manual work on `convProduct_one_left` + `inverse_unique` while
waiting. Default plan: skip Aristotle entirely.

## Priority 4 — Cycle 083 scoping (~5 min if everything else closes)

Once Priority 1 + 2 land, the §383 algebraic infrastructure is
**done** for this convolution. The next §380-area target needs
fresh infrastructure:

* `thm:382A` (RK group well-defined-ness): needs RK composition
  (`composedMethod : RKTableau s₁ → RKTableau s₂ → RKTableau (s₁+s₂)`)
  and a Lipschitz-based equality-of-output argument. **Heavy** —
  multiple cycles. Not blocked by the convolution divergence.
* `thm:381G` (Irreducible RK Stage Distinguishability): blocked by
  `thm:314A` (Independence of elementary differentials), itself
  blocked by `lem:311A`/`thm:311B/C/D`. Heavy.
* `thm:343B` (Reflected order conditions preservation): requires
  formalising B(η), C(η), D(η), E(η,ζ) simplifying assumptions.
  Heavy.

**Action**: do NOT pre-commit cycle 083 to any of these. Use the
slack to read the following entity files and write a one-line scope
estimate for each in `.prover-state/task_results/cycle_082.md`
§"Suggested next approach":

* `extraction/formalization_data/entities/lem_311A.json`
  (foundational §311 entry — Taylor expansion of exact solution).
* `extraction/formalization_data/entities/thm_441A.json` (Chapter 4
  §441, possibly cleaner than §380 — max order for convergent
  k-step methods).
* `extraction/formalization_data/entities/def_422B.json`
  (Chapter 4 §422 entry — a definition, may be tractable in one
  cycle).
* `extraction/formalization_data/entities/lem_322A.json` (§322
  methods of order 4 — Chapter 3 algebraic, may avoid the
  elementary-differential infrastructure).

Let the next planner cycle pick from your scoping notes.

## What NOT to do this cycle

* **Do NOT refactor `convProduct`** to use vertex-subset partition.
  Per the Priority 0 decision, this is option (a) and is deferred.
  The refactor would invalidate the entire cycle 077–081 chain and
  is multi-cycle.
* **Do NOT attempt `lem:383D`** (partition-sum inverse formula).
  Per the convolution caveat, our closed-form inverse from cycle 081
  is the right object in our algebra; lem:383D's textbook formula
  presupposes the vertex-subset convolution.
* **Do NOT attempt `thm:386A`** (recursive product formula). Same
  blocker as `lem:383D`.
* **Do NOT attempt `thm:382A`, `thm:381G`, or `thm:343B`** this
  cycle. All three need fresh multi-cycle infrastructure
  (RK composition, elementary-differential independence, simplifying
  assumptions B/C/D/E respectively).
* **Do NOT submit Aristotle for the Priority 1 lemmas** unless they
  stall hard. These are short, manual, and well-targeted; a 30-min
  Aristotle wait dominates their actual proof time.
* **Do NOT introduce `axiom` or `constant`** for any "the multiset
  sum-eq-single lemma is missing from Mathlib" gap. If Mathlib's
  `Multiset.powerset` summation API is genuinely thin, build the
  one-line helper you need as a private lemma in `Section383.lean`
  (e.g., a small lemma extracting the unique non-zero summand).
* **Do NOT raise `maxHeartbeats`**.
* **Do NOT touch `scripts/autonomous_loop.py`** or any other
  loop-infrastructure file (per the standing scanner false-positive
  issue and CLAUDE.md).
* **Do NOT skip the file-level docstring update** in Priority 0.
  The convolution divergence is now a documented project-level
  decision; the file must reflect it so future readers (planner +
  worker) don't accidentally try `lem:383D`.

## Faithfulness checks for new lemmas

For `convProduct_one_left`, `convProduct_one_right`,
`inverse_unique`, `convInverse_convInverse`:

* No textbook entity IDs (helpers).
* All four are standard group-theoretic identities; their
  truth in our convolution algebra follows from cycles 077–081.
* Tautology check: each conclusion does not appear verbatim as a
  hypothesis. ✓
* Identity check: each proof does genuine algebraic work via `calc`
  / `Multiset.sum_eq_single` / `convProduct_assoc`. None is a bare
  `exact h` re-export. ✓
* Hypothesis strength: identity laws drop `IsMultiplicative` (pure
  unfolding); `inverse_unique` drops it too; `convInverse_convInverse`
  legitimately needs `IsMultiplicative` because `convProduct_convInverse`
  requires it.

For the file-level docstring update: not a theorem; a documentation
change. Faithfulness to the convolution-divergence decision is the
content.

## Estimated effort budget

| Priority | Task | Time |
|---|---|---|
| 0 | Convolution doc + issue update | 5 min |
| 1a | `convProduct_one_left` + `convProduct_one_right` | 30 min |
| 1b | `inverse_unique` | 15 min |
| 1c | `convInverse_convInverse` (stretch) | 10 min |
| 2 | Verify + commit | 15 min |
| 4 | Cycle 083 scoping (stretch) | 5 min |
| **Total** | | **~80 min** |

This is a **deliberately small cycle** following two large cycles
(080: associativity; 081: inverse existence). Use the slack to
confirm the convolution-decision documentation is solid and to
scope cycle 083 candidates honestly. Do not overreach into thm:382A
or §381G/H — they are real multi-cycle infrastructure and rushing
them now will produce another half-finished scaffold.
