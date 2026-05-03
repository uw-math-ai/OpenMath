# Cycle 081 Results

## Worked on

`lem:383C` — Existence of left and right inverses in G₁ (multiplicative
forest mappings).

Appended to `OpenMath/Chapter3/Section383.lean`:

* `convOne : Forest → ℝ` — convolution-product identity element.
* `convInverse : (Forest → ℝ) → Forest → ℝ` — closed-form inverse.
* `isMultiplicative_convOne` — non-vacuity / supporting infra.
* `convInverse_isMultiplicative` — closed form is multiplicative.
* `convProduct_singleton_eq_zero` — `(α · convInverse α)({t}) = 0`.
* `convProduct_singleton_symm_eq_zero` — symmetric singleton zero.
* `convProduct_convInverse` — right-inverse property.
* `convProduct_convInverse_symm` — left-inverse property.
* `exists_inverse_of_isMultiplicative` — **lem:383C**, the existential.

## Approach

Followed the planner's strategy for cycle 081 verbatim. Closed-form
inverse `convInverse α F = (-1)^|F| · ∏_{t ∈ F} α({t})`, then:

1. Verified `convInverse α` is multiplicative by direct computation
   (`Multiset.card_add` + `prod_add` + `pow_add` + ring).
2. Computed per-singleton zero via `Multiset.powerset_cons` +
   `powerset_zero` to expose the only two summands.
3. For the inverse property, used `Multiset.induction` on the forest
   `F`. Empty case: direct from `α(0) · β(0) = 1`. Cons case:
   factor `t ::ₘ rest = (t ::ₘ 0) + rest`, apply
   `multiplicative_conv` (Lemma 383A) to split, kill the
   `(t ::ₘ 0)` factor by per-singleton zero, then `simp` finishes
   the `if F = 0 then 1 else 0` branch using `cons` ≠ `0`.

Manual proof was short enough that I skipped the Aristotle batch
(per cycle 080's discovery: "do not waste compute on Aristotle when
manual proofs are faster"). Per the strategy's explicit guidance:

> Expect Aristotle to be irrelevant (manual proofs are short and
> well-targeted); use it only as a backup.

## Result

**SUCCESS** — `lem:383C` closed.

* `lake env lean OpenMath/Chapter3/Section383.lean` — clean (no
  errors, no warnings).
* `lake build OpenMath.Chapter3.Section383` — clean (1933 jobs,
  3.1s).
* All five new theorems verified via `#print axioms`: depend only
  on the baseline `[propext, Classical.choice, Quot.sound]`. No new
  axioms introduced.
* No `sorry`s anywhere in the file.

Sorry count: still 0 across `OpenMath/`.

## Faithfulness check

**For `convOne`** (helper, not a textbook-named entity):

* No textbook entity ID — supporting definition for the
  `(α · α⁻¹) = 1` formulation. Captures the unit element of the
  Butcher group.
* Lean type `Forest → ℝ` matches the natural type of "1 ∈ G₁".

**For `convInverse`** (closed-form witness for the existential):

* No textbook entity ID — chosen as the explicit constructive
  witness for `lem:383C`. The textbook (page 310) uses an inductive
  recurrence; we use a closed form because our forest-encoded
  convolution does not have a φ-term on single-tree forests (see
  caveat below).
* Documented in the docstring with the explicit formula and the
  reason it differs from Butcher's β.

**For `exists_inverse_of_isMultiplicative`** (= `lem:383C`):

* Entity `lem:383C` — textbook (quoted from
  `extraction/formalization_data/entities/lem_383C.json`):

  > Given α ∈ G₁, there exist a left inverse and a right inverse.

* Lean statement captures: **same content** at the existential
  level — the inverse exists. Strictly stronger in providing an
  explicit constructive witness rather than an opaque ∃.
* Hypothesis: only `IsMultiplicative α` (= G₁ membership). ✓
* Tautology check: conclusion `convProduct α β = convOne` does not
  appear as a hypothesis. ✓
* Identity check: proof is
  `⟨convInverse α, convInverse_isMultiplicative α, …, …⟩` —
  constructive, not a vacuous re-export. ✓
* Definition smuggling check on `convInverse`: closed-form formula,
  not a re-statement of "inverse property". ✓

**FAITHFULNESS CAVEAT (escalated, not deferred)**: the underlying
`convProduct` (defined cycle 077–078) uses *multiset sub-selection*
where Butcher's textbook uses *vertex-subset partition*. This means
our convolution is strictly weaker than Butcher's, and the
inverse-existence theorem holds in our (multiset-graded) algebra
but is not literally Butcher's group's inverse-existence claim.

The closed-form `convInverse α F = (-1)^|F| · ∏ α({t})` is the
correct inverse for *our* convolution; Butcher's α⁻¹ would involve
a sum over vertex-subset partitions (Lemma 383D).

Documented in `Section383.lean` (docstring of
`exists_inverse_of_isMultiplicative`) and escalated as
`.prover-state/issues/convolution_vertex_vs_multiset.md` for the
planner to decide whether to refactor `convProduct` before tackling
`lem:383D`.

## Dead ends

None. Followed the strategy literally; everything worked first
attempt after fixing two name-typo errors (`Multiset.le_zero` not
`eq_zero_of_le_zero`; `Multiset.notMem_zero` not `not_mem_zero`).

The `simp [hne]` calls at the end of the inductive cases initially
included `hne` and `← hcons` as redundant arguments — `simp` was
already closing those goals via the `t ::ₘ 0 + rest` ≠ `0` simp
machinery. Cleaned up to bare `simp` per the unused-arg linter.

## Discovery

1. **`(t ::ₘ 0 : Multiset _) + rest = t ::ₘ rest`** holds by
   `rfl` — useful for converting between the cons-form and the
   addition-form of multisets.

2. **`simp` knows `(a ::ₘ s) ≠ 0`** without needing explicit hints
   — it has the cons-non-zero simp lemma in its default set.

3. **The textbook's convolution and ours diverge structurally** at
   single trees of order > 1. The textbook's R ⊑ S means
   "vertex-subset of S" (page 287); ours means "multiset
   sub-selection". This was implicit in cycle 077–078's
   definition; cycle 081 makes it explicit and escalates.

4. **Closed-form inverses are short proofs**; the textbook's
   recursive induction is heavier infrastructure. For our
   multiset-encoded algebra, the closed form is the right choice
   — short, explicit, computable (modulo the noncomputable `α`).

5. **Skipping Aristotle when proofs are short** — confirmed cycle
   080's hypothesis. Manual proof of all five new theorems took
   ~30 minutes wall-clock; an Aristotle round-trip would have been
   slower with no expected uplift.

## Suggested next approach

For the planner:

1. **Decide on convolution refactoring before `lem:383D`.** The
   partition-sum formula in 383D *requires* the vertex-subset
   convolution to make sense. Three options laid out in
   `.prover-state/issues/convolution_vertex_vs_multiset.md`:

   (a) Refactor `convProduct` to use vertex subsets — invalidates
       cycle 077–081's algebra but unlocks faithful 383D.
   (b) Document the divergence prominently and skip 383D.
   (c) Hybrid — keep both convolutions, prove 383D for the
       textbook one separately.

   My recommendation: option (a) is the cleanest long-term, but
   it's a multi-cycle refactor. If the planner wants to keep
   §383's momentum, option (b) for now.

2. **In the meantime**, pick a different §383 sub-target that
   doesn't depend on the partition picture. Candidates from the
   plan order:
   * `thm:386A` (Runge–Kutta group structure) — depends on 383C ✓
     and 383D ✗ (needs partition convolution).
   * Smaller helper lemmas around `convOne` /
     `IsMultiplicative` — e.g. uniqueness of the inverse (now
     follows from associativity + identity + existence, all
     proved).

3. **Stretch helper opportunity**: prove `inverse_unique` —
   for any α ∈ G₁, the left and right inverses are equal. The
   textbook gives the standard argument
   `αₗ⁻¹ = αₗ⁻¹(α αᵣ⁻¹) = (αₗ⁻¹ α)αᵣ⁻¹ = αᵣ⁻¹` — three rewrites
   using associativity (383B), identity (convOne), and the inverse
   properties just proved. ~5–8 lines. Useful infrastructure for
   `thm:386A`.
