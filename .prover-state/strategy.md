# Strategy — Cycle 081

## Status snapshot

- **Last cycle**: 080 closed `lem:383B` (associativity of convolution
  product) at `OpenMath/Chapter3/Section383.lean:340`. Score +2,
  build clean, axioms baseline only. Progress 51 → **52 / 175**.
- **Sorry count**: 0 across all of `OpenMath/`.
- **Aristotle**: no pending jobs.
- **Open issues**: nothing blocking — all open issues are documented
  deferrals (AN-stability, reduced-method construction, Picard
  strengthening, etc.) that do NOT block §383 work.

## Priority 0 — none

No Aristotle results to incorporate, no infrastructure blockers, no
sorries to clean up. Cycle 080's deliverable was the cleanest in
recent history. Proceed directly to the next entity.

## Priority 1 — `lem:383C` (existence of left and right inverses)

### Target

`OpenMath/Chapter3/Section383.lean` — append a new theorem
`exists_inverse_in_G1` (or paired left/right), plus the supporting
closed-form construction `convInverse`.

**Textbook statement** (`extraction/formalization_data/entities/lem_383C.json`):

> Given α ∈ G₁, there exist a left inverse and a right inverse.

Where G₁ = multiplicative forest mappings with `α(∅) = 1` (= our
`IsMultiplicative` predicate, which already requires `α 0 = 1`).

**Textbook proof** (Butcher §383, p. 310):

> By induction on the order of `t`. For singleton τ:
> `(αβ)(τ) = (βα)(τ) = α(τ) + β(τ)`, set `β(τ) := −α(τ)`.
>
> For higher-order `t`: `(αβ)(t) = α(t) + β(t) + φ(t, α, β)`, where
> `φ(t, α, β)` involves only values of α and β at trees of order
> < ord(t). So `β(t) := −α(t) − φ(t, α, β)` makes `(αβ)(t) = 0`.

### Critical observation: our forest encoding makes this much simpler

In our `convProduct` (defined on **forests** = `Multiset RootedTree`,
with multiset subtraction), the convolution on a *single-tree forest*
`{t} = (t ::ₘ 0)` collapses:

```
(αβ)({t}) = Σ_{R ≤ {t}} α({t} - R) β(R)
          = α({t}) β(∅) + α(∅) β({t})         -- powerset of {t} = {∅, {t}}
          = α({t}) + β({t})                    -- using α(∅)=β(∅)=1
```

There is **no φ term** at the forest level for single-tree forests —
the textbook's φ comes from tree-level partitions (decomposing a tree
along its edges into a forest), but our convolution operates over
forest sub-multisets, which for a singleton-tree forest are just ∅
and {t} itself.

So `β({t}) := -α({t})` directly works, and we extend β
multiplicatively to multi-tree forests via the closed form

```
β(F) := (-1)^|F| · ∏_{t ∈ F} α({t})
```

By multiplicativity (Lemma 383A) of `αβ`, once `(αβ)({t}) = 0` for
every single-tree forest, `(αβ)(F) = 0` for every non-empty forest
(it factors as a product containing at least one zero).

### Step-by-step plan

#### Step A — Sorry-first scaffold + checkpoint commit

Write the full structure with `sorry` at every closure point. Verify
it compiles with `lake env lean OpenMath/Chapter3/Section383.lean`.
Then commit as
"Cycle 081 [scaffold] — sorry-first scaffold for lem:383C".

The scaffold should include:

```lean
/-- The convolution-product identity element on G₁: 1 on the empty
forest, 0 elsewhere. (Used to state the inverse property succinctly.) -/
noncomputable def convOne : Forest → ℝ :=
  fun F => if F = 0 then 1 else 0

/-- Closed-form inverse: β(F) = (-1)^|F| · ∏_{t ∈ F} α({t}). -/
noncomputable def convInverse (α : Forest → ℝ) : Forest → ℝ :=
  fun F => (-1)^(Multiset.card F) *
    (F.map (fun t => α ({t} : Multiset RootedTree))).prod

/-- `convInverse α` is multiplicative whenever the formula structure
permits (which is always — multiplicativity of α is not required to
make convInverse itself multiplicative). -/
theorem convInverse_isMultiplicative (α : Forest → ℝ) :
    IsMultiplicative (convInverse α) := by sorry

/-- Per-tree zero: `(αβ)({t}) = 0` where β = convInverse α. -/
theorem convProduct_singleton_eq_zero
    {α : Forest → ℝ} (hα : IsMultiplicative α) (t : RootedTree) :
    convProduct α (convInverse α) ({t} : Multiset RootedTree) = 0 := by sorry

/-- Inverse property: `convProduct α (convInverse α) = convOne`. -/
theorem convProduct_convInverse
    {α : Forest → ℝ} (hα : IsMultiplicative α) :
    convProduct α (convInverse α) = convOne := by sorry

/-- Symmetric: `convProduct (convInverse α) α = convOne`. -/
theorem convProduct_convInverse_symm
    {α : Forest → ℝ} (hα : IsMultiplicative α) :
    convProduct (convInverse α) α = convOne := by sorry

/-- **Butcher §383 Lemma 383C** — existence of left and right
inverses for any α ∈ G₁. -/
theorem exists_inverse_of_isMultiplicative
    {α : Forest → ℝ} (hα : IsMultiplicative α) :
    ∃ β : Forest → ℝ, IsMultiplicative β ∧
      convProduct α β = convOne ∧ convProduct β α = convOne :=
  ⟨convInverse α, convInverse_isMultiplicative α,
   convProduct_convInverse hα, convProduct_convInverse_symm hα⟩
```

#### Step B — Aristotle batch (parallel mode, do NOT sleep)

**Cycle 080 discovery (memorialise this)**: Aristotle was at 2-5%
after 14 minutes on the lem:383B batch. The "sleep 30 min then
check" rule wasted compute when manual proofs landed faster. **For
cycle 081**: submit the batch, then *immediately* work on the manual
proof in parallel. Check Aristotle at the **end** of the cycle, not
mid-cycle.

Submit the following targets to Aristotle (self-contained `Mathlib`
files, axiom-mock the dependencies on `convProduct`,
`IsMultiplicative`, `Forest`):

1. `convInverse_isMultiplicative` — pure algebra over Multiset.
2. `convProduct_singleton_eq_zero` — direct unfolding.
3. (Optional) `convProduct_convInverse` — full inverse property.

Do NOT submit the top-level `exists_inverse_of_isMultiplicative` to
Aristotle — it composes the sub-lemmas trivially.

#### Step C — Manual proofs

##### `convInverse_isMultiplicative` (~15 lines)

```lean
refine ⟨?_, ?_⟩
· -- convInverse α 0 = 1
  unfold convInverse
  simp [Multiset.card_zero, pow_zero, Multiset.map_zero, Multiset.prod_zero]
· -- convInverse α (s + t) = convInverse α s * convInverse α t
  intro s t
  unfold convInverse
  rw [Multiset.card_add, Multiset.map_add, Multiset.prod_add, pow_add]
  ring
```

##### `convProduct_singleton_eq_zero` (~10 lines)

```lean
unfold convProduct
have hpow : (Multiset.card ({t} : Multiset RootedTree) : ℕ) = 1 := by
  simp [Multiset.card_singleton]
-- {t}.powerset = {∅, {t}}; expand the sum directly.
simp only [show ({t} : Multiset RootedTree) = t ::ₘ 0 from rfl,
           Multiset.powerset_cons, Multiset.powerset_zero,
           Multiset.map_singleton, Multiset.map_cons, Multiset.sum_cons,
           Multiset.sum_singleton, Multiset.map_zero, Multiset.sum_zero]
-- Goal reduces to: α({t}) * β(0) + α(0) * β({t}) = 0
-- where β = convInverse α.
unfold convInverse
simp [hα.1, Multiset.card_zero, Multiset.card_singleton, pow_zero, pow_one,
      Multiset.map_zero, Multiset.prod_zero, Multiset.map_singleton,
      Multiset.prod_singleton]
ring
```

(Worker: the exact set of `simp` lemmas to thread through may need
adjustment; use `lean_multi_attempt` to probe the unfolding shape.)

##### `convProduct_convInverse` (~25 lines)

Use `Multiset.induction` on F:

```lean
funext F
unfold convOne
induction F using Multiset.induction with
| empty =>
  -- (αβ)(0) = α(0) * β(0) = 1.
  simp only [if_pos rfl]
  show ((Multiset.powerset 0).map _).sum = 1
  simp [Multiset.powerset_zero, hα.1, convInverse_isMultiplicative α |>.1]
| cons t rest IH =>
  -- (αβ)(t ::ₘ rest) = (αβ)({t} + rest) = (αβ)({t}) * (αβ)(rest)  [by 383A]
  --                  = 0 * (...) = 0.
  rw [show t ::ₘ rest = ({t} : Multiset RootedTree) + rest from rfl]
  -- Apply Lemma 383A multiplicativity.
  have hαβ : IsMultiplicative (convProduct α (convInverse α)) :=
    multiplicative_conv hα (convInverse_isMultiplicative α)
  rw [hαβ.2 ({t}) rest]
  rw [convProduct_singleton_eq_zero hα t]
  simp
```

The `if F = 0 then 1 else 0` branch when `F = t ::ₘ rest`: since
`t ::ₘ rest ≠ 0` (a non-empty multiset), `if_neg` collapses to 0 on
the RHS; the LHS is `0 * (αβ)(rest) = 0`. Match cleanly.

##### `convProduct_convInverse_symm` (~25 lines)

Same shape — by Lemma 383A multiplicativity of `(convInverse α) * α`,
plus the symmetric per-singleton zero
`convProduct (convInverse α) α {t} = β({t}) + α({t}) = -α({t}) + α({t}) = 0`.

The structure is identical; just swap the order of arguments. May
factor a shared helper `convProduct_singleton_alpha_beta` if it
saves lines, but a copy-paste is fine.

### Mathlib lemmas (verify with `lean_local_search` before use)

| Goal | Lemma |
|---|---|
| `Multiset.card (s + t) = Multiset.card s + Multiset.card t` | `Multiset.card_add` |
| `(s + t).map f = s.map f + t.map f` | `Multiset.map_add` |
| `(s + t).prod = s.prod * t.prod` | `Multiset.prod_add` |
| `(-1 : ℝ)^(a + b) = (-1)^a * (-1)^b` | `pow_add` |
| `Multiset.card 0 = 0` | `Multiset.card_zero` |
| `Multiset.card {x} = 1` | `Multiset.card_singleton` |
| `(0 : Multiset α).map f = 0` | `Multiset.map_zero` |
| `(0 : Multiset ℝ).prod = 1` | `Multiset.prod_zero` |
| `(t ::ₘ 0).powerset = ...` | `Multiset.powerset_cons` + `Multiset.powerset_zero` |
| Singleton-multiset map | `Multiset.map_singleton` |
| Singleton-multiset prod | `Multiset.prod_singleton` |

### Faithfulness check

For `convInverse` and the inverse-existence theorem:

- Entity: `lem:383C`. Textbook: "Given α ∈ G₁, there exist a left
  inverse and a right inverse."
- Lean: `convInverse α` is exhibited as both a left and right
  inverse (the per-singleton zero identity is symmetric in α and β).
- The Lean statement is **strictly stronger** than the textbook in
  one sense: we provide an explicit closed-form formula, not just
  an existential. This is a faithful constructive refinement, not a
  restriction.
- Hypothesis check: only `IsMultiplicative α` (= G₁ membership). ✓
- Tautology check: conclusion `convProduct α β = convOne` does not
  appear as a hypothesis. ✓
- Identity check: the proof of `exists_inverse_of_isMultiplicative`
  is `⟨convInverse α, ..., ..., ...⟩` — *constructive*, not a
  vacuous re-export of a hypothesis. ✓
- Definition smuggling check: `convInverse` is a genuine new
  definition with a closed-form formula. It IS the textbook's β,
  computed in closed form. ✓
- Notable divergence from textbook PROOF (not statement): the
  textbook does induction on tree order to construct β; we use a
  closed form because our forest-level convolution makes the φ term
  vanish on single-tree forests. **Document this in the docstring**
  of `convInverse` so future readers understand why the textbook's
  inductive structure is unnecessary in our encoding.

### What NOT to try

1. **Do NOT do induction on `RootedTree.order`** to define β. The
   textbook does this because its convolution operates on tree
   partitions; in our forest encoding, single-tree forests have only
   the trivial sub-multisets {∅, {t}}, so the recursion collapses to
   a closed form. Doing induction would massively over-complicate
   the proof.

2. **Do NOT define β via well-founded recursion on `Multiset.card`**
   of forests. The closed form `(-1)^|F| · ∏ α({t})` works directly.

3. **Do NOT submit the top-level existence theorem to Aristotle** as
   a single job. It depends on `multiplicative_conv` (Lemma 383A)
   and the closed-form `convInverse`, which Aristotle would have to
   discover. Submit only the *sub-lemmas*; compose manually.

4. **Do NOT introduce a class or structure for the Runge–Kutta
   group**. That would be `thm:386A` territory (and possibly
   premature even there). Keep `convOne`, `convInverse`, etc. as
   plain `def`s. The Runge–Kutta-group abstraction is a future-cycle
   concern.

5. **Do NOT mix LHS-form and RHS-form intermediate lemmas** (per
   cycle 080 dead-end §1). Always rewrite LHS-to-LHS or RHS-to-RHS
   before invoking IH or comparison lemmas.

6. **Do NOT wait 30 minutes for Aristotle**. Per cycle 080's
   discovery: submit, then immediately work in parallel. Check
   Aristotle at end of cycle. If a useful proof is returned, swap
   it in opportunistically. Otherwise cancel the jobs.

7. **Do NOT increase `maxHeartbeats`**. Decompose if a single proof
   is slow (likely the multi-forest induction step in the inverse
   property — split off helper lemmas for the base case and
   inductive step if needed).

8. **Do NOT define `convOne` if a Mathlib equivalent exists**. Run
   `lean_local_search "Pi.single"` and `lean_local_search "single
   indicator"` first — there may be a Mathlib indicator function
   that fits. If nothing matches, the local `def` is fine.

### Stretch goal — only if main target lands cleanly by mid-cycle

If `lem:383C` is closed by ~half-cycle, attempt **either**:

(a) **`lem:383D`** (a more explicit formula for the inverse). The
    textbook gives a partition-sum formula
    `α⁻¹(t) = Σ_{P ∈ P(t)} (-1)^{#P} ∏ α(tᵢ)`. Our `convInverse`
    already encodes a closed-form on FORESTS, so `lem:383D` may
    require relating our forest-level inverse to a tree-partition
    formula via the multiplicative extension — likely a multi-cycle
    job once partition machinery is needed. **Probably skip.**

(b) **A small follow-up cleanup**: prove
    `IsMultiplicative convOne` (it is: `convOne (s + t) = convOne s
    · convOne t` since both sides are 1 iff both s = 0 and t = 0).
    Useful for the future Runge–Kutta-group material.

**Do NOT pursue the stretch goal unless the main target is
unambiguously closed by mid-cycle.**

### Workflow checklist (worker)

1. [ ] Read `extraction/formalization_data/entities/lem_383C.json`
   (just to confirm the textbook statement firsthand).
2. [ ] Sketch the Lean signatures in this strategy as a draft block
   in `Section383.lean`.
3. [ ] Sorry-first scaffold; build with
   `lake env lean OpenMath/Chapter3/Section383.lean`; commit as
   "Cycle 081 [scaffold] — sorry-first scaffold for lem:383C".
4. [ ] Submit Aristotle batch (sub-lemmas 1–2, optionally 3); do
   NOT sleep.
5. [ ] Manually prove `convInverse_isMultiplicative`.
6. [ ] Manually prove `convProduct_singleton_eq_zero`.
7. [ ] Manually prove `convProduct_convInverse` (and the symmetric
   variant).
8. [ ] Package the existence theorem.
9. [ ] Build clean. Verify axioms via `#print axioms` (expect
   `[propext, Classical.choice, Quot.sound]`).
10. [ ] Update `extraction/formalization_data/lean_status.json` —
    mark `lem:383C` as `formalized` with file/symbol pointers.
11. [ ] Update `plan.md` — `lem:383C` row `[ ]` → `[x]`, increment
    progress 52 → **53 / 175**.
12. [ ] Check Aristotle status; if useful proofs returned, decide
    whether to swap in (only if cleaner than manual). Cancel
    remaining jobs.
13. [ ] Write `.prover-state/task_results/cycle_081.md` (use the
    template in `CLAUDE.md`).
14. [ ] Final commit:
    "Cycle 081 — close lem:383C; existence of convolution inverse in G₁".

### Time budget

Estimated 1.5–2 hours wall-clock for a clean close. The closed-form
encoding makes this much simpler than the textbook's induction.
Expect Aristotle to be irrelevant (manual proofs are short and
well-targeted); use it only as a backup. **Do not spend more than
30 min on any single sub-lemma without decomposing further.**
