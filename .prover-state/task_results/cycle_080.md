# Cycle 080 Results

## Worked on
`lem:383B` — associativity of the convolution product on forest
mappings (Butcher §383, p. 309): `(αβ)γ = α(βγ)`. New theorem
`OpenMath.Chapter3.Section383.convProduct_assoc` plus three private
helpers (`double_powerset_swap`, `convProduct_assoc_lhs_eq`,
`convProduct_assoc_rhs_eq`) at `OpenMath/Chapter3/Section383.lean:230-352`.

## Approach
Followed the cycle 080 strategy (Aristotle-first, scaffold-checkpoint):

1. **Scaffold-first checkpoint commit** with four sorries
   (`double_powerset_swap`, two LHS/RHS expansion lemmas,
   `convProduct_assoc`).
2. **Submitted all four to Aristotle in batch** with self-contained
   `import Mathlib` files (and an axiom-mocked variant for the main
   theorem so Aristotle didn't have to rediscover the decomposition).
3. **While Aristotle was running** (it stayed at 2-5% the whole time —
   evidently slow start), I probed the LHS/RHS expansions with
   `mcp__lean-lsp__lean_multi_attempt`. Both landed in one shot
   using `unfold convProduct; rw [Multiset.sum_bind]; refine
   congrArg Multiset.sum (Multiset.map_congr rfl ...); rw
   [← Multiset.sum_map_mul_right/left]; ring`. Wrote them in.
4. **Manual induction proof of `double_powerset_swap`**. The textbook
   bijection `(Q, T) ↔ (Q + T, Q)` becomes induction on `S`, with the
   `cons a s` step split into 4 pieces (LHS = A + B, RHS = C + D)
   via `Multiset.powerset_cons` + `Multiset.add_bind` +
   `Multiset.bind_map`. After splitting:
   - A further factors as `A1 + Z` (via `Multiset.cons_sub_of_le`
     + `Multiset.powerset_cons` under `Multiset.bind_congr`).
   - B simplifies to LHS-form of IH applied to `f' Q T := f (a::Q) T`
     (via `hcons_sub : a ::ₘ m - a ::ₘ n = m - n`).
   - D factors as `W + V` (similarly to A).
   - The IH applied thrice (to `f`, to `fun Q T => f Q (a ::ₘ T)`,
     and to `fun Q T => f (a ::ₘ Q) T`) makes A1 = C, Z = W, B = V.
   - `ring` closes A + B = C + W + V = C + D.
5. **`convProduct_assoc`** then went in cleanly:
   `funext S; rw [LHS_eq, RHS_eq, double_powerset_swap S _]`, then
   pointwise `α (S - Q - (R - Q)) = α (S - R)` via
   `Multiset.sub_add_eq_sub_sub` + `add_comm` +
   `Multiset.sub_add_cancel` (for `Q ≤ R`).
6. Cancelled the four queued/in-progress Aristotle jobs; manual proof
   was already in place and verified.

## Result
**SUCCESS**. `OpenMath/Chapter3/Section383.lean` builds clean
(no warnings, no sorries, ~2.7s build time).

`#print axioms OpenMath.Chapter3.Section383.convProduct_assoc`
returns `[propext, Classical.choice, Quot.sound]` — only the
expected baseline axioms (`Classical.choice` is forced by the
file's `noncomputable instance : DecidableEq RootedTree`
workaround at line 65, established in cycle 078).

Updated:
- `extraction/formalization_data/lean_status.json` — `lem:383B`
  now `formalized` with full notes.
- `plan.md` — `lem:383B` row marked `[x]`; progress 51 → 52 / 175.

## Faithfulness check

For `OpenMath.Chapter3.Section383.convProduct_assoc`:

- Entity ID: `lem:383B`. Textbook statement (from
  `extraction/formalization_data/entities/lem_383B.json`):
  > Let α, β and γ be multiplicative mappings from forests to reals.
  > Then (αβ)γ = α(βγ).
- Lean statement: `convProduct (convProduct α β) γ = convProduct α
  (convProduct β γ)` for `α β γ : Forest → ℝ` (no
  `IsMultiplicative` hypotheses).
- Lean statement captures: **weaker hypotheses** — drops
  multiplicativity of α, β, γ. This is a *faithful generalisation*,
  not a strengthening: Butcher's proof (per `proof_latex` in the
  JSON) uses only the algebraic identity `(αβ)(S) = Σ_{R ⊑ S}
  α(S\R)β(R)` (the convolution definition), never invokes
  `α(s+t) = α(s)·α(t)` or `α(0) = 1`. Documented in the docstring.
- Tautology check: conclusion `convProduct (convProduct α β) γ
  = convProduct α (convProduct β γ)` does not appear as a
  hypothesis. ✓
- Identity check: proof is not `exact h` / `id`; it does real work
  (LHS and RHS unfold to genuinely different `Multiset.bind` double
  sums; the bijection is required). ✓
- Definition smuggling check: no new `structure`/`class`. The three
  helpers are `theorem`s, not definitions. ✓
- Hypothesis strength check: hypotheses are *weaker* than the
  textbook (multiplicativity dropped). Justification per docstring
  and noted above. ✓
- Absent theorem check: `double_powerset_swap`,
  `convProduct_assoc_lhs_eq`, `convProduct_assoc_rhs_eq` all exist
  and are proved (no sorry). ✓

The three private helpers are not Butcher entities — they are
internal infrastructure. `double_powerset_swap` is a generic
Multiset library lemma (could be upstreamed to Mathlib).

## Dead ends

- **First Z-definition mismatch.** Initial induction proof set
  `Z := (s.powerset.bind fun R => R.powerset.map fun Q => f Q
  (a ::ₘ (R - Q))).sum` (the RHS-style form) and tried to merge it
  with A's first half via `Multiset.bind_add`. This failed because
  `bind_add` requires both binds to range over the same multiset
  with the same body shape, but A's first half has inner powerset
  `(s - Q).powerset` while my Z had inner powerset `R.powerset` —
  Lean unified the binders to `Q` and the inner became `Q.powerset`,
  giving an absurd goal. Fix: redefine Z in **LHS form** (over
  `(s - Q).powerset`), apply IH explicitly to convert to RHS form
  later. This is the "always-rewrite-LHS-to-LHS-then-use-IH" pattern
  rather than mixing forms.

- **Aristotle slow start.** Submitted at 03:05 UTC; 14 minutes
  later all four jobs were still at 2-5% complete. Rather than wait
  the full 30 min and risk the cycle running past 3-hour budget,
  switched to manual proofs (which `lean_multi_attempt` revealed
  were one-liners for the easy two and a 60-line induction for the
  bijection). Cancelled jobs at 03:20 UTC.

- **`lean_multi_attempt` quirk.** When the snippet ends with `sorry`,
  `goals: []` and zero diagnostics — the sorry hides whether the
  preceding tactics actually closed sub-goals. Workaround: re-run
  the same probe without the trailing `sorry` to see the real goal
  state and any errors. Useful pattern: probe with-sorry first to
  confirm the snippet PARSES, then probe without-sorry to read the
  remaining goal.

## Discovery

- **The convolution-product associativity proof is hypothesis-free.**
  The textbook prefaces with "Let α, β, γ be multiplicative", but
  the proof doesn't use this. Documented as a faithful
  generalisation in the Lean theorem's docstring and in the
  task-results faithfulness check. This is genuinely useful for
  cycle 081 (`lem:383C` left/right inverses) — the monoid structure
  on `Forest → ℝ` exists at the type level, not gated by
  multiplicativity, which keeps the inverse construction clean.

- **`Multiset.bind_congr` + `Multiset.map_congr` are the right
  hammer for under-binder rewrites.** Both take a function
  `∀ x ∈ s, ...` letting you assume membership; that's how I got
  `Q ≤ s` (via `Multiset.mem_powerset.mp hQ`) inside the bind to
  apply `Multiset.cons_sub_of_le`. This pattern recurs in any
  `S.powerset.bind`-style proof.

- **`Multiset.cons_sub_of_le` (for `Q ≤ s ⇒ a ::ₘ s - Q = a ::ₘ
  (s - Q)`) does exist in Mathlib** — at
  `Mathlib/Data/Multiset/AddSub.lean:347`. But the symmetric
  cancellation `a ::ₘ s - a ::ₘ Q = s - Q` does NOT have a named
  Mathlib lemma; trivial to derive via `ext y; simp only
  [Multiset.count_sub, Multiset.count_cons]; omega`. Could be
  upstreamed.

- **`Multiset.sum_bind` exists** (auto-generated from
  `Multiset.prod_bind` via `@[to_additive]` at
  `Mathlib/Data/Multiset/Bind.lean:218`). It is `(s.bind t).sum
  = (s.map fun a => (t a).sum).sum`, which converts a flat-bind sum
  to a sum-of-sums. Useful in both directions for the LHS/RHS
  expansion lemmas.

## Suggested next approach

`lem:383C` (existence of left and right inverses for the convolution
product on `G₁`, the multiplicative forest mappings with α(∅)=1) is
the natural cycle 081 target. It depends on `lem:383B` (now closed)
plus the multiplicativity hypothesis. Approach: define the inverse
recursively over the forest's order/cardinality, with the recursion
guarded by `α(∅) = 1` (so the leading `(α·α⁻¹)(∅) = α(∅)·α⁻¹(∅)
= α⁻¹(∅) = 1` works out). The recursion is well-founded on
`Multiset.card`. Then `lem:383D` (the closure of the convolution
product's inverse under multiplicativity) and `thm:386A` (the
Runge-Kutta group as a topological group) become reachable.

Aristotle observation (for the planner): jobs in this batch took
> 14 minutes to reach even 5% complete and were cancelled. If
Aristotle is consistently slow to start, consider adjusting the
"submit and sleep 30 min" cadence in CLAUDE.md to "submit and
proceed manually in parallel; integrate Aristotle if/when it
delivers". Cycle 080 finished in ~30 min wall-clock by going
manual; the 30-min sleep would have been pure waste.
