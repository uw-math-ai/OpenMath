# Cycle 079 Strategy

## State summary

* **Cycle 078 closed** `lem:383A` (Butcher §383, convolution of
  multiplicative forest mappings) in
  `OpenMath/Chapter3/Section383.lean` (commit `27256e9`).
  Score = +2. Progress: 50/175.
* `Section383.lean` exposes a clean infrastructure layer that is
  **directly load-bearing for `lem:383B`**:
  - `_PowersetAdd.powerset_add : (s + t).powerset = (s.powerset ×ˢ t.powerset).map (fun p => p.1 + p.2)`
  - `_PowersetAdd.sum_mul_sum_eq_sum_product`
  - `Forest := Multiset RootedTree`
  - `IsMultiplicative` predicate (`α 0 = 1 ∧ ∀ s t, α (s+t) = α s * α t`)
  - `convProduct α β S = (S.powerset.map (fun R => α (S - R) * β R)).sum`
  - `multiplicative_conv : IsMultiplicative α → IsMultiplicative β → IsMultiplicative (convProduct α β)`
* **Aristotle project `18504be5-2481-4d60-9d7b-12b8a5cd2b47`** (cycle
  077 §410D submission of 5 sub-lemmas including the reverse-direction
  substitution and `subst log expPS = 1 + X`) was at 13% at start of
  cycle 078; cycle 078 did **not** poll. Per CLAUDE.md it is now safe
  to check **once** at the start of cycle 079.

## Priority 0 — One-shot Aristotle status check

**At the start of the cycle, run exactly one
`mcp__aristotle__get_status` call** on project
`18504be5-2481-4d60-9d7b-12b8a5cd2b47`.

* If `status` is `COMPLETED` and any of the §410D sub-lemmas have
  returned proofs (especially the reverse-direction
  `coeff_eq_zero_of_coeff_subst_eq_zero` or the load-bearing
  `subst_logOnePlusPS_expNegPS` chain — see
  `.prover-state/issues/thm_410D_substitution.md` for the exact
  identifiers), **switch to Path A below (incorporate §410D)**.
* Otherwise (still `IN_PROGRESS`, `FAILED`, or only weak/non-bridging
  proofs returned), **proceed with Path B (`lem:383B`)**. Do **NOT**
  poll Aristotle a second time during this cycle.

## Path A — incorporate §410D Aristotle results (only if Priority 0 returned proofs)

If Aristotle solved the reverse-direction substitution lemma:

1. Open `OpenMath/Chapter4/Section410.lean` at the two sorry sites
   (lines ~949 and ~969 — `coeff_eq_zero_of_coeff_subst_eq_zero` and
   `subst_logOnePlusPS_expNegPS`).
2. Copy in the returned proof. Verify it compiles with
   `lake env lean OpenMath/Chapter4/Section410.lean`.
3. Run `#print axioms OpenMath.Chapter4.Section410.thm_410D` and
   confirm `[propext, Classical.choice, Quot.sound]` only.
4. Build the entire chapter via
   `lake build OpenMath.Chapter4.Section410` to refresh the .olean
   cache (otherwise `#print axioms` may report stale `sorryAx` per
   the cycle 072 cache lesson).
5. Update `extraction/formalization_data/lean_status.json::thm:410D`
   from `partial` (or `unformalized`) to `formalized` with file
   pointer `OpenMath/Chapter4/Section410.lean`.
6. Mark `thm:410D` as `[x]` in `plan.md` and bump the progress
   counter.
7. Run the pre-commit faithfulness checklist; commit.

Skip Path B in this case.

## Path B — `lem:383B` (default if Priority 0 did not unblock §410D)

**Target**: `lem:383B` — *Associativity of multiplicative forest
mappings* (Butcher §383, page 309). Read
`extraction/formalization_data/entities/lem_383B.json` first.

### Textbook statement (verbatim)

> Let α, β and γ be multiplicative mappings from forests to reals.
> Then `(αβ)γ = α(βγ).`

### Lean target

In `OpenMath/Chapter3/Section383.lean` (extending the existing
namespace `OpenMath.Chapter3.Section383`):

```lean
/-- **Butcher §383 Lemma 383B** — convolution of multiplicative
forest mappings is associative. -/
theorem convProduct_assoc {α β γ : Forest → ℝ}
    (hα : IsMultiplicative α) (hβ : IsMultiplicative β) (hγ : IsMultiplicative γ) :
    convProduct (convProduct α β) γ = convProduct α (convProduct β γ) := by
  sorry
```

Note: associativity in the textbook is stated **pointwise**
((αβ)γ)(S) = (α(βγ))(S) for all `S`. Use `funext S` first.

The two `IsMultiplicative` hypotheses are not strictly needed for
the pointwise reindexing identity — convolution is associative on
**all** functions `Forest → ℝ`, multiplicative or not.
**Recommended formulation**:

```lean
theorem convProduct_assoc (α β γ : Forest → ℝ) :
    convProduct (convProduct α β) γ = convProduct α (convProduct β γ)
```

(no hypotheses). This is the cleaner statement and matches how
Mathlib formulates `Polynomial.mul_assoc` etc. The `IsMultiplicative`
hypotheses are not used in Butcher's textbook proof either — the
identity is purely combinatorial. The textbook *applies* it within
the multiplicative-mappings group, but the lemma itself is more
general.

### Proof skeleton — three explicit sub-lemmas

The textbook proof flattens both sides into a triple-sum over
`Q ⊑ R ⊑ S` and reindexes. Decompose into **three named sub-lemmas**;
write all three sorry-first, submit ≤2 to Aristotle, prove the rest
manually.

#### Sub-lemma 1 — flatten `(αβ)γ` into a flat triple sum

```lean
private lemma convProduct_left_eq_flatten (α β γ : Forest → ℝ) (S : Forest) :
    convProduct (convProduct α β) γ S
      = (S.powerset.bind (fun Q =>
          (S - Q).powerset.map (fun R' => α ((S - Q) - R') * β R' * γ Q))).sum
```

Proof sketch: unfold `convProduct (convProduct α β) γ` once, then
unfold the inner `convProduct α β`, then use
`Multiset.sum_map_mul_right` (or push the outer `γ Q` into the
inner sum via direct `mul_sum` distribution), then convert the
iterated map-sum into a `bind`-sum via
`Multiset.sum_bind`/`Multiset.bind_map`.

#### Sub-lemma 2 — flatten `α(βγ)` into a flat triple sum

```lean
private lemma convProduct_right_eq_flatten (α β γ : Forest → ℝ) (S : Forest) :
    convProduct α (convProduct β γ) S
      = (S.powerset.bind (fun R =>
          R.powerset.map (fun Q => α (S - R) * β (R - Q) * γ Q))).sum
```

Proof sketch: symmetric to sub-lemma 1.

#### Sub-lemma 3 — the load-bearing reindexing (combinatorial identity)

```lean
private lemma triple_sum_reindex (S : Forest) (f : Forest → Forest → Forest → ℝ) :
    (S.powerset.bind (fun Q =>
      (S - Q).powerset.map (fun R' => f Q R' (S - Q - R')))).sum
    = (S.powerset.bind (fun R =>
      R.powerset.map (fun Q => f Q (R - Q) (S - R)))).sum
```

This is the bijection `(Q, R') ↔ (R, Q)` via `R := Q + R'`,
`R' := R - Q`. Both sides enumerate ordered triples `(X, Y, Z)`
with `X + Y + Z = S` (where `X = Q`, `Y = R - Q = R'`,
`Z = S - R = S - Q - R'`).

**Recommended proof technique**: prove a stronger multiset-level
equality first:

```lean
private lemma powerset_bind_swap (S : Forest) :
    S.powerset.bind (fun Q => (S - Q).powerset.map (fun R' => (Q, R')))
    = S.powerset.bind (fun R => R.powerset.map (fun Q => (Q, R - Q)))
```

(equality of `Multiset (Forest × Forest)`), and derive
`triple_sum_reindex` from it via `Multiset.sum_map_congr` plus the
`f`-substitution `f Q (R - Q) (S - R) = f Q R' (S - Q - R')` when
`R = Q + R'`.

Try by induction on `S` using `Multiset.induction`. Base case
`S = 0` is `[(0, 0)] = [(0, 0)]`. Inductive case: add a tree `t`,
expand both sides via `Multiset.powerset_cons` and
`Multiset.cons_sub_*` identities. This may need an auxiliary
`cons_sub_of_le` style lemma — check `lean_local_search` for the
exact name before inventing one.

If the inductive proof is too painful, an alternative is to
explicitly construct the bijection `(Q, R') ↔ (Q + R', Q)` as a
`Multiset.Nodup`-aware `Equiv`. **Not recommended** for this cycle
— it requires more Mathlib machinery than the inductive route.

### Combine sub-lemmas

```lean
theorem convProduct_assoc (α β γ : Forest → ℝ) :
    convProduct (convProduct α β) γ = convProduct α (convProduct β γ) := by
  funext S
  rw [convProduct_left_eq_flatten, convProduct_right_eq_flatten,
      ← triple_sum_reindex]
```

### Aristotle batch for cycle 079

Submit at most two sub-lemmas to Aristotle, batched in a single
file `.prover-state/aristotle_submissions/cycle_079/section383b.lean`:

* **Sub-lemma 3** (`powerset_bind_swap` and/or
  `triple_sum_reindex`) — the combinatorial reindexing. **Highest
  Aristotle leverage** (premise selection on `Multiset.bind` /
  `powerset_cons` may surface the right inductive shape).
* **Sub-lemma 1 or 2** (flattening) — moderate leverage; may close
  via `simp [convProduct, Multiset.sum_bind, Multiset.bind_map,
  Multiset.sum_map_mul_left]` plus a `ring`-level rearrangement.

Submit at the **start** of the cycle right after the Aristotle
status check (so it has 30+ min to run while you do manual work).

### Manual work plan

1. Write the three sub-lemma signatures + the main theorem
   signature, all with `sorry`. Verify the file compiles
   (`lake env lean OpenMath/Chapter3/Section383.lean`).
2. Submit the Aristotle batch (sub-lemmas 1+3 or 2+3).
3. Prove **sub-lemma 1** manually first (it is the most mechanical:
   distribute `γ Q`, rewrite via `Multiset.sum_bind`, etc.). Target
   ~30 lines.
4. Prove **sub-lemma 2** by symmetric argument (~30 lines).
5. If Aristotle returns sub-lemma 3, integrate. Otherwise attempt
   the inductive proof manually; if it stalls past ~60 min of
   wall-clock, **fall back** to leaving sub-lemma 3 as `sorry` and
   commit the partial scaffold (cycle 080 can finish it). Sorry-first
   partial is acceptable per CLAUDE.md provided the
   `.prover-state/task_results/cycle_079.md` faithfulness section
   documents the gap and an issue file
   `.prover-state/issues/lem_383B_reindex_pending.md` is created.
6. Otherwise close `convProduct_assoc` from the three sub-lemmas
   (~5 lines).

### Hypothesis weakening — faithfulness flag

Butcher's textbook statement requires `α, β, γ` multiplicative.
Our proposed Lean statement drops these hypotheses. This is a
**genuine weakening** (not strengthening) and is faithful: the
generalised lemma implies Butcher's. Document the relationship in a
docstring comment:

> "Butcher's §383 Lemma 383B requires the three mappings to be
> multiplicative; this Lean version states the more general purely-
> combinatorial associativity, of which Butcher's is the special
> case."

Mention this in the cycle 079 faithfulness check.

### Non-vacuity

`isMultiplicative_const_one` (already in file) plus the new
`convProduct_assoc` together imply that `convProduct` is associative
on multiplicative mappings. No new witness required — the existing
constant-1 witness suffices.

## What NOT to do

* **Do NOT** poll Aristotle more than once. CLAUDE.md is explicit;
  the cycle 040/078 consultant notes echo the rule.
* **Do NOT** introduce `axiom`/`constant` for any of the three
  sub-lemmas. If the reindexing genuinely cannot be proved in one
  cycle, leave it as `sorry` with an issue file.
* **Do NOT** rebuild `lem:383A` infrastructure — `Forest`,
  `IsMultiplicative`, `convProduct`, `_PowersetAdd.powerset_add`,
  and `_PowersetAdd.sum_mul_sum_eq_sum_product` are all already in
  `Section383.lean` and load-bearing. Reuse, do not redefine.
* **Do NOT** define a parallel "pointwise" associativity statement
  on top of the convolution one. The cycle 078 task results
  explicitly noted that the pointwise variant would be definition
  smuggling for §383's group structure.
* **Do NOT** edit `OpenMath/Chapter3/Section310.lean` to add a
  `DecidableEq RootedTree` instance there. The cycle 078 placement
  inside `Section383.lean` (via `Classical.decEq`) is deliberate —
  keeping `Section310` computable is preserved.
* **Do NOT** raise `maxHeartbeats` above 200000; if the reindexing
  proof is too heavy, decompose further (e.g. peel off a
  `Multiset.bind_powerset_cons` helper).
* **Do NOT** modify `scripts/autonomous_loop.py` (loop-maintainer
  territory; the cycle 014/015 stale-`attempts.md` issue is tracked
  in `tautology_scanner_false_positives.md`).
* **Do NOT** edit `extraction/raw_text/` or
  `extraction/formalization_data/entities/`; both are regenerated
  (see `extraction/CLAUDE.md` §3). Only
  `lean_status.json::lem:383B` (or `thm:410D` under Path A) is
  editable.
* **Do NOT** expand scope into `lem:383C` (Existence of Left and
  Right Inverses) or `lem:383D` (group inverse formula) this cycle
  — both depend on §383B and require single-tree-domain restriction
  (`G_1`) plus an order-induction on rooted trees (per cycle 078
  task results). Cycle 080 territory.
* **Do NOT** start `def:381F` (P-equivalent) as a fallback — its
  textbook definition uses the "reduced method" construction
  deferred per `.prover-state/issues/reduced_method_deferred.md`,
  and that blocker is unresolved. If §383B blows up, the proper
  fallback is **partial commit** of the sorry-first §383B scaffold,
  not a pivot.

## Failed approaches recorded in attempts.md (do not repeat)

* Cycle 078: planner Path B "pointwise multiplicativity" formulation
  — rejected as definition smuggling. The convolution formulation
  is the only faithful encoding.
* Cycle 077: `subst log expPS = 1 + X` direct coefficient
  computation via `PowerSeries.coeff_subst` — Bell-polynomial
  machinery missing in Mathlib; returned to Aristotle batch.
* Cycle 071: staging Lean changes without committing — same
  commits-not-reaching-repo failure as cycles 008/035; verify with
  `git rev-parse HEAD == origin/Main/Experiments` after the commit
  step.
* Cycle 050: `Finset.sum_le_sum_nbij'` does not exist; not directly
  relevant here but the same reindexing pattern (use
  `← Finset.sum_image hinj` + `sum_le_sum_of_subset_of_nonneg`)
  applies if Multiset reindexing fails and we need an inequality.
* Cycle 060: single ~430-line target without decomposition →
  regression. Hence the explicit three-sub-lemma decomposition
  above.

## Pre-commit checklist (CLAUDE.md, abbreviated for this cycle)

- [ ] **Definition smuggling check**: `convProduct_assoc` proves
      genuine combinatorial associativity, not a vacuous restatement.
      The proof manipulates a triple sum, not a single hypothesis.
- [ ] **Tautology check**: the conclusion is not verbatim a
      hypothesis (no hypothesis on the form `(αβ)γ = α(βγ)` exists
      at the top level — it is constructed).
- [ ] **Hypothesis strength check**: drop the unused
      `IsMultiplicative` hypotheses; document the divergence
      relative to Butcher's literal statement (this is a *weakening*
      of hypotheses, hence a *strengthening* of the conclusion's
      generality, which is acceptable and documented).
- [ ] **Absent-theorem check**: every `private lemma` named in the
      theorem chain is actually proved (modulo the explicit
      sorry-first fallback for sub-lemma 3, which must have a matching
      issue file `.prover-state/issues/lem_383B_reindex_pending.md`).
- [ ] **`lake build OpenMath.Chapter3.Section383`** clean before
      commit (so `#print axioms` reads from fresh .olean, not the
      cycle 072 cache trap).
- [ ] **Axiom check**: `#print axioms convProduct_assoc` →
      `[propext, Classical.choice, Quot.sound]` only (cycle 078's
      `Classical.decEq` instance has already trade-balanced the
      Quot.sound contribution).
- [ ] **`lean_status.json::lem:383B`** updated to `formalized` with
      file pointer `OpenMath/Chapter3/Section383.lean` and symbol
      `OpenMath.Chapter3.Section383.convProduct_assoc`.
- [ ] **`plan.md`**: mark `lem:383B` as `[x]`; bump progress 50/175 →
      51/175.
- [ ] **Push verified**: after `git push`, run `git rev-parse HEAD`
      and `git rev-parse origin/Main/Experiments`; confirm equal.

## Suggested cycle-080 follow-ups

* If sub-lemma 3 was left as `sorry` this cycle: close it (Aristotle
  + manual hybrid).
* Otherwise: `lem:383C` (Existence of Left and Right Inverses) —
  switch from `Forest → ℝ` to single-tree domain `G_1 := T → ℝ`,
  prove existence of left/right inverses by order-induction on
  rooted trees.
* Then `thm:382A` (group structure) and `lem:383D` (inverse
  formula) follow naturally.
