# Cycle 080 Strategy — `lem:383B` (associativity of multiplicative forest mappings)

## Status going in

- Cycle 079 closed `thm:410D`. The §410 cluster (410A/B/C/D) is fully done.
- Progress: 51/175.
- No Aristotle results pending (cycle 077's batch was consumed in 079).
- Current sorry count: 0.
- The cycle 077 issue file `thm_410D_substitution.md` was never committed
  (cycle 079's task results §"Discovery" item 3) — nothing to delete this
  cycle.

## Target this cycle

**`lem:383B` — associativity of multiplicative forest mappings**
(Butcher §383, p. 309).

This is the natural successor to cycle 078's `lem:383A`
(`multiplicative_conv` in `OpenMath/Chapter3/Section383.lean:165`), which
proved the convolution product preserves multiplicativity. `lem:383B`
proves the convolution product is associative — together they make
`Forest → ℝ` (with the convolution product) a monoid; combined with
`lem:383C`, the multiplicative-`α`-with-`α(∅)=1` mappings form a group
(Butcher's "Runge–Kutta group" `G₁`).

**Why this and not the alternatives:**

- `thm:422A` (LMM underlying one-step method) and `thm:441C` /
  `lem:441A` / `lem:441B` (order-bound cluster) are good Chapter-4
  successors but they consume more LMM infrastructure than is in place
  (and `441C` needs §410D as a tool — now closed, but the order-bound
  cluster is multi-cycle).
- `lem:383B` is single-cycle, infrastructure is *already* in place
  (cycle 078 built `Forest`, `convProduct`, `IsMultiplicative`,
  `_PowersetAdd.powerset_add`, `_PowersetAdd.sum_mul_sum_eq_sum_product`),
  and the textbook proof is the algebraic 4-step manipulation.
- `lem:383C` depends on `lem:383B` per its `dependencies` field (cycle
  081 territory).

**Textbook statement** (verbatim from
`extraction/formalization_data/entities/lem_383B.json`):

> Let α, β and γ be multiplicative mappings from forests to reals.
> Then `(αβ)γ = α(βγ)`.

**Textbook proof** (from same file):

> If Q ⊆ R ⊆ S then (R \ Q) ⊆ (S \ Q). Hence we find
>
>   `((αβ)γ)(S) = Σ_{Q ⊑ S} (αβ)(S - Q) γ(Q)`
>              `= Σ_{Q ⊑ S} Σ_{T ⊑ S-Q} α((S-Q) - T) β(T) γ(Q)`
>              `= Σ_{Q ⊑ R ⊑ S} α(S - R) β(R - Q) γ(Q)`     [reindex T = R - Q, R = Q + T]
>              `= Σ_{R ⊑ S} α(S - R) (βγ)(R)`
>              `= (α(βγ))(S)`.

The key combinatorial step is the third equality: for fixed `Q ⊑ S`,
the map `T ↦ Q + T` bijects `(S - Q)`'s sub-multisets with the
sub-multisets `R` of `S` containing `Q`.

## Faithfulness check (do this BEFORE coding)

Open `extraction/formalization_data/entities/lem_383B.json` and confirm
the Lean statement below captures the textbook content. The Lean
target is:

```lean
theorem convProduct_assoc (α β γ : Forest → ℝ) :
    convProduct (convProduct α β) γ = convProduct α (convProduct β γ)
```

Note: the textbook does **not** use multiplicativity of α/β/γ in the
proof — associativity holds for the convolution product on *all*
`Forest → ℝ`, and the textbook's `(αβ)(R) = ...` notation just refers
to the convolution. This means the Lean theorem can be stated without
`IsMultiplicative` hypotheses; that is a *generalisation* of the
textbook content, not a strengthening, and is faithful. Document this
in the docstring.

The statement is a *real* theorem (LHS and RHS unfold to genuinely
different sums; the proof requires the bijection); it is not a
tautology.

## Approach (Aristotle-first, per CLAUDE.md MANDATORY rule)

### Step 1: write the sorry-first scaffold (~30 min)

Open `OpenMath/Chapter3/Section383.lean` and append, after
`isMultiplicative_const_one` (line 221, before
`end OpenMath.Chapter3.Section383`), the following structure. All
proofs are `sorry` initially; verify the structure compiles, then
**commit the scaffold** (so the cycle has a checkpoint before
submitting to Aristotle).

```lean
/-! ### Lemma 383B — convolution is associative -/

/-- Key combinatorial bijection: for fixed `S`, summing first over
`Q ≤ S` and then over `T ≤ S - Q` is the same as summing first over
`R ≤ S` and then over `Q ≤ R` with `T = R - Q`.

This is the multiset analogue of the textbook reindexing
`Σ_{Q ⊑ R ⊑ S} f(R-Q, Q) = Σ_{Q ⊑ S, T ⊑ S-Q} f(T, Q)` via the
bijection `(Q, T) ↔ (Q + T, Q)`. -/
private theorem double_powerset_swap
    (S : Multiset RootedTree)
    (f : Multiset RootedTree → Multiset RootedTree → ℝ) :
    ((S.powerset).bind
        (fun Q => (S - Q).powerset.map (fun T => f Q T))).sum
      = ((S.powerset).bind
          (fun R => R.powerset.map (fun Q => f Q (R - Q)))).sum := by
  sorry

/-- Expansion of the LHS of associativity as a double sum. -/
private theorem convProduct_assoc_lhs_eq (α β γ : Forest → ℝ) (S : Forest) :
    convProduct (convProduct α β) γ S
      = ((S.powerset).bind
          (fun Q => (S - Q).powerset.map
            (fun T => α (S - Q - T) * β T * γ Q))).sum := by
  sorry

/-- Expansion of the RHS of associativity as a double sum. -/
private theorem convProduct_assoc_rhs_eq (α β γ : Forest → ℝ) (S : Forest) :
    convProduct α (convProduct β γ) S
      = ((S.powerset).bind
          (fun R => R.powerset.map
            (fun Q => α (S - R) * β (R - Q) * γ Q))).sum := by
  sorry

/-- **Butcher §383 Lemma 383B** — the convolution product on
forest mappings is associative.

> Let α, β and γ be multiplicative mappings from forests to the real
> numbers. Then (αβ)γ = α(βγ).

Faithfulness note: the textbook hypothesises multiplicativity of
α, β, γ, but its proof uses only the algebraic structure of the
convolution sum (not multiplicativity). The Lean statement therefore
drops the hypothesis — a faithful generalisation. -/
theorem convProduct_assoc (α β γ : Forest → ℝ) :
    convProduct (convProduct α β) γ = convProduct α (convProduct β γ) := by
  funext S
  rw [convProduct_assoc_lhs_eq, convProduct_assoc_rhs_eq]
  -- Apply the bijection with f := fun Q T => α (S - Q - T) * β T * γ Q.
  -- LHS double sum:  Σ_{Q ≤ S} Σ_{T ≤ S-Q}  α (S - Q - T) * β T      * γ Q
  -- RHS double sum:  Σ_{R ≤ S} Σ_{Q ≤ R}    α (S - R)     * β (R - Q) * γ Q
  -- After `double_powerset_swap` with the LHS f, the LHS becomes
  --   Σ_{R ≤ S} Σ_{Q ≤ R} α (S - Q - (R - Q)) * β (R - Q) * γ Q.
  -- Then `S - Q - (R - Q) = S - (Q + (R - Q)) = S - R` (using
  -- `Multiset.sub_add_eq_sub_sub` and `Multiset.add_sub_cancel'` /
  -- `Multiset.add_tsub_cancel_of_le`) collapses each summand to
  -- the RHS form.
  sorry
```

After writing this, run:

```bash
lake env lean OpenMath/Chapter3/Section383.lean
```

Confirm it compiles with **only** the four `sorry`s (no errors, no
unintentional new sorries elsewhere). Then **commit this scaffold**
with a `[scaffold]` tag in the message so the cycle has a checkpoint
even if Aristotle stalls.

### Step 2: submit the four sorries to Aristotle (~10 min)

Use `mcp__aristotle__submit_file` with a self-contained file mirroring
`Section383.lean`'s imports plus the four sorry-first definitions. Or
use `mcp__aristotle__submit_directory` against
`.prover-state/aristotle_submissions/cycle_080/` containing the
project's `lakefile.toml`, `lean-toolchain`, and a single
`Aristotle383B.lean` mirror file.

The four targets, in priority order:

1. **`double_powerset_swap`** — the key bijection. Hardest of the
   four; this is the genuine Mathlib gap (no off-the-shelf lemma swaps
   the order of `Multiset.powerset.bind`-quantifiers like this).
   Aristotle's odds: moderate. The textbook bijection is
   `(Q, T) ↔ (Q + T, Q)`; if Aristotle finds a `Multiset.ext` +
   induction argument, this lands. **If it fails, this is the manual
   fallback for cycle 081.**

2. **`convProduct_assoc_lhs_eq`** — unfold the outer convolution and
   distribute the inner sum through multiplication by `γ Q`. The
   needed identity:
   ```
   ((S.powerset).map (fun Q =>
       ((S - Q).powerset.map (fun T => α ((S - Q) - T) * β T)).sum
       * γ Q)).sum
   = ((S.powerset).bind (fun Q =>
       (S - Q).powerset.map (fun T => α (S - Q - T) * β T * γ Q))).sum
   ```
   Mathlib lemmas Aristotle should reach for:
   `Multiset.sum_map_mul_right`, `Multiset.sum_bind`,
   `Multiset.sum_map_mul_left`. Aristotle's odds: high (canonical
   sum-distributivity).

3. **`convProduct_assoc_rhs_eq`** — symmetric to (2); unfold the
   *inner* convolution `(βγ) R = Σ_{Q ≤ R} β (R - Q) * γ Q`, then
   distribute by `α (S - R)`. Aristotle's odds: high.

4. **`convProduct_assoc`** — given (1) and (2) and (3), the proof is
   `funext S; rw [convProduct_assoc_lhs_eq, convProduct_assoc_rhs_eq]`,
   then reduce LHS to RHS using `double_powerset_swap` instantiated
   with `f := fun Q T => α (S - Q - T) * β T * γ Q`. After the swap,
   the goal becomes:
   ```
   Σ over (R ≤ S, Q ≤ R) of  α (S - Q - (R - Q)) * β (R - Q) * γ Q
   =
   Σ over (R ≤ S, Q ≤ R) of  α (S - R) * β (R - Q) * γ Q
   ```
   These are equal pointwise: under `Q ≤ R`,
   `Q + (R - Q) = R` (Mathlib: `Multiset.add_tsub_cancel_of_le`,
   `Multiset.sub_add_cancel`), so `S - Q - (R - Q) = S - (Q + (R - Q))
   = S - R` by `Multiset.sub_add_eq_sub_sub` (which is
   `s - (t + u) = s - t - u`, see
   `Mathlib/Data/Multiset/AddSub.lean:334`). Use `Multiset.sum_congr`
   or rewrite under the bind. Aristotle's odds: moderate (clean
   tactic chain).

After submission, **sleep 30 minutes** (CLAUDE.md MANDATORY rule). Do
not poll repeatedly — exactly one `mcp__aristotle__get_status` call
after the sleep window.

### Step 3: incorporate Aristotle returns

After 30 min, run `mcp__aristotle__get_status` once. If complete,
extract proofs via `mcp__aristotle__extract_result`. For each returned
proof:

- Verify it compiles in your scaffold (paste in, run
  `lake env lean OpenMath/Chapter3/Section383.lean`).
- Verify lemma names cited in the proof exist
  (`lean_local_search "<name>"` or `lean_hover_info`). Aristotle has
  invented non-existent lemma names in the past
  (`Finset.sum_le_sum_nbij'` was the cycle 050 false flag) — verify
  before committing.
- After the file builds clean, run
  `lake build OpenMath.Chapter3.Section383` (NOT `lake env lean`
  alone — per cycle 072 dead end, the .olean cache only updates on
  `lake build`).
- `#print axioms <name>` should return
  `[propext, Classical.choice, Quot.sound]` only. (The
  `noncomputable instance : DecidableEq RootedTree` workaround at
  `Section383.lean:65` already pulls in `Classical.choice`; that's
  expected and not an extra axiom.)
- If any check fails, the Aristotle proof has a real bug;
  fix or fall back to manual.

### Step 4: manual fallback for what Aristotle missed

If `double_powerset_swap` (the bijection) is the only remaining sorry,
the manual proof goes:

**Approach A: induction on `S` (recommended).**
```lean
private theorem double_powerset_swap
    (S : Multiset RootedTree)
    (f : Multiset RootedTree → Multiset RootedTree → ℝ) :
    ((S.powerset).bind
        (fun Q => (S - Q).powerset.map (fun T => f Q T))).sum
      = ((S.powerset).bind
          (fun R => R.powerset.map (fun Q => f Q (R - Q)))).sum := by
  induction S using Multiset.induction with
  | empty =>
    simp [Multiset.powerset_zero, Multiset.zero_sub]
  | cons a s IH =>
    -- (a ::ₘ s).powerset = s.powerset + s.powerset.map (a ::ₘ ·)
    rw [Multiset.powerset_cons]
    rw [Multiset.bind_add, Multiset.bind_add]
    rw [Multiset.sum_add, Multiset.sum_add]
    -- Goal: (LHS first half + LHS second half) = (RHS first half + RHS second half)
    -- LHS first half = sum over Q ≤ s, T ≤ (a::s) - Q of f Q T  -- but Q ≤ s ≤ a::s so (a::s)-Q = a ::ₘ (s - Q)
    -- RHS first half = sum over R ≤ s, Q ≤ R of f Q (R - Q)
    -- Match each half separately. The IH applies to `s`, not `a::s`,
    -- so the induction step is non-trivial; need to relate
    -- (a::s).powerset.bind to s.powerset.bind via casework on whether
    -- `a` is in `Q` (LHS) or `R` (RHS).
    sorry  -- Roughly 60-90 lines.
```

**Approach B: prove via `Multiset.ext`-on-counts in the bind.**
Show that for any indexed pair `(Q, T)` on the LHS multiset and any
`(R, Q')` on the RHS multiset, the `Multiset.count` matches under the
bijection. Use `Multiset.count_bind`. May be cleaner if it exists.

If both fail, **decompose the bijection further** into a pair-multiset
identity (without `f`):
- Sub-helper `B1`:
  `(S.powerset).bind (fun Q => (S - Q).powerset.map (fun T => (Q, T)))`
  equals (as a `Multiset (Forest × Forest)`)
  `(S.powerset).bind (fun R => R.powerset.map (fun Q => (Q, R - Q)))`.
- Then the f-version follows by `Multiset.map_congr`.

If even `B1` is hard, file an issue at
`.prover-state/issues/double_powerset_swap_deferred.md` describing
the gap, and ship the cycle with `convProduct_assoc_lhs_eq`,
`convProduct_assoc_rhs_eq` proved (and the bijection sorry isolated).
Cycle 081 picks it up. **A cycle that closes 2 of the 4 sorries is
still positive progress** — do not panic-revert if Aristotle returns
nothing useful for `double_powerset_swap`.

## What NOT to try (failed approaches from past cycles)

- **Do NOT increase `maxHeartbeats` above 200000** (CLAUDE.md hard
  rule). If a proof is slow, decompose it.
- **Do NOT introduce `axiom`/`constant`** to bypass the bijection
  (CLAUDE.md hard rule). If you can't prove it, file an issue.
- **Do NOT propose a "trivial pointwise multiplicativity" version**
  of `lem:383B` — cycle 078's task results §"Dead ends" called this
  out as definition smuggling for `lem:383A`; the same argument
  applies here. The convolution product is the genuine textbook
  object; do not weaken to a pointwise product.
- **Do NOT skip the sorry-first commit before submitting to
  Aristotle.** Cycle 040's task results recorded a near-miss where
  the worker did all the manual proof first; the sorry-first scaffold
  commit guarantees the cycle has *some* progress on a worst-case
  Aristotle timeout, and supervisor's "commits not reaching repo"
  phantoms (cycles 008, 035, 071, 073) all involved missed
  intermediate commits.
- **Do NOT submit `convProduct_assoc` standalone to Aristotle**
  without sub-lemmas 1/2/3 also in the prompt — Aristotle would have
  to rediscover the entire decomposition, and the bijection step is
  hard to find from first principles.
- **Do NOT use `Multiset.sum_le_sum_nbij'` or `Finset.sum_le_sum_nbij'`**
  — neither exists (per
  `feedback_finset_sum_le_sum_nbij_nonexistent` user-memory rule).
  We don't need it here, but flagging because Aristotle sometimes
  invents non-existent lemma names; verify each name with
  `lean_local_search` before pasting an Aristotle proof.
- **Do NOT use `Multiset.mul_sum`** — it does not exist (cycle 078
  dead end). The correct name is `Multiset.sum_map_mul_left`.
- **Do NOT silently rename `_PowersetAdd.powerset_add` or
  `_PowersetAdd.sum_mul_sum_eq_sum_product`** (cycle 078 helpers).
  Both should remain in the `_PowersetAdd` namespace.
- **Do NOT touch `RootedTree`'s `noncomputable instance : DecidableEq`
  workaround** at line 65. It is the standing solution for the
  nested-inductive deriving failure (cycle 078 dead end); leaving it
  alone is the right move.
- **Do NOT chase the prompt-builder's "stuck on" / "What's tried
  recently" rows from `attempts.md`.** Per
  `consultant_advice_cycle_009.md` §A and
  `consultant_advice_cycle_015.md` §B, those rows are stale carry-overs
  and are routinely contradicted by HEAD. The current task is fresh.

## Pre-commit checklist (per CLAUDE.md)

After the four sorries are closed:

- [ ] Run `lake env lean OpenMath/Chapter3/Section383.lean` —
      clean exit, no errors.
- [ ] Run `lake build OpenMath.Chapter3.Section383` (mandatory before
      `#print axioms` per cycle 072 cache rule).
- [ ] `#print axioms convProduct_assoc` →
      `[propext, Classical.choice, Quot.sound]` only.
      (Same check for `double_powerset_swap`.)
- [ ] **Faithfulness — definition smuggling check**: confirm
      `convProduct_assoc` is `convProduct (convProduct α β) γ =
      convProduct α (convProduct β γ)` with no extra hypotheses.
- [ ] **Faithfulness — tautology check**: confirm conclusion does
      not appear verbatim as a hypothesis. (Cannot — there are no
      hypotheses other than the implicit `α β γ : Forest → ℝ`.)
- [ ] **Faithfulness — hypothesis strength check**: the textbook
      hypothesises multiplicativity; we drop it (the convolution
      product is associative regardless). This is a *generalisation*,
      not a strengthening. Document in the docstring.
- [ ] Update
      `extraction/formalization_data/lean_status.json`: set
      `lem:383B` row to `formalized` with
      `lean_file = "OpenMath/Chapter3/Section383.lean"`,
      `lean_symbol = "OpenMath.Chapter3.Section383.convProduct_assoc"`.
- [ ] Update `plan.md` Chapter 3 row: mark `[x] lem:383B` and bump
      "Progress: 51 / 175" → "52 / 175".
- [ ] Write `.prover-state/task_results/cycle_080.md` per CLAUDE.md
      template.
- [ ] **`git push`** to `origin/Main/Experiments`. Verify
      `git rev-parse HEAD == git rev-parse origin/Main/Experiments`
      before reporting cycle complete (cycles 008, 035, 071, 073
      were "commit-not-reaching-repo" failures; do not repeat).

## Stretch goal (only if time permits after the main target lands)

If `convProduct_assoc` lands cleanly with > 30 min of cycle time
remaining: also formalize a one-line corollary that `convProduct`
preserves multiplicativity through the associativity:

```lean
theorem multiplicative_conv_assoc {α β γ : Forest → ℝ}
    (hα : IsMultiplicative α) (hβ : IsMultiplicative β) (hγ : IsMultiplicative γ) :
    IsMultiplicative (convProduct (convProduct α β) γ) :=
  multiplicative_conv (multiplicative_conv hα hβ) hγ
```

This is purely documentation value — no plan entity gains. Skip if
any pre-commit checklist item is unchecked.

## Cycle budget

- Step 1 (scaffold + checkpoint commit): 30 min
- Step 2 (Aristotle submission): 10 min
- Step 3 (sleep + integrate): 30 min sleep + 30 min integrate
- Step 4 (manual fallback for what Aristotle missed): 30-60 min
- Faithfulness check + commit + push: 15 min

**Total: 2.5-3 hours.** If Aristotle returns all four cleanly,
the cycle finishes in ~1.5 hours.
