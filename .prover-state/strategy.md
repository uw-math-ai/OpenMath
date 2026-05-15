# Cycle 251 strategy

## A. Headline directive

**Ship `alphaWeight_pos` (Butcher α(t) > 0) plus its two structural
prerequisites `density_pos` and `symmetry_pos`, all in
`OpenMath/Chapter3/Section301.lean`.** This is a clean, low-risk
single-cycle deliverable that closes the obvious infrastructure gap
left by cycle 250: every downstream consumer of α(t) (sums for
B-series Taylor expansions, the Φ(t) = 1/γ(t) order conditions, the
σ(t)γ(t) ratio in (302a)) needs positivity to use Mathlib's positivity
and divisibility APIs. No new entities, no new mathematical content
— pure infrastructure built from the existing mutual recursions.

This is option (2) from cycle 250's "Suggested next approach". Options
(1) (`lem:310B` proper, multi-cycle tree-indexed-sum infrastructure)
and (3) (combinatorial equivalence of α(t), multi-cycle) are
deliberately deferred. Option (4) (Φ values on more RK methods) is a
fine fallback if the primary plan stalls — see §G.

## B. What to ship (concrete)

Three new public theorems plus one preserving move.

### B.1 — Move `order_pos` from Section323 to Section301

`order_pos` currently lives at `OpenMath/Chapter3/Section323.lean:55–58`
in namespace `OpenMath.Chapter3.Section310.RootedTree`. It's load-bearing
for `density_pos`. **Move it** (don't duplicate) to
`OpenMath/Chapter3/Section301.lean`, immediately before the new
`density_pos` block — same namespace, same body:

```lean
/-- Every rooted tree has at least one vertex (the root), so its order
is positive. -/
theorem order_pos : ∀ t : RootedTree, 0 < t.order
  | mk children => by
      show 0 < 1 + orderSum children
      omega
```

Then delete lines 53–60 from Section323.lean (the docstring + theorem +
the trailing `end OpenMath.Chapter3.Section310.RootedTree` if it's only
there to close this one theorem — read the file first to confirm).
Section323's two consumers (lines 84 and 111) keep working via the
Section301 → Section323 import chain without any edit at the call sites.

This move is the minimum-effort way to get `order_pos` available where
it's needed without duplication.

### B.2 — `density_pos` and `densityProd_pos`

Inserted after `density_eq` (current line ~156) and before the symmetry
block (current line ~157), in `namespace OpenMath.Chapter3.Section310.RootedTree`:

```lean
/-- `γ(t) > 0` for every rooted tree (every product factor is
positive: the root order is `≥ 1`, and each subtree's density is
positive by structural induction). -/
mutual
  theorem density_pos : ∀ t : RootedTree, 0 < density t
    | mk children => by
        show 0 < order (mk children) * densityProd children
        exact Nat.mul_pos (order_pos _) (densityProd_pos children)
  theorem densityProd_pos : ∀ cs : List RootedTree, 0 < densityProd cs
    | [] => by decide
    | t :: ts => by
        show 0 < density t * densityProd ts
        exact Nat.mul_pos (density_pos t) (densityProd_pos ts)
end
```

The `show` tactics expose the definitional unfolds (matching
`density`/`densityProd`'s literal bodies — see Section301.lean
lines 134–139). `Nat.mul_pos` is core; the `decide` on `0 < 1` is
trivial.

### B.3 — `symmetry_pos` and `symmetryProd_pos`

Inserted after `σ_recursion` (current line ~217) and before
`tau_values` (current line ~221):

```lean
/-- `σ(t) > 0` for every rooted tree. The `symmetryProd` walk emits
factors of the form `mᵢ! · σ(tᵢ)^{mᵢ}` (each positive by induction +
`Nat.factorial_pos` + `Nat.pos_pow_of_pos`); the empty-cursor base
case is `1`. -/
mutual
  theorem symmetry_pos : ∀ t : RootedTree, 0 < symmetry t
    | mk children => by
        show 0 < symmetryProd children children
        exact symmetryProd_pos children children
  theorem symmetryProd_pos :
      ∀ full cursor : List RootedTree, 0 < symmetryProd full cursor
    | _, [] => by decide
    | full, t :: rest => by
        unfold symmetryProd
        split_ifs with h
        · exact symmetryProd_pos full rest
        · refine Nat.mul_pos (Nat.mul_pos (Nat.factorial_pos _) ?_) ?_
          · exact Nat.pos_pow_of_pos _ (symmetry_pos t)
          · exact symmetryProd_pos full rest
end
```

Mathlib hooks used:
- `Nat.factorial_pos : ∀ n, 0 < n.factorial` (in
  `Mathlib.Data.Nat.Factorial.Basic`, already pulled by the existing
  Section301 imports for `alphaWeight_vertex`).
- `Nat.pos_pow_of_pos : ∀ (n : ℕ), 0 < b → 0 < b ^ n` (in
  `Mathlib.Algebra.Order.Group.Nat` or similar). If
  `lean_local_search "pos_pow_of_pos"` shows this name has drifted,
  the fallback is generic `pow_pos (symmetry_pos t) (full.count t)`
  which gives the same conclusion via the ordered-semiring API.

### B.4 — `alphaWeight_pos`

Inserted **immediately after** `alphaWeight_vertex` (current line ~269)
and **before** the four `example` blocks (lines 271+):

```lean
/-- Butcher §302 α(t) is strictly positive: `r(t)! > 0` (since
factorials are positive), `σ(t) > 0` (§B.3), and `γ(t) > 0` (§B.2),
so the quotient `r(t)!/(σ(t)γ(t))` is positive. -/
theorem alphaWeight_pos (t : RootedTree) : 0 < alphaWeight t := by
  unfold alphaWeight
  apply div_pos
  · exact_mod_cast Nat.factorial_pos t.order
  · apply mul_pos
    · exact_mod_cast symmetry_pos t
    · exact_mod_cast density_pos t
```

`div_pos`, `mul_pos`, and `exact_mod_cast` are all standard. The cast
fires because `Nat.cast_pos.mpr` is built into `exact_mod_cast`'s
preprocessing.

### B.5 — Sanity examples (optional but recommended)

Add up to two `example` blocks confirming positivity on the same
trees used as cycle 250's α-value witnesses. These are NOT new
theorems, just non-vacuity checks:

```lean
example : 0 < alphaWeight broom₃ := alphaWeight_pos broom₃
example : 0 < alphaWeight (mk [vertex, cherry]) :=
  alphaWeight_pos (mk [vertex, cherry])
```

Keep ≤ 5 LOC. If `alphaWeight_pos` typechecks they trivially follow,
but they help future tautology-scanner audits see real consumers.

## C. Tactic recipes — what to try first

For each new theorem, the proof shape is **mutual structural
recursion** matching the cycle 249 / 250 / `density_eq` template.
Do NOT try `induction t with | mk children ih`-style induction on
RootedTree — per memory `feedback_rootedtree_nested_induction.md`,
nested inductives don't autogen a recursor with IH; the recipe is
mutual theorem blocks with constructor pattern matching.

For `density_pos` / `densityProd_pos`:
1. Pattern-match on `mk children` (resp. `[]` / `t :: ts`).
2. `show` the body of `density (mk children)` (resp. the cons-case
   product) literally — i.e. `show 0 < order (mk children) *
   densityProd children`.
3. `exact Nat.mul_pos (...) (...)` with the two recursive calls.

For `symmetry_pos` the cons case branches on `if t ∈ rest`; use
`split_ifs with h` then close each branch separately. The `else`
branch needs three positivity facts combined via `Nat.mul_pos`
twice.

For `alphaWeight_pos`: `unfold alphaWeight` → `div_pos` → `mul_pos`.

## D. What NOT to try

1. **Do NOT pursue `lem:310B` directly.** It needs tree-indexed-sum
   infrastructure (finitary truncation by order, or a custom
   `TruncatedRootedTreeSum` type) that is itself multi-cycle work.
   The cycle 250 task results listed it as a candidate "after auditing
   what infrastructure exists"; the audit is not part of cycle 251.
2. **Do NOT prove the combinatorial equivalence of α(t)** (labelling
   count = closed form). Per `.prover-state/issues/symmetry_group_equivalence.md`,
   this is the same multi-cycle scope as the σ-group equivalence and
   no downstream consumer needs it.
3. **Do NOT use `induction t with | mk children ih`.** It fails on
   nested inductives. Use mutual theorem blocks (per cycles 017, 249,
   250).
4. **Do NOT duplicate `order_pos` in Section301 while leaving it in
   Section323.** Two declarations with the same name in the same
   namespace will conflict at import time. Move, don't copy.
5. **Do NOT add new entities to `extraction/formalization_data/`**.
   These three theorems are derived corollaries, not Butcher
   entities. No `lean_status.json` row change needed.
6. **Do NOT attempt `OpenMath/Chapter4/Section441.lean`** — the GPFS
   compile pathology has now reproduced 43 consecutive times across
   cycles 182–239 (~30 calendar days). Skip per the standing pattern
   in `.prover-state/issues/cycle_182_gpfs_slowness.md`.
7. **Do NOT raise `maxHeartbeats`**. These proofs are sub-second; if
   any of them stalls, the issue is the proof shape, not the limit.
8. **Do NOT introduce `axiom` or `sorry`**. Cycles 149 / 200 / 201
   established the rollback precedent for sorry-first scaffolds. Ship
   axiom-clean or skip.
9. **Do NOT edit `scripts/autonomous_loop.py`** for the tautology
   scanner false-positive issue. Loop-maintainer territory per
   `.prover-state/issues/tautology_scanner_false_positives.md`.
10. **Do NOT rename `h_*` hypotheses cosmetically** unless the
    tautology scanner explicitly flags them. None of the proofs
    above use `:= h_*` / `exact h_*` patterns, so the scanner should
    stay silent.

## E. Verification protocol

After each landing:

1. `lake env lean OpenMath/Chapter3/Section301.lean` — clean exit.
2. `lake env lean OpenMath/Chapter3/Section323.lean` — clean exit
   (verifies the `order_pos` move didn't break downstream consumers).
3. `lake env lean OpenMath/Chapter3.lean` — full chapter aggregator.
4. `grep -c sorry OpenMath/Chapter3/Section301.lean` → 0.
5. `grep -c sorry OpenMath/Chapter3/Section323.lean` → 0.
6. `#print axioms` on each of the four new theorems
   (`order_pos` after move, `density_pos`, `symmetry_pos`,
   `alphaWeight_pos`) — must return only
   `[propext, Classical.choice, Quot.sound]`.
7. Tautology-scanner regex sweep:
   `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/Chapter3/Section301.lean`
   — must return 0 hits.

If step 2 fails: revisit whether `order_pos`'s namespace open/close
markers were preserved correctly when deleting from Section323. Read
Section323.lean line 51–60 carefully before deleting to confirm
exactly what bracketing belongs to `order_pos` versus what belongs to
later theorems.

## F. Risk register and abort thresholds

| Risk | Mitigation | Abort threshold |
|---|---|---|
| `Nat.pos_pow_of_pos` namespace drift in Mathlib | Fall back to generic `pow_pos` | If `lean_local_search` finds neither, case-split on `full.count t = 0 ∨ 0 < full.count t` and close trivially in each branch |
| `densityProd`/`symmetryProd` unfold mismatches | Use `show` with the literal definitional body | If `show` fails, `unfold density` / `unfold symmetry` instead |
| `split_ifs` produces unexpected hypothesis names | Use `by_cases h : t ∈ rest; · ...; · ...` as fallback | None — both forms work in current Mathlib |
| `order_pos` move triggers a downstream cascade | Section323 only uses `order_pos` internally; verify with step E.2 | If a third file imports it (verify via `grep -r "order_pos" OpenMath/`), leave a 1-line `export` alias in Section323 |
| `exact_mod_cast` fails on `Nat.factorial_pos` | Use `Nat.cast_pos.mpr (Nat.factorial_pos _)` explicitly | None |

**Hard abort threshold**: if any of B.1–B.4 has not landed
axiom-clean within ~45 minutes of cycle start, fall back to the
plan in §G.

## G. Fallback plan

If the primary plan stalls (e.g. unexpected Mathlib API drift,
namespace conflicts, GPFS slowness propagating to Section301),
ship one of these instead:

1. **Just `order_pos` move + `density_pos`** — drop `symmetry_pos`
   and `alphaWeight_pos`. Still a positive cycle delta (one new
   public theorem, one structural reorganisation).
2. **Compute one new α value matching Butcher Table 310(II)** —
   e.g. `alphaWeight (mk [cherry]) = ?` (r=3 tree with one
   non-trivial subtree). Mechanical via `unfold + rw + norm_num`,
   following cycle 250's witness template at line 280.
3. **Compute `internalWeight` of `explicitEuler`** on a small set of
   trees — option (4) from cycle 250's suggested next approach.
   Tests §312's elementary-weight machinery on `cherry` / `broom₃`.

Each fallback is ≤ 20 LOC and axiom-clean by construction.

## H. Scope boundary

Cycle 251 ships **positivity infrastructure for α(t)** — no new
entities, no new textbook content, no new sorries. The next planner
cycle (252+) can pivot to lem:310B groundwork (tree-indexed sum
truncation, B-series Taylor) or to a fresh entity, with the
positivity API now in hand.
