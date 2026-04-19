# Strategy — Cycle 126

## Situation
- **0 sorry** project-wide.
- All compilation errors from cycle 125 are fixed (OrderStars.lean).
- Aristotle project `8a9315e1` (odd-angle order-star lemmas) is IN_PROGRESS at 9% — proofs are already in-tree manually, so this is confirmation only. Check status at start, harvest if COMPLETE, but do not wait.
- Aristotle project `a63c1035` (reflect_satisfiesE) is IN_PROGRESS at 37% — already closed in cycle 124, ignore.
- All other recent Aristotle projects are COMPLETE for already-incorporated work.
- Reflected methods (Theorem 343A) fully done: B/C/D/E transfer proved (cycles 121–124).
- Order stars: even-angle + odd-angle arrow theorems proved. Ehle barrier is statement-only (winding number not in Mathlib).
- Rooted tree infrastructure (`OpenMath/RootedTree.lean`): `BTree` with `List`-based children, `order`/`density`/`symmetry`/`beta`/`alpha` defined with examples up to order 4. No B-series or elementary differentials yet.
- plan.md next targets: (1) Theorem 301A rooted trees, (2) Theorem 342C remaining (342j/k/l, blocked on rooted trees), (3) Order star / Ehle barrier setup.

## Priority 1: Extend Rooted Tree Infrastructure (60 min)

Rooted trees are the highest-priority unfinished item in plan.md, and they unblock Theorem 342C implications (342j, 342k, 342l). The current `RootedTree.lean` is 177 lines with basic definitions. Extend it with:

### 1A: Enumerate all trees up to order 5 (15 min)

Add the 9 trees of order 5 (needed for order conditions). The trees are:
```
t5a = [τ⁴]           (all leaves)
t5b = [τ², [τ]]      (two leaves + chain-2)
t5c = [τ, [τ²]]      (leaf + bushy-3)
t5d = [τ, [[τ]]]     (leaf + chain-3)
t5e = [[τ], [τ]]     (two chain-2s)
t5f = [[τ³]]         (bushy-4 grafted)
t5g = [[τ, [τ]]]     (mixed-4 grafted)
t5h = [[[τ²]]]       (t4c grafted)
t5i = [[[[τ]]]]      (chain-5)
```

Define them, add `native_decide` examples verifying:
- `order`, `density`, `symmetry`, `beta`, `alpha` for each

This is mechanical but establishes the census needed for order-5 conditions.

### 1B: Prove structural theorems about `order` (15 min)

Prove basic properties that connect `BTree` to numerical analysis:
```lean
theorem order_pos (t : BTree) : 0 < t.order

theorem order_node_eq (children : List BTree) :
    (BTree.node children).order = 1 + (children.map BTree.order).sum

theorem density_pos (t : BTree) : 0 < t.density

theorem symmetry_pos (t : BTree) : 0 < t.symmetry

theorem order_dvd_density_mul_symmetry (t : BTree) :
    t.order.factorial = t.beta * t.symmetry
```

Start with `order_pos` (induction on `BTree`, both cases give `Nat.succ_pos`). Then `density_pos` and `symmetry_pos` by mutual induction. The factorial divisibility `order_dvd_density_mul_symmetry` follows from the definition of `beta`.

### 1C: Order condition framework (30 min)

Define the B-series order condition for Runge–Kutta methods (Theorem 301A statement):
```lean
/-- The RK order condition for a rooted tree `t`:
    ∑ᵢ bᵢ · Φᵢ(t) = 1/γ(t), where Φ is the elementary weight. -/
def elementaryWeight (tab : ButcherTableau s) : BTree → Fin s → ℝ
  | .leaf, i => 1
  | .node children, i =>
      children.foldr (fun t acc => (fun j => acc j * ∑ k, tab.A i k * elementaryWeight tab t k)) (fun _ => 1) i

def satisfiesOrderCondition (tab : ButcherTableau s) (t : BTree) : Prop :=
  ∑ i, tab.b i * elementaryWeight tab t i = 1 / t.density
```

Then state (with sorry) the main theorem:
```lean
theorem order_iff_all_trees (tab : ButcherTableau s) (p : ℕ) :
    tab.HasOrderGe p ↔ ∀ t : BTree, t.order ≤ p → satisfiesOrderCondition tab t
```

**Important**: The `elementaryWeight` recursive definition needs careful handling of the `List.foldr` to match Butcher's `Φ` function. The key recurrence is:
```
Φᵢ(τ) = 1
Φᵢ([t₁, ..., tₘ]) = ∑ⱼ aᵢⱼ Φⱼ(t₁) · ... · ∑ⱼ aᵢⱼ Φⱼ(tₘ)
```

Verify the framework by checking that order-1 and order-2 conditions match existing `SatisfiesB` definitions:
```lean
example (tab : ButcherTableau s) (hb : tab.SatisfiesB 1) :
    satisfiesOrderCondition tab .leaf  -- should be ∑ bᵢ = 1

example (tab : ButcherTableau s) (hb : tab.SatisfiesB 2) :
    satisfiesOrderCondition tab t2    -- should be ∑ bᵢ cᵢ = 1/2
```

### Approach
1. Write the full structure with `sorry` at every new theorem.
2. Verify it compiles.
3. Close the mechanical proofs (`order_pos`, `density_pos`, examples).
4. Submit `elementaryWeight` correctness lemmas to Aristotle.
5. Close remaining sorries manually using Lean LSP tools.

## Priority 2: Connect Order Stars to Padé (if time permits, 20 min)

If rooted tree work finishes early, add infrastructure connecting arrow-direction theorems to concrete Padé approximants.

### 2A: Padé error constant

State the error constant for the `(p,q)` Padé approximant:
```lean
theorem pade_error_constant (p q : ℕ) :
    ∃ C K δ₀, C = (-1)^q * (↑(p.factorial * q.factorial) : ℝ) /
      ↑((p + q).factorial * (p + q + 1).factorial) ∧
    0 < K ∧ 0 < δ₀ ∧
    ∀ z : ℂ, ‖z‖ < δ₀ →
      ‖padeR p q z * exp (-z) - (1 - ↑C * z ^ (p + q + 1))‖ ≤ K * ‖z‖ ^ (p + q + 2)
```

This connects `OpenMath/Pade.lean` (which has `pade_approximation_order`) to `OpenMath/OrderStars.lean` (which has arrow-direction theorems). The proof uses the Taylor expansion of `padeR(z)·exp(-z)` around 0.

### 2B: Arrow directions for diagonal Padé

As a corollary, derive:
```lean
theorem pade_diagonal_arrow_up (p : ℕ) (k : ℕ) :
    IsUpArrowDir (padeR p p) (2 * ↑k * π / (2 * ↑p + 1))
```

(For diagonal Padé `(p,p)`, `q = p` so `(-1)^p` determines the sign of `C`.)

## Priority 3: Verify Compilation (throughout)

After every batch of changes, verify with:
```bash
PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/RootedTree.lean
```

If `lake` hangs due to Mathlib git issues:
```bash
rm -rf .lake/packages/mathlib/.git/index.lock 2>/dev/null
PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/RootedTree.lean
```

If project-level verification fails (as in cycle 125), fall back to `lean_run_code` with explicit imports for isolated theorem checking.

## What NOT to try

1. **Do NOT attempt Ehle barrier proof** — requires winding number theory (not in Mathlib). The statement-only version is correct.
2. **Do NOT add new concrete RK method files** — the file count is already large.
3. **Do NOT try `lake build`** — use `lake env lean <file>` for verification.
4. **Do NOT increase `maxHeartbeats`** — decompose instead.
5. **Do NOT work on Theorem 342j/342k/342l directly** — they need the rooted tree framework first. Build the framework this cycle.
6. **Do NOT re-derive any proved results** — 0 sorrys means all existing proofs are done.
7. **Do NOT use `Multiset BTree` for children** — defining inductive types with `Multiset` is problematic in Lean 4. Keep `List BTree` and work with the existing representation. If unordered semantics matter later, define a `Setoid` quotient.
8. **Do NOT spend more than 15 min on Aristotle result harvesting** — projects 8a9315e1 and a63c1035 are for already-proved theorems.

## Recommended execution order

1. Check Aristotle project `8a9315e1` status, harvest if COMPLETE (5 min)
2. Add order-5 tree definitions and `native_decide` examples (15 min)
3. Verify RootedTree.lean compiles (5 min)
4. Prove `order_pos`, `density_pos`, `symmetry_pos` structural lemmas (15 min)
5. Define `elementaryWeight` and `satisfiesOrderCondition` (20 min)
6. State `order_iff_all_trees` with sorry, verify compilation (10 min)
7. Submit elementary weight verification lemmas to Aristotle (5 min)
8. If time: start Padé error constant connection (20 min)
9. Write task result, commit (5 min)

Total: ~100 min. The tree enumeration and structural lemmas are the critical path.

## Verification

```bash
PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/RootedTree.lean
PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/OrderStars.lean
```

## Commit message template

```
cycle 126: extend rooted tree infrastructure (order-5 census + elementary weights)
```

## End-of-Cycle Checklist

- [ ] All modified `.lean` files compile
- [ ] Write `.prover-state/task_results/cycle_126.md`
- [ ] Update `.prover-state/cycle` to `126`
- [ ] Update `.prover-state/history.jsonl` with cycle summary
- [ ] Commit and push all changes
