# Cycle 313 strategy — ship `thm:342C` clause (342m): `B(2s) ∧ C(s) ⇒ E(s,s)` for arbitrary `RKTableau`

## §A. TL;DR

Cycle 312 just shipped `butcherGaussLegendreRK_satisfiesE` — the
specialisation of Butcher's `E(n,n)` simplifying assumption to the
canonical Gauss–Legendre tableau. Its proof was a **purely algebraic
two-step composition** of B(2n) and C(n), and it **never inspected the
specific Gauss–Legendre structure** — only consumed the abstract
`SatisfiesB`/`SatisfiesC` predicates.

**Cycle 313 generalises that proof to arbitrary `RKTableau`**, shipping
Butcher's `thm:342C` clause (342m):

```lean
theorem RKTableau.satisfiesE_of_satisfiesB_satisfiesC {s : ℕ}
    (M : RKTableau s)
    (hB : M.SatisfiesB (2 * s)) (hC : M.SatisfiesC s) :
    M.SatisfiesE s s
```

Cycle 312's worker incorrectly claimed `thm:342C` requires `thm:314A`
elementary-differential infrastructure (multi-cycle). That is wrong:
`thm:342C` has **7 sub-implications**, of which **4 are purely
algebraic** among the B/C/D/E predicates and require **no** elementary-
weight machinery:

* (342j) `G(2s) ⇒ B(2s)` ← needs G = order = elementary differentials
* (342k) `G(2s) ⇒ E(s,s)` ← needs G = order
* (342l) `B(2s) ∧ C(s) ∧ D(s) ⇒ G(2s)` ← needs G = order
* **(342m) `B(2s) ∧ C(s) ⇒ E(s,s)` ← purely algebraic — cycle 313 target**
* (342n) `B(2s) ∧ E(s,s) ⇒ C(s)` ← purely algebraic (non-singular matrix)
* (342o) `B(2s) ∧ D(s) ⇒ E(s,s)` ← purely algebraic — cycle 313 P2 stretch
* (342p) `B(2s) ∧ E(s,s) ⇒ D(s)` ← purely algebraic (non-singular matrix)

Verified by reading `extraction/formalization_data/entities/thm_342C.json`:
`transitive_dependencies = []`.

Plan: ship (342m) as the cycle 313 headline (high-confidence,
~80 LOC mechanical port of cycle 312). Optionally ship (342o) as a
P2 stretch (~80 LOC, analogous algebraic composition using D(s)
instead of C(s)). The G(2s)-involving clauses and the converse
clauses (342n)/(342p) are deferred to future cycles.

## §B. Mandatory pre-flight reading

Read these files **before writing any Lean code**:

1. **`OpenMath/Chapter3/Section321.lean` lines 85–135** — confirm the
   `SatisfiesB`/`SatisfiesC`/`SatisfiesE` definitions verbatim:

   ```lean
   def SatisfiesB {s : ℕ} (M : RKTableau s) (η : ℕ) : Prop :=
     ∀ k : ℕ, 1 ≤ k → k ≤ η →
       (∑ i : Fin s, M.b i * M.c i ^ (k - 1)) = 1 / (k : ℝ)

   def SatisfiesC {s : ℕ} (M : RKTableau s) (ξ : ℕ) : Prop :=
     ∀ i : Fin s, ∀ k : ℕ, 1 ≤ k → k ≤ ξ →
       (∑ j : Fin s, M.A i j * M.c j ^ (k - 1)) = M.c i ^ k / (k : ℝ)

   def SatisfiesE {s : ℕ} (M : RKTableau s) (η ζ : ℕ) : Prop :=
     ∀ k : ℕ, 1 ≤ k → k ≤ η →
     ∀ l : ℕ, 1 ≤ l → l ≤ ζ →
       (∑ i : Fin s, ∑ j : Fin s,
           M.b i * M.c i ^ (k - 1) * M.A i j * M.c j ^ (l - 1))
         = 1 / ((l : ℝ) * ((k : ℝ) + (l : ℝ)))
   ```

2. **`OpenMath/Chapter3/Section342.lean`'s `butcherGaussLegendreRK_satisfiesE`
   proof** (just landed cycle 312, near the bottom of the file). This is the
   **template** for cycle 313. Read its proof body completely. The
   tactic skeleton is:

   ```
   intro k h1 hk l hl1 hl
   have hn : 0 < n := lt_of_lt_of_le hl1 hl
   show (∑ i, ... butcherGaussLegendreRK ...) = ...
   have hC_i := fun i => butcherGaussLegendreRK_satisfiesC n i l hl1 hl
   -- outer rewrite: factor (1/l) out; per-i substitution via hC_i
   have h_outer : (outer LHS) = (1/l) • (∑ i, b_i · c_i^(k+l-1))
   rw [h_outer]
   -- B(2n) at exponent (k+l):
   have hB_kl : (∑ i, b_i · c_i^((k+l)-1)) = 1/(k+l)
     := butcherGaussLegendreRK_satisfiesB n hn (k+l) hkl_lo hkl_hi
   rw [hB_kl]
   -- arithmetic closes
   push_cast; field_simp
   ```

   **Cycle 313's job is to delete the Gauss-Legendre-specific lemma
   calls and replace them with `hC i k hk_ok` / `hB (k+l) hkl_ok` from
   the new hypotheses.** Almost nothing else changes.

3. **`extraction/formalization_data/entities/thm_342C.json`** — confirm
   the textbook statement and `dependencies = []`. Read at minimum
   `statement_text`, `proof_text`, and `dependents`.

4. **`extraction/formalization_data/entities/cor_342D.json`** —
   understand how (342m) feeds into `cor:342D` (along with B(2n)/C(n),
   the partial closure of cor:342D advances one more prong toward
   general RK-method order characterisation).

## §C. Concrete signature and proof recipe — P1 deliverable

Add to `OpenMath/Chapter3/Section321.lean` (NOT Section342 — this is
a generic §321 lemma about the predicates defined there):

```lean
namespace RKTableau

/-- *Butcher §342 Theorem 342C, clause (342m).* `B(2s)` (quadrature
order `2s`) plus `C(s)` (interpolation order `s`) imply `E(s, s)`
(the pair condition for trees `[τ^{k-1} [τ^{l-1}]]` at `k, l ≤ s`).

Pure algebraic two-step composition: per row `i`, use `C(s)` at
exponent `l` to reduce `∑ⱼ A_ij c_j^(l-1) = c_i^l / l`; pull `1/l`
out of the outer `i`-sum and combine powers via `pow_add`; apply
`B(2s)` at exponent `k + l` (legal because `1 ≤ k+l ≤ 2s` from
`1 ≤ k ≤ s` and `1 ≤ l ≤ s`) to reduce `∑ᵢ b_i c_i^(k+l-1) =
1/(k+l)`; close `(1/l) · (1/(k+l)) = 1/(l·(k+l))` by `field_simp`.

No `0 < s` hypothesis required: at `s = 0` the goal quantifies
`∀ k, 1 ≤ k → k ≤ 0`, vacuously true. -/
theorem satisfiesE_of_satisfiesB_satisfiesC {s : ℕ}
    (M : RKTableau s) (hB : M.SatisfiesB (2 * s))
    (hC : M.SatisfiesC s) :
    M.SatisfiesE s s := by
  intro k h1 hk l hl1 hl
  -- ... port cycle 312's _satisfiesE proof body verbatim, replacing
  --     `butcherGaussLegendreRK_satisfiesC n i l hl1 hl`
  --       → `hC i l hl1 hl`
  --     `butcherGaussLegendreRK_satisfiesB n hn (k+l) hkl_lo hkl_hi`
  --       → `hB (k+l) hkl_lo hkl_hi` (no `hn` needed: B(2s) hypothesis
  --                                    is already universally quantified)
  sorry  -- replace with port of cycle 312 proof body
end RKTableau
```

**Critical difference from cycle 312**: there is no `0 < n` derivation
step. Cycle 312 needed `hn : 0 < n` because
`butcherGaussLegendreRK_satisfiesB` *itself* takes `0 < n` as a
hypothesis. Here, `hB` is the abstract predicate `M.SatisfiesB (2*s)`,
which is already universally quantified — no precondition extraction
needed. Just verify `1 ≤ k+l` and `k+l ≤ 2*s` from `hk`/`hl` via
`omega` and invoke `hB`.

### Step-by-step decomposition (mirrors cycle 312 verbatim)

1. `intro k h1 hk l hl1 hl` — unpack the universal SatisfiesE binders.
2. Compute `hkl_lo : 1 ≤ k + l` and `hkl_hi : k + l ≤ 2 * s` via
   `omega` (using `1 ≤ k ≤ s` and `1 ≤ l ≤ s`).
3. Compute `hl_ne : (l : ℝ) ≠ 0` from `hl1 : 1 ≤ l`. Cycle 312 uses
   `exact_mod_cast Nat.one_le_iff_ne_zero.mp hl1` or similar — port verbatim.
4. `have hCi := fun i => hC i l hl1 hl` — per-row C(s) application.
5. Outer-sum rewrite: `have h_outer : (∑ i, ∑ j, M.b i · M.c i^(k-1) · M.A i j · M.c j^(l-1)) = (1/l) • (∑ i, M.b i · M.c i^(k+l-1))`.
   Inside the `have`:
   * `rw [Finset.mul_sum]` to factor `(1/l)` outside.
   * `apply Finset.sum_congr rfl; intro i _`.
   * Per-`i` goal: `∑ j, M.b i · M.c i^(k-1) · M.A i j · M.c j^(l-1)
                     = (1/l) · (M.b i · M.c i^(k+l-1))`.
   * Internal `show ... = M.b i · M.c i^(k-1) · (∑ j, M.A i j · M.c j^(l-1))
                          by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring`
     factors `b_i · c_i^(k-1)` out of the inner `j`-sum.
   * `rw [hCi i]` substitutes `∑ j, M.A i j · M.c j^(l-1) = M.c i^l / l`.
   * Combine `c_i^(k-1) · c_i^l = c_i^(k+l-1)` via `← pow_add` plus
     `Nat.sub_add_cancel h1` to bridge `(k - 1) + l = (k + l) - 1`
     (cycle 312 uses this exact pattern — port directly).
   * `field_simp` closes (NO trailing `ring` — cycle 312 task results
     flagged that `field_simp` already closes; a trailing `ring` triggers
     "No goals to be solved").
6. `rw [h_outer]`.
7. Handle the `(1/l) •` factor — cycle 312 likely uses `smul_eq_mul`
   or pulls the scalar outside via `Finset.smul_sum` rewriting; port directly.
8. `have hB_kl := hB (k+l) hkl_lo hkl_hi`.
9. `rw [hB_kl]`.
10. `push_cast` to lift `((k + l : ℕ) : ℝ) = (k : ℝ) + (l : ℝ)`.
11. `field_simp` closes `(1/l) · (1/(k+l)) = 1/(l · (k+l))`.

**Strategy: literally open `Section342.lean`, find
`butcherGaussLegendreRK_satisfiesE`, copy its body, and apply the
substitutions:**

* `butcherGaussLegendreRK_satisfiesC n i l hl1 hl` → `hC i l hl1 hl`
* `butcherGaussLegendreRK_satisfiesB n hn (k+l) hkl_lo hkl_hi` →
  `hB (k+l) hkl_lo hkl_hi`
* Delete the `have hn : 0 < n := ...` step
* Delete (or generalise) any `show ...` line that unfolds
  `butcherGaussLegendreRK`'s `.A`/`.b`/`.c` projections (the generic
  version stays at the abstract `M.A`/`M.b`/`M.c` form throughout —
  no projection-unfolding `show` should be needed)

That's the entire proof.

### Non-vacuity witnesses

Add two `example`s near the new theorem in `Section321.lean`:

```lean
/-- Non-vacuity at `s = 1`: `gaussLegendre1Stage` satisfies `E(1, 1)`
because it satisfies `B(2)` and `C(1)`. Cites the existing
`Section321.lean:242`/`248` SatisfiesB/SatisfiesC examples. -/
example : gaussLegendre1Stage.SatisfiesE 1 1 := by
  -- Match `(2 * 1)` with `2` for hB via `show` or by inlining;
  -- existing examples provide SatisfiesB 2 / SatisfiesC 1 directly.
  refine gaussLegendre1Stage.satisfiesE_of_satisfiesB_satisfiesC
    (hB := ?_) (hC := ?_)
  · -- gaussLegendre1Stage.SatisfiesB 2  (port existing example body)
    sorry  -- replace with the body from Section321.lean:242
  · -- gaussLegendre1Stage.SatisfiesC 1  (port existing example body)
    sorry  -- replace with the body from Section321.lean:248
```

(If the existing `example` at `Section321.lean:259` already proves
`gaussLegendre1Stage.SatisfiesE 1 1` by hand, leave that one
untouched and add the *abstract-route* version as a fresh
`example` so the regression check is meaningful.)

Plus a parametric regression-check:

```lean
/-- *Regression check.* The general-`n` Gauss-Legendre tableau
satisfies `E(n, n)` via the abstract (342m) lemma, agreeing with
cycle 312's direct `butcherGaussLegendreRK_satisfiesE`. -/
example (n : ℕ) (hn : 0 < n) :
    (butcherGaussLegendreRK n).SatisfiesE n n :=
  (butcherGaussLegendreRK n).satisfiesE_of_satisfiesB_satisfiesC
    (butcherGaussLegendreRK_satisfiesB n hn)
    (butcherGaussLegendreRK_satisfiesC n)
```

Place this *inside* `Section321.lean` if the Gauss-Legendre symbols
are visible there, OR inside `Section342.lean` if they're not (the
cycle 309–311 Gauss-Legendre symbols live in `Section342`).

**Do NOT delete cycle 312's `butcherGaussLegendreRK_satisfiesE`** —
keep it as a regression-witness alongside the abstract lemma.

## §D. P2 stretch — clause (342o): `B(2s) ∧ D(s) ⇒ E(s,s)`

Butcher's prose says "proved in similar way" without spelling it out.
The algebraic derivation, mirroring (342m) but swapping roles:

**Given**: `D(s)` says `∑ᵢ b_i · c_i^(k-1) · A_ij = (b_j/k)(1 - c_j^k)`.
**Goal**: `E(s,s)` says `∑ᵢ ∑ⱼ b_i · c_i^(k-1) · A_ij · c_j^(l-1) = 1/(l(k+l))`.

Algebraic derivation:

1. Sum-swap LHS via `Finset.sum_comm`:
   `LHS = ∑ⱼ (∑ᵢ b_i · c_i^(k-1) · A_ij) · c_j^(l-1)`
   (need to inject the `c_j^(l-1)` factor inside, which is constant in i,
   then swap).
2. Apply D(s) at exponent `k` per `j`:
   `LHS = ∑ⱼ (b_j/k)(1 - c_j^k) · c_j^(l-1)
        = (1/k) (∑ⱼ b_j · c_j^(l-1) - ∑ⱼ b_j · c_j^(k+l-1))`.
3. Apply B(2s) at exponent `l` (`1 ≤ l ≤ s ≤ 2s`):
   `∑ⱼ b_j · c_j^(l-1) = 1/l`.
4. Apply B(2s) at exponent `k+l` (`1 ≤ k+l ≤ 2s`):
   `∑ⱼ b_j · c_j^(k+l-1) = 1/(k+l)`.
5. `LHS = (1/k)(1/l - 1/(k+l)) = (1/k) · k/(l(k+l)) = 1/(l(k+l))`. ✓

Implementation sketch:

```lean
theorem satisfiesE_of_satisfiesB_satisfiesD {s : ℕ}
    (M : RKTableau s) (hB : M.SatisfiesB (2 * s))
    (hD : M.SatisfiesD s) :
    M.SatisfiesE s s := by
  intro k h1 hk l hl1 hl
  have hkl_lo : 1 ≤ k + l := by omega
  have hkl_hi : k + l ≤ 2 * s := by omega
  have hl_2s : l ≤ 2 * s := by omega
  have hl_ne : (l : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hl1
  have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp h1
  have hkl_ne : ((k : ℝ) + (l : ℝ)) ≠ 0 := by positivity
  -- sum-swap: ∑i ∑j = ∑j ∑i, then factor c_j^(l-1) out of inner i-sum
  -- (it's constant in i)
  have h_swap : (∑ i, ∑ j, M.b i * M.c i^(k-1) * M.A i j * M.c j^(l-1))
              = (∑ j, (∑ i, M.b i * M.c i^(k-1) * M.A i j) * M.c j^(l-1)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
  rw [h_swap]
  -- apply D(s) per j
  have hDj := fun j => hD j k h1 hk
  -- replace each inner i-sum with (b_j/k)(1 - c_j^k)
  -- ... etc
  sorry
```

Expected LOC: ~90, similar to (342m). Ship only if P1 (342m) closes
in <100 LOC and there's budget remaining. **Do NOT block on (342o)**
— it is a stretch deliverable.

## §E. What NOT to try

### Forbidden approaches

* **Do NOT attempt clauses (342j), (342k), (342l)**. These involve
  `G(2s)` = "method has order 2s" which requires the elementary-
  differential framework (Butcher §31x): `RootedTree`, `α(t)`, `F(t)(y₀)`,
  Φ(t)-matching. None of this is currently formalised. Cycle 312's worker
  was correct that *those* clauses need `thm:314A` infrastructure;
  they were wrong only in claiming (342m) needs it.

* **Do NOT attempt clauses (342n), (342p)**. These are the
  "converse" implications `B(2s) ∧ E(s,s) ⇒ C(s)` and
  `B(2s) ∧ E(s,s) ⇒ D(s)`. Butcher's proof argues that the matrix
  multiplier `[b_i c_i^(k-1)]` is non-singular (Vandermonde-style),
  so inverting it recovers `C(s)` / `D(s)` from `E(s,s)` and `B(2s)`.
  This requires `Matrix.det` of a `b`-weighted Vandermonde matrix to
  be nonzero — tractable but its own cycle.

* **Do NOT attempt `cor:342D` headline closure**. The full iff
  `RK order 2s ⇔ Gauss-Legendre collocation` requires `thm:342C`
  (only one prong shipped this cycle) + `thm:314A` (multi-cycle). Just
  ship (342m) and let the planner pivot.

* **Do NOT add a `(hs : 0 < s)` hypothesis**. The cycle 310–312
  pattern is: B(2n)/`_satisfiesB` takes `0 < n` only because the
  underlying weight-positivity proof needs it; C/D/E predicates and
  the abstract clauses don't. At `s = 0`, `SatisfiesE 0 0` is
  vacuous (no `k` satisfies `1 ≤ k ≤ 0`), so the conclusion holds
  with no hypotheses needed. The `intro k h1 hk` step at `s = 0`
  produces `1 ≤ k ∧ k ≤ 0`, which `omega` closes by deriving False.

### Dead-end tactics flagged by recent cycles

* **`ring` after `field_simp`** — cycle 312 task results flagged this:
  `field_simp` already closes the final field identity, so a trailing
  `ring` triggers Lean's "No goals to be solved" error. Use one or the
  other.

* **`simp [butcherGaussLegendreRK]; ring` directly on the goal** — too
  aggressive; blows past 200000 heartbeats. Use the `show ... by rw + ring`
  pattern from cycle 312 for inner-sum factoring.

* **Skipping the `hl_ne : (l : ℝ) ≠ 0` derivation** — `field_simp`
  needs it explicitly when dividing by `l`. Derive it eagerly from
  `hl1 : 1 ≤ l`.

### Infrastructure-cycle traps

* **Do NOT write a "scoping doc" for thm:342C as the cycle 313
  primary deliverable**. Cycle 312's worker recommended this, but
  inspection of `thm_342C.json` reveals (342m) is a clean single-cycle
  Lean target — no multi-phase plan needed. Just ship it. (If P2
  (342o) also closes, the remaining clauses can be enumerated in a
  short paragraph appended to `lean_status.json`'s cycle-313 note;
  no separate `.md` file needed.)

* **Do NOT pivot to a fresh entity** (e.g. `thm:352A` Padé
  approximations, or §35x stability). The §342 momentum is preserved
  by shipping (342m), and the abstract (342m) is genuinely useful
  for downstream §342/§344/§35x consumers.

## §F. Faithfulness check requirements

Before commit:

* Read `extraction/formalization_data/entities/thm_342C.json` and
  quote `(342m)` verbatim in the new theorem's docstring.
* The Lean theorem's hypothesis pack must be exactly
  `M.SatisfiesB (2 * s) ∧ M.SatisfiesC s` — no extra hypotheses, no
  weaker hypotheses. (Butcher's statement is `B(2s) ∧ C(s) ⇒ E(s,s)`
  flat; we ship the implication form with the same hypothesis names.)
* The Lean conclusion `M.SatisfiesE s s` matches the textbook `E(s,s)`.
  The Section321 definitions audit (cycle 306) already verified the
  three predicates correctly encode Butcher's §321 (321a)/(321b)/(321c)
  equations — no faithfulness divergence introduced here.
* Tautology scan: the conclusion `M.SatisfiesE s s` does NOT appear
  among the hypotheses (which are `M.SatisfiesB (2*s)` and
  `M.SatisfiesC s` — distinct predicates). Genuine algebraic content.
* Identity scan: the proof is structural (multiple `rw`s + per-row
  `Finset.sum_congr` rewriting); NOT a single `:= h_*` or `:= id`.
* Hypothesis strength: cannot weaken to `SatisfiesB s` (need 2s for
  the `k+l ≤ 2s` step) or `SatisfiesC` at lower index (need exponent
  up to s). Match Butcher exactly.

## §G. Verification protocol

After landing the new theorem:

1. `lake env lean OpenMath/Chapter3/Section321.lean` — exit 0
2. `lake env lean OpenMath/Chapter3.lean` — exit 0 (aggregator)
3. `grep -c sorry OpenMath/Chapter3/Section321.lean` — 0
4. `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/Chapter3/Section321.lean`
   — zero hits (tautology-scanner safe)
5. `lean_verify
    OpenMath.Chapter3.Section321.RKTableau.satisfiesE_of_satisfiesB_satisfiesC`
   — axiom set should be `[propext, Classical.choice, Quot.sound]`
   (no `sorryAx`)
6. Cycle 312's `butcherGaussLegendreRK_satisfiesE` should remain
   axiom-clean and unchanged; verify no regression.

## §H. Housekeeping at end of cycle

* `extraction/formalization_data/lean_status.json`: update `thm:342C`
  row to `partial` with `lean_symbol = "satisfiesE_of_satisfiesB_satisfiesC"`
  and a note explaining that clauses (342m) and (any stretch) are
  shipped, while (342j)/(342k)/(342l) await elementary-differential
  infrastructure and (342n)/(342p) await the non-singular-matrix
  argument.
* `plan.md`: bump `thm:342C` row from `[ ]` to `[~]` with a cycle 313
  cumulative note (single line, ~150 chars) capturing the clauses
  shipped.
* Cycle 312's `cor:342D` row: add a one-line cycle-313 update noting
  that the (342m) generalisation means we now have *generic* (B+C → E)
  evidence applicable to any RKTableau, not just butcherGaussLegendreRK.

## §I. Optional P3 — a tiny scoping note (within lean_status.json)

If both (342m) and (342o) ship cleanly, write a short scoping note
**inside `lean_status.json`'s cycle 313 entry** (not a separate
file) enumerating the remaining `thm:342C` work:

* (342n)/(342p) [converses]: ~150 LOC each, need Vandermonde-style
  non-singular-matrix argument. Could ship in cycles 314-315.
* (342j)/(342k)/(342l) [G(2s) clauses]: blocked on `thm:314A`
  (multi-cycle) per `lem_310B_plan.md` Phase D infrastructure.

Don't create a separate `thm_342C_plan.md` file. The remaining work
is shallow enough that a paragraph in `lean_status.json` suffices.

## §J. Cycle 313 success criteria

Cycle 313 ships clean if:

1. `RKTableau.satisfiesE_of_satisfiesB_satisfiesC` lands axiom-clean
   in `OpenMath/Chapter3/Section321.lean`.
2. At least one non-vacuity `example` (preferably both — the
   `gaussLegendre1Stage` abstract-route witness AND the parametric
   `butcherGaussLegendreRK n` regression check) closes cleanly.
3. Sorry count remains 0 across the file and the chapter aggregator.
4. `lean_status.json` and `plan.md` are updated.

P2 stretch (342o) is a bonus, not a requirement. Failing P2 should
not abort the cycle; ship P1 in isolation if P2 stalls.

## §K. Bailout plan

If the P1 port stalls (e.g. unexpected Lean elaboration issue with
the abstract `M.A`/`M.b`/`M.c` projections versus
`butcherGaussLegendreRK`'s concrete projections):

1. **First fallback**: try `show ∑ i, ∑ j, M.b i * M.c i^(k-1) * M.A i j * M.c j^(l-1) = ...`
   at the very top of the proof body to force Lean to use the
   explicit `Finset.sum` form before any `rw` fires. This matches
   cycle 312's pattern of using `show` to unfold definitional
   equalities deterministically.
2. **Second fallback**: split the proof into two private lemmas — one
   for the per-`i` factorisation (`per_row_lemma`) and one for the
   outer `(1/l) · (1/(k+l)) = 1/(l(k+l))` arithmetic. The cycle 312
   recipe lives inside a single `theorem` body, but a 2-lemma split
   reduces single-step heartbeat load.
3. **Third fallback**: if all else fails, ship a scoping doc in
   `.prover-state/issues/thm_342C_plan.md` documenting the algebra
   in full and the obstacle. Cycle 314 then ships (342m) with the
   obstacle pre-resolved. This is the rollback path matching cycle
   149/200's precedent.

Do NOT introduce sorries. Do NOT introduce `axiom`/`constant`. Do
NOT raise `maxHeartbeats` above 200000.
