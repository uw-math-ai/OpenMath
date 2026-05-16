# Cycle 312 Strategy — §342 Phase 3.3: `E(n,n)` for the Gauss–Legendre `RKTableau`

## §A — Target

Ship `butcherGaussLegendreRK_satisfiesE` (fourth prong of `cor:342D`)
for the canonical Gauss–Legendre `RKTableau`, completing the
B/C/D/E quadrature characterisation. This is **NOT** an IBP repeat
of cycle 311's D(n) recipe — E(n,n) reduces to a mechanical
two-step algebraic composition of cycle 309's B(2n) and cycle 310's
C(n).

Cycle 311 closed D(n); cycle 312 closes E(n,n); after this, the
canonical Gauss–Legendre tableau provably satisfies all four §321
simplifying assumptions B(2n) / C(n) / D(n) / E(n,n) for general
`n`. The full `cor:342D` iff statement still requires `thm:342C` +
`thm:314A` infrastructure (multi-cycle, out of scope).

## §B — Why E(n,n) is single-cycle

Cycle 311's task results §"Suggested next approach" calls E(n,n)
"a plausible 2-cycle target", but the actual proof reduces to a
two-step composition of B(2n) and C(n) — not an IBP repeat. The
key observation: for the canonical Gauss–Legendre tableau, the
inner sum `∑ⱼ aᵢⱼ · cⱼ^(l-1)` is *exactly* C(n)'s LHS at `k := l`,
so it evaluates to `cᵢ^l / l`. The outer sum then becomes B(2n)'s
LHS at the combined exponent `k+l`.

Mathematical sketch:

```
∑ᵢ ∑ⱼ bᵢ · cᵢ^(k-1) · aᵢⱼ · cⱼ^(l-1)
  = ∑ᵢ bᵢ · cᵢ^(k-1) · (∑ⱼ aᵢⱼ · cⱼ^(l-1))   [factor out i-only term]
  = ∑ᵢ bᵢ · cᵢ^(k-1) · (cᵢ^l / l)             [by C(n) at k := l, l ≤ n]
  = (1/l) · ∑ᵢ bᵢ · cᵢ^(k+l-1)                [pull 1/l out, combine powers]
  = (1/l) · (1 / (k+l))                        [by B(2n) at k+l, 1 ≤ k+l ≤ 2n]
  = 1 / (l · (k+l))                            [arithmetic]
```

Two `rw` invocations + arithmetic close. Estimated 40–80 LOC for
the headline + non-vacuity witnesses.

## §C — Pre-flight verification (MANDATORY, 10 minutes upfront)

Before writing any proof, **verify these three signatures** via
`lean_hover_info` (or `lean_file_outline` on
`OpenMath/Chapter3/Section321.lean`):

1. **`SatisfiesE p q` exact field shape.** Possible forms:
   - `∀ k, 1 ≤ k → k ≤ p, ∀ l, 1 ≤ l → l ≤ q, ∑ᵢⱼ bᵢ · cᵢ^(k-1) · aᵢⱼ · cⱼ^(l-1) = 1/(l·(k+l))`
   - or with `Fin p`, `Fin q` binders.
   - The RHS denominator may be `l·(k+l)` or `k·(k+l)` or
     `(k+l)·l` — verify which.
   - There may or may not be a `0 < p ∨ 0 < q` precondition.

2. **`SatisfiesB k` and `SatisfiesC k` cycle 309/310 signatures.**
   Confirm:
   - `butcherGaussLegendreRK_satisfiesB n hn` expects
     `(hn : 0 < n)` — derive inside E(n,n) proof from
     `k : Fin n` or `l : Fin n` via
     `lt_of_le_of_lt (Nat.zero_le _) (k.lt_of_lt …)`.
   - `butcherGaussLegendreRK_satisfiesC n` does *not* need
     `0 < n` (cycle 310 confirmed this).
   - The exact predicate signature (e.g. `∀ k, 1 ≤ k → k ≤ p,
     ∀ i, ∑ⱼ aᵢⱼ · cⱼ^(k-1) = cᵢ^k / k` for SatisfiesC).

3. **Cycle 308's coincidence theorem name and signature.** The
   `gaussLegendre1Stage.SatisfiesE 1 1` round-trip witness will
   need
   `butcherGaussLegendreRK_one_eq_gaussLegendre1Stage`.

If the SatisfiesE field shape is significantly different from
the sketch above (e.g., uses `Fin` binders with a different
denominator), adapt the proof recipe in §D accordingly. **Do
NOT skip this step.**

## §D — Concrete Lean recipe

After signature verification:

```lean
theorem butcherGaussLegendreRK_satisfiesE (n : ℕ) :
    (butcherGaussLegendreRK n).SatisfiesE n n := by
  intro k l hk_lo hk_hi hl_lo hl_hi  -- adapt to actual predicate
  -- Step 0: derive 0 < n from l (or k).
  have hn : 0 < n := lt_of_lt_of_le hl_lo hl_hi
  -- Step 1: rewrite the inner sum via SatisfiesC.
  -- Outer is ∑ᵢ bᵢ · cᵢ^(k-1) · (∑ⱼ aᵢⱼ · cⱼ^(l-1)).
  -- Use Finset.sum_congr to replace inner with cᵢ^l / l (via C(n)).
  conv_lhs =>
    rw [show (∑ i j, _) = ∑ i, _ from ?_]
    -- ... details, see §"Sub-step details" below
  sorry
```

### Sub-step details

After the `intro` block, the goal looks roughly like:

```
∑ i : Fin n, ∑ j : Fin n,
  (butcherGaussLegendreRK n).b i
    * ((butcherGaussLegendreRK n).c i) ^ (k - 1)
    * (butcherGaussLegendreRK n).A i j
    * ((butcherGaussLegendreRK n).c j) ^ (l - 1)
  = 1 / (↑l * (↑k + ↑l))   -- or however the RHS reads
```

**Step 1 — factor i-only out of the inner sum.** Use
`Finset.mul_sum` (read direction: `c · ∑ f = ∑ c · f` becomes
`∑ c · f = c · ∑ f`):

```lean
have hfactor : ∀ i,
    (∑ j, (b i) * (c i)^(k-1) * (A i j) * (c j)^(l-1))
    = (b i) * (c i)^(k-1) * (∑ j, (A i j) * (c j)^(l-1)) := by
  intro i
  rw [← Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring
```

(Use the qualified field names from the actual goal; this is
schematic.)

**Step 2 — apply C(n) to the inner sum.** Cycle 310's
`butcherGaussLegendreRK_satisfiesC n` evaluated at the index
`l` (using `hl_lo : 1 ≤ l` and `hl_hi : l ≤ n`) gives:

```lean
have hC : ∀ i, (∑ j, (A i j) * (c j)^(l-1)) = (c i)^l / l :=
  butcherGaussLegendreRK_satisfiesC n l hl_lo hl_hi
```

Substitute this into the outer sum.

**Step 3 — pull `(1/l)` out and combine powers.** After
substitution, the outer sum is

```
∑ i, (b i) * (c i)^(k-1) * ((c i)^l / l)
  = (1/l) * ∑ i, (b i) * (c i)^(k+l-1)
```

via `Finset.mul_sum`, `pow_add`, and the identity
`(k-1) + l = k+l-1` (for `1 ≤ k`). The `Nat`-subtraction
identity `(k-1) + l = k+l-1` needs `omega` (works since
`k ≥ 1`).

**Step 4 — apply B(2n) to the outer power-sum.** Cycle 309's
`butcherGaussLegendreRK_satisfiesB n hn` evaluated at `k+l`
(with bounds `1 ≤ k+l` from `hk_lo + hl_lo` and `k+l ≤ 2n`
from `hk_hi + hl_hi`) gives:

```lean
have hB : ∑ i, (b i) * (c i)^(k+l-1) = 1 / (k+l) := by
  have h1 : 1 ≤ k + l := by linarith
  have h2 : k + l ≤ 2 * n := by linarith
  exact butcherGaussLegendreRK_satisfiesB n hn (k+l) h1 h2
```

**Step 5 — close `(1/l) · (1/(k+l)) = 1/(l·(k+l))`.** Plain
`field_simp; ring` should suffice. If not, decompose into a
private helper.

## §E — Non-vacuity witnesses

Two examples, mirroring cycle 311's structure:

```lean
example : (butcherGaussLegendreRK 2).SatisfiesE 2 2 :=
  butcherGaussLegendreRK_satisfiesE 2

example : gaussLegendre1Stage.SatisfiesE 1 1 := by
  rw [← butcherGaussLegendreRK_one_eq_gaussLegendre1Stage]
  exact butcherGaussLegendreRK_satisfiesE 1
```

## §F — Step-by-step procedure

1. **(5 min) Pre-flight signature verification** (§C above).
   `lean_hover_info` on `SatisfiesE`, `SatisfiesB`, `SatisfiesC`
   in `OpenMath/Chapter3/Section321.lean`.

2. **(45 min) Write the headline proof** per §D.
   - Locate the right place to insert in `Section342.lean`
     (after cycle 311's D(n) deliverables).
   - Mirror cycle 310's `satisfiesC` proof structure.
   - Use `Finset.sum_congr` for the inner sum rewrite, then
     `Finset.mul_sum` to factor.

3. **(15 min) Non-vacuity witnesses** per §E.

4. **(10 min) Verification.**
   - `lake env lean OpenMath/Chapter3/Section342.lean` exits 0.
   - `lake env lean OpenMath/Chapter3.lean` exits 0.
   - `grep -c sorry OpenMath/Chapter3/Section342.lean` = 0.
   - `lean_verify` on the headline returns axiom set
     `[propext, sorryAx, Classical.choice, Quot.sound]` — same
     profile as cycles 309/310/311 (the `sorryAx` is the
     pre-existing cycle-301 upstream leak; not a regression).
   - Tautology-scanner clean (no `:= h_*` / `exact h_*` / `:= id`
     patterns).

5. **(10 min) Housekeeping.**
   - `extraction/formalization_data/lean_status.json`: add a
     cycle 312 note on `cor:342D`'s row mentioning E(n,n)
     prong shipped. The full row stays `unformalized` because
     the iff headline is multi-cycle work; this is partial
     evidence.
   - `plan.md`: append a one-line cycle 312 paragraph to
     `cor:342D`'s entry noting the complete B/C/D/E package
     for the canonical Gauss–Legendre tableau.
   - `task_results/cycle_312.md`: full deliverable record per
     CLAUDE.md format.

## §G — What NOT to try

- **Do NOT attempt `thm:342C`** (RK order 2s ⇔ B(2s) ∧ C(s) ∧
  D(s)). Its forward direction requires `thm:314A` (independence
  of elementary differentials), which is currently unformalized
  and multi-cycle prerequisite work. Cycle 311's task results
  explicitly defer this.
- **Do NOT attempt the `cor:342D` iff statement itself.** Same
  reason — requires `thm:342C` + `thm:314A`. Out of scope.
- **Do NOT use cycle 311's IBP recipe.** E(n,n) is *not* an
  integration-by-parts theorem. The proof is purely algebraic
  composition of cycle 309/310's already-shipped results. No
  `poly_ibp`, no antiderivative, no FTC.
- **Do NOT submit to Aristotle.** E(n,n) is a structural
  composition, not a premise-search problem. Cycle 282's (342f)
  Aristotle stalls (12% → 20% across three observations) and
  the cycle 285 resubmission stall (11% → 20% across three more)
  document that Aristotle does not handle structural §342 proofs
  well. Manual closure is fast and reliable here.
- **Do NOT skip the pre-flight signature verification (§C).**
  The proof recipe in §D assumes specific predicate shapes; if
  Section321's `SatisfiesE` uses different binders (e.g.,
  `Fin p` instead of `1 ≤ k ∧ k ≤ p`) or a different RHS
  denominator (e.g., `k·(k+l)` instead of `l·(k+l)`), the
  arithmetic close in Step 5 will fail with a confusing error.
  Verify upfront.
- **Do NOT introduce `axiom`, `constant`, or new sorries.**
  Sorry count must remain 0. The pre-existing `sorryAx` leak
  from cycle 301's `_rootsInIoo_card_ge` is fine — it's upstream
  and not a cycle 312 issue.
- **Do NOT raise `maxHeartbeats` above 200000.** If
  `field_simp + ring` is slow on the final closure, extract a
  private arithmetic helper lemma `private lemma cycle312_arith :
  ∀ (l k : ℕ), 0 < l → 0 < k+l → (1 : ℝ) / l * (1 / (k+l)) = 1 /
  (l * (k+l)) := by intros; field_simp` and apply it.
- **Do NOT attempt to compile
  `OpenMath/Chapter4/Section441.lean`.** Per
  `cycle_182_gpfs_slowness.md`: 43+ consecutive GPFS timeouts
  since cycle 182. Skip §441 entirely.
- **Do NOT pivot to a fresh entity** unless E(n,n) genuinely
  proves intractable (see §I fallback). The cycle 311 → cycle
  312 path is a clean two-cycle completion of the §342 ↔ §321
  bridge; abandoning it leaves the package half-finished.
- **Do NOT modify cycle 309's `butcherGaussLegendreRK_satisfiesB`
  or cycle 310's `butcherGaussLegendreRK_satisfiesC`.** They
  are axiom-clean and load-bearing. The E(n,n) proof should
  consume them as-is via direct invocation.

## §H — Faithfulness check requirements

For the new `butcherGaussLegendreRK_satisfiesE` theorem:

- **Entity ID**: `cor:342D` partial (fourth prong only).
  The full `cor:342D` is the iff "RK order 2s ⇔ collocation at
  shifted Legendre zeros". This cycle ships *evidence* (the
  E(n,n) prong) that the canonical Gauss–Legendre tableau
  satisfies one of the §321 simplifying assumptions implied
  by the iff's RHS. Document explicitly in the theorem
  docstring.
- **Quote the textbook statement** from
  `extraction/formalization_data/entities/cor_342D.json` and
  confirm Section321's `SatisfiesE` predicate captures it
  faithfully. The predicate shape (cycle 306) was already
  audited; the cycle 312 proof should not introduce any new
  divergence.
- **No `0 < n` precondition on the signature** (matching cycle
  310's `_satisfiesC` and cycle 311's `_satisfiesD`). Derive
  `0 < n` inside the proof from `k : Fin n` (or the analogous
  binder).
- **Tautology check**: the conclusion `1 / (l · (k+l))` does
  NOT appear verbatim among hypotheses — it's an arithmetic
  consequence of B(2n) at `k+l` plus C(n) at `l`. Genuine
  theorem, not a re-export of a hypothesis.
- **Hypothesis strength check**: the proof uses exactly
  `(butcherGaussLegendreRK n).satisfiesB n hn` and
  `(butcherGaussLegendreRK n).satisfiesC n` (no extra
  hypotheses), matching the §321/§342 textbook
  derivation. Document this in the theorem docstring.

## §I — Fallback if E(n,n) stalls

If pre-flight verification (§C) reveals a SatisfiesE shape
that doesn't decompose cleanly via the §D recipe, or if the
proof body exceeds the 90-minute budget:

1. **Ship partial E(n,n) at fixed small n.** Concrete
   instances `(butcherGaussLegendreRK 1).SatisfiesE 1 1` and
   `(butcherGaussLegendreRK 2).SatisfiesE 2 2` shipped via
   direct unfolding without the general proof. ~30 LOC each.
   Then defer the general proof to cycle 313.

2. **Ship a `_satisfiesE` helper lemma** that captures only
   the C(n) substitution step:
   ```
   ∑ⱼ (butcherGaussLegendreRK n).A i j * (c j)^(l-1)
     = (c i)^l / l    for 1 ≤ l ≤ n
   ```
   abstracted from the inner sum. This is essentially a
   re-export of `satisfiesC` with the index renamed; useful
   as a stepping stone. ~20 LOC.

3. **Pivot to E(n,n) Phase A** (build a polynomial
   `∑ⱼ A i j · X^(l-1)` antiderivative-style helper) and
   defer the full headline to cycle 313. This is the
   IBP-style fallback the strategy-of-strategy from cycle
   311 anticipates.

4. **Last-resort pivot**: ship one of the small auxiliary
   theorems flagged in cycle 311's outlook (e.g. polishing
   the cycle 308 coincidence theorem, or extracting a public
   `_collocationA_satisfies_C_n_helper` lemma that cycle
   310's `satisfiesC` consumes internally). This keeps the
   cycle non-empty.

If E(n,n) genuinely needs IBP machinery (e.g., the predicate
involves a `cⱼ^(l-1)` factor that doesn't reduce to C(n)'s
shape directly), document the divergence in a new issue file
`.prover-state/issues/satisfiesE_predicate_shape.md` and treat
cycle 312 as a scoping cycle for cycle 313+.

## §J — Cycle budget

- **90 minutes total.** The pre-flight verification is 5 min;
  the proof body is the bulk (45 min); non-vacuity is 15 min;
  verification and housekeeping is 25 min combined.
- **LOC budget**: ~80 LOC for the headline + two non-vacuity
  examples + possibly one private arithmetic helper. Aggressive
  but achievable given the proof's algebraic simplicity.

## §K — Cross-references

- **Cycle 311 task results**: `task_results/cycle_311.md` —
  recommended E(n,n) as cycle 312 target; flagged the
  "B(2n) + C(n) ⇒ E(n,n)" composition as plausible.
- **Cycle 310 C(n)**: `OpenMath/Chapter3/Section342.lean`
  `butcherGaussLegendreRK_satisfiesC` — consumed in Step 2 of
  the recipe. Template for proof structure (intro + sum_congr
  + arithmetic).
- **Cycle 309 B(2n)**:
  `butcherGaussLegendreRK_satisfiesB` — consumed in Step 4 of
  the recipe.
- **Cycle 306 predicates**: `OpenMath/Chapter3/Section321.lean`
  — `SatisfiesB`, `SatisfiesC`, `SatisfiesD`, `SatisfiesE`
  definitions. **Verify SatisfiesE shape via `lean_hover_info`
  in §C BEFORE writing the proof.**
- **Cycle 308 coincidence theorem**:
  `butcherGaussLegendreRK_one_eq_gaussLegendre1Stage` —
  consumed in the `n = 1` round-trip non-vacuity witness.
- **Memory `feedback_heterogeneous_matrix_algebra.md`** —
  relevant if matrix-vector manipulations arise (likely not,
  since E(n,n) works in sum form). Useful to know exists.
- **Memory `feedback_finset_sum_le_sum_nbij_nonexistent.md`** —
  reminder that `Finset.sum_le_sum_nbij'` does not exist; use
  alternatives.

## §L — Status target after this cycle

- **`cor:342D` row in `lean_status.json`**: still
  `unformalized` overall (iff not shipped), but cycle 312
  note documents that all four prongs (B/C/D/E) for the
  canonical Gauss–Legendre tableau are shipped axiom-clean.
- **`plan.md` `cor:342D` row**: still `[ ]`, but cycle history
  notes the complete B/C/D/E package.
- **Sorry count**: 0 (unchanged).
- **Section342.lean**: grows roughly +80 LOC (E(n,n) theorem
  + two non-vacuity witnesses + possibly one private helper).
- **Axiom profile**: same `[propext, sorryAx, Classical.choice,
  Quot.sound]` as cycles 308–311 (the `sorryAx` is the
  pre-existing cycle-301 leak).

## §M — Out-of-scope pivots (DO NOT pursue this cycle)

These are valid future targets but explicitly excluded from
cycle 312:

- `thm:314A` (independence of elementary differentials) —
  needed for `cor:342D` iff, but multi-cycle scope.
- `thm:342C` (RK order 2s ⇔ B(2s) ∧ C(s) ∧ D(s)) — needs
  `thm:314A` first.
- §314A elementary-weight infrastructure broadly.
- `sorryAx` cleanup of cycle 301's `_rootsInIoo_card_ge` —
  pre-existing leak, doesn't affect cycle 312, defer to a
  dedicated cleanup cycle.
- Phase A polynomial-antiderivative-style helpers for E(n,n)
  (only relevant in §I fallback).
- Any §441 work (GPFS-blocked, 43+ consecutive timeouts).

The right pivots for cycle 313+ (if cycle 312 ships cleanly):
either start `thm:314A` infrastructure scoping, or pivot to a
fresh chapter entity per `lem_310B_plan.md` §8 (e.g.
`lem:342A` is closed; consider `lem:312B`, `lem:313A`, or a
§3 §35x stability target).
