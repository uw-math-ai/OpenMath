# Cycle 308 Strategy

## Context

Cycle 307 closed the §342 ↔ §321 algebraic bridge
(`butcherShiftedLegendre_quadratureWeights_satisfiesB`). Per cycle 307
task results §"Suggested next approach", the natural continuation is to
**define the full Gauss–Legendre `RKTableau`** so that the bridge can
be lifted to `(butcherGaussLegendreRK n).SatisfiesB (2 * n)` on a
genuine `RKTableau` (Butcher §342 / §321). That is multi-cycle work
(estimated 3–4 cycles); cycle 308 ships **Phase 1 of 3**: the
collocation `A`-matrix definition + a concrete `n = 1` witness +
the assembled `RKTableau` struct at `n = 1`.

The deliverables are scoped so cycle 308 ships axiom-clean and zero
sorries even if Phase 2/3 stretch goals slip. The §342/§321 chains and
the §310/§311 `lem:310B` plan all stay open as fallback pivots.

## Primary deliverable (P1, mandatory)

**Define the collocation `A`-matrix at the canonical Gauss–Legendre
nodes**, in `OpenMath/Chapter3/Section342.lean`, immediately after
cycle 307's `butcherShiftedLegendre_quadratureWeights_satisfiesB`
(line 6745, before `end OpenMath.Chapter3.Section342` at line 6806).

### Symbol

```lean
/-- **Collocation A-matrix** at the canonical zeros of
`butcherShiftedLegendre n` (Butcher §342 collocation method). The
`(i, j)` entry is the integral of the Lagrange basis polynomial `Lⱼ`
over `[0, cᵢ]`:

  `Aᵢⱼ := ∫₀^{cᵢ} Lⱼ(x) dx`,    `Lⱼ` interpolating `δⱼₖ` at `cₖ`.

This is the standard collocation construction: `Yᵢ = y₀ + h Σⱼ Aᵢⱼ
f(Yⱼ)` is exactly the equation that forces the polynomial
interpolating `(cⱼ, f(Yⱼ))` to integrate to `Yᵢ − y₀` over `[0, cᵢ]`.
At `n = 1` it collapses to the implicit-midpoint A-entry `1/2`
(matches §321's `gaussLegendre1Stage` from cycle 306). -/
noncomputable def butcherShiftedLegendre_collocationA
    (n : ℕ) (i j : Fin n) : ℝ :=
  ∫ x in (0 : ℝ)..butcherShiftedLegendre_zeros n i,
    (Lagrange.basis Finset.univ (butcherShiftedLegendre_zeros n) j).eval x
```

This is a one-line variation of cycle 303's
`butcherShiftedLegendre_quadratureWeights` (Section342.lean:6229),
which integrates over `[0, 1]` instead of `[0, cᵢ]`.

### Concrete `n = 1` witness (axiom-clean target)

Worker should grep for an existing `butcherShiftedLegendre_zeros 1`
helper first (`grep -n "zeros 1" OpenMath/Chapter3/Section342.lean`).
The cycle 307 non-vacuity at line 6792 uses
`butcherShiftedLegendre_zeros 1 j ^ (2 - 1)` directly, so the value
`butcherShiftedLegendre_zeros 1 ⟨0, _⟩ = 1/2` may already be
discharged inside that example via `simp`/computation. If a clean
named lemma is needed, factor it out via cycle 273's
`butcherShiftedLegendre_one : P_1^* = C 2 * X - C 1` plus
`butcherShiftedLegendre_zeros_isRoot 1 ⟨0, _⟩` (which says the value
is a root of `P_1^*`):

```lean
-- Helper (only if not already named).
lemma butcherShiftedLegendre_zeros_one_apply :
    butcherShiftedLegendre_zeros 1 ⟨0, by omega⟩ = 1 / 2 := by
  have hroot := butcherShiftedLegendre_zeros_isRoot 1 ⟨0, by omega⟩
  -- `hroot : (butcherShiftedLegendre 1).IsRoot (... ⟨0, _⟩)`
  rw [butcherShiftedLegendre_one] at hroot
  -- Goal: `(C 2 * X - C 1).IsRoot (zeros 1 ⟨0, _⟩)` ⇒ value = 1/2.
  simp [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X] at hroot
  linarith
```

Then the P1 non-vacuity:

```lean
example : butcherShiftedLegendre_collocationA 1 ⟨0, by omega⟩ ⟨0, by omega⟩
    = 1 / 2 := by
  unfold butcherShiftedLegendre_collocationA
  -- Lagrange basis on a singleton is the constant polynomial `1`
  -- (cf. cycle 303's non-vacuity at Section342.lean:6286).
  simp [Lagrange.basis_singleton, Polynomial.eval_one,
        butcherShiftedLegendre_zeros_one_apply]
  -- Goal: `∫ x in 0..(1/2), 1 = 1/2`. Closed by
  -- `intervalIntegral.integral_const : ∫ a..b, c = (b - a) • c`.
  -- After `simp`, may be `(1/2 - 0) * 1 = 1/2` ⇒ `ring` or `norm_num`.
  ring
```

If the final tactic doesn't close, try `norm_num` or
`intervalIntegral.integral_const` rewrite explicitly. Confirm
axiom-clean via `mcp__lean-lsp__lean_verify`.

## Secondary deliverable (P2, recommended)

**Construct the `n = 1` Gauss–Legendre tableau** as an
`RKTableau 1`, in `OpenMath/Chapter3/Section342.lean` after the
collocation matrix def:

```lean
/-- **The 1-stage Gauss–Legendre `RKTableau`** assembled from the
canonical Lagrange weights and zeros of `butcherShiftedLegendre 1`.
At `n = 1` this is the implicit-midpoint method with `c = 1/2`,
`b = 1`, `A = 1/2` — verified to coincide with §321's hand-defined
`gaussLegendre1Stage` (cycle 306). -/
noncomputable def butcherGaussLegendreRK_one :
    OpenMath.Chapter3.Section312.RKTableau 1 where
  A := butcherShiftedLegendre_collocationA 1
  b := butcherShiftedLegendre_quadratureWeights 1
  c := butcherShiftedLegendre_zeros 1
```

Plus a coincidence theorem against §321's hand-defined witness:

```lean
theorem butcherGaussLegendreRK_one_eq_gaussLegendre1Stage :
    butcherGaussLegendreRK_one =
      OpenMath.Chapter3.Section321.gaussLegendre1Stage := by
  -- `RKTableau.mk.injEq` reduces to per-field equalities.
  -- Use `RKTableau.ext` if available; otherwise:
  refine RKTableau.mk.injEq.mpr ⟨?_, ?_, ?_⟩
  · -- A field: funext + per-entry computation via P1 example
    funext i j
    fin_cases i; fin_cases j
    show butcherShiftedLegendre_collocationA 1 _ _ = (1 : ℝ) / 2
    -- direct citation of the P1 example (promoted to a named theorem
    -- if it isn't already)
    sorry  -- worker fills with the named version of P1's example
  · -- b field
    funext i; fin_cases i
    show butcherShiftedLegendre_quadratureWeights 1 _ = 1
    -- cycle 303 non-vacuity at Section342.lean:6284
    sorry  -- worker fills via existing example
  · -- c field
    funext i; fin_cases i
    show butcherShiftedLegendre_zeros 1 _ = 1 / 2
    exact butcherShiftedLegendre_zeros_one_apply
```

Worker should **promote both the P1 collocationA `example` and the
cycle 303 `_quadratureWeights` example to named theorems first**
(rename `example` → `theorem butcherShiftedLegendre_collocationA_one_apply`
and `theorem butcherShiftedLegendre_quadratureWeights_one_apply`)
so the coincidence proof can cite them.

If `RKTableau.mk.injEq` doesn't exist, try `RKTableau.ext`, or fall
back to the manual `cases`/`rfl` pattern.

Then the bridge from cycle 307's algebraic theorem to a
`RKTableau`-level statement at `n = 1`:

```lean
example : butcherGaussLegendreRK_one.SatisfiesB 2 := by
  rw [butcherGaussLegendreRK_one_eq_gaussLegendre1Stage]
  -- Discharge by §321's existing example pattern (lines 242–247).
  intro k h1 hk
  interval_cases k
  · simp [OpenMath.Chapter3.Section321.gaussLegendre1Stage]
  · simp [OpenMath.Chapter3.Section321.gaussLegendre1Stage]
```

## Stretch deliverable (P3, optional — only if P1 + P2 close in <2 hours)

**Generalize to `butcherGaussLegendreRK n`** for arbitrary `n`:

```lean
noncomputable def butcherGaussLegendreRK (n : ℕ) :
    OpenMath.Chapter3.Section312.RKTableau n where
  A := butcherShiftedLegendre_collocationA n
  b := butcherShiftedLegendre_quadratureWeights n
  c := butcherShiftedLegendre_zeros n
```

Plus an unfold-`SatisfiesB`-and-cite-cycle-307 theorem:

```lean
theorem butcherGaussLegendreRK_satisfiesB (n : ℕ) (hn : 0 < n) :
    (butcherGaussLegendreRK n).SatisfiesB (2 * n) := by
  intro k h1 hk
  -- Unfold `SatisfiesB` and `butcherGaussLegendreRK`; the goal
  -- reduces to cycle 307's theorem statement verbatim.
  show (∑ j : Fin n, butcherShiftedLegendre_quadratureWeights n j *
            butcherShiftedLegendre_zeros n j ^ (k - 1)) = 1 / (k : ℝ)
  exact butcherShiftedLegendre_quadratureWeights_satisfiesB n hn k h1 hk
```

This closes the §342 ↔ §321 `B(2n)` half of the lift in full. The
remaining halves (`C(n)`, `D(n)`, `E(n, n)`) are deferred to cycle
309+ — they require an upper-limit-parametrized version of cycle
304's `2n`-degree exactness (collocation form), which is itself a
multi-cycle infrastructure step.

## Approach (concrete recipe)

1. Open the file: `OpenMath/Chapter3/Section342.lean`.
2. Locate cycle 307's bridge theorem at line 6745 (its closing `end`
   for the namespace is at line 6806).
3. **First**: grep for any existing `butcherShiftedLegendre_zeros 1`
   helper. If not present, ship one as a public lemma — cite
   `butcherShiftedLegendre_zeros_isRoot` + cycle 273's
   `butcherShiftedLegendre_one`.
4. Promote the cycle 303 line 6284 `example` for
   `_quadratureWeights 1 = 1` to a named theorem
   (`butcherShiftedLegendre_quadratureWeights_one_apply`) so P2 can
   cite it.
5. Insert the P1 `butcherShiftedLegendre_collocationA` definition
   immediately before the namespace `end` (line 6806).
6. Add a P1 named theorem
   `butcherShiftedLegendre_collocationA_one_apply` (the worked-out
   `n = 1` value `= 1/2`) — make it a theorem, not an `example`, so
   P2 can cite it.
7. Compile-check with `lake env lean OpenMath/Chapter3/Section342.lean`.
   Expected runtime: 1–3 minutes (warm cache).
8. If P1 closes: insert the P2 `butcherGaussLegendreRK_one` def + the
   coincidence theorem. Re-run `lake env lean`.
9. If P2 closes: optionally attempt P3 (generic `n` tableau +
   `B(2n)` corollary).
10. Run `mcp__lean-lsp__lean_verify` on each new public symbol to
    confirm `[propext, Classical.choice, Quot.sound]` only.
11. Commit per CLAUDE.md workflow with a message like
    `Cycle 308 — §342 collocation A-matrix + n=1 Gauss-Legendre RKTableau.`

## What NOT to try

* **Do NOT attempt the general-`n` `C(n)` collocation identity in
  cycle 308.** The `C(ξ)` predicate from cycle 306 is
  `∑ⱼ Aᵢⱼ cⱼ^{k-1} = cᵢ^k / k`; specializing to the collocation
  matrix needs cycle 304's exactness machinery applied at the upper
  limit `cᵢ` (not 1), which means we'd need a generalization of
  `butcherShiftedLegendre_quadrature_exact_lt_n` parameterized by
  the upper limit. That's worth a dedicated cycle 309/310 — do not
  short-cut it inside cycle 308.
* **Do NOT redefine `_quadratureWeights` to share the
  `_collocationA` integral form.** Cycle 303's existing definition
  is `∫₀¹ Lⱼ`, which equals `b_j` directly via the Kronecker-delta
  property. Linking the two via a separate equality lemma is a
  cycle 309+ concern — leave the cycle 303 def untouched.
* **Do NOT attempt to redefine `gaussLegendre1Stage` as
  `butcherGaussLegendreRK 1`.** §321's hand-defined
  `gaussLegendre1Stage` is a separate, standalone witness for
  §321's predicate non-vacuity examples. The coincidence theorem
  `butcherGaussLegendreRK_one_eq_gaussLegendre1Stage` is a *bridge*,
  not a refactor — keep both definitions and prove they're equal.
* **Do NOT raise `maxHeartbeats`.** The non-vacuity at `n = 1`
  closes by `intervalIntegral.integral_const` + `ring`/`norm_num`,
  well within default heartbeats.
* **Do NOT introduce `axiom` or leave any `sorry` in the final
  commit.** If the helper proofs stall, ship only the P1 def + the
  named `_one_apply` theorem + the P2 coincidence theorem with the
  `sorry`s in the recipe above all closed. Failing that, defer the
  entire cycle 308 deliverable and pivot to the fallback below.
* **Do NOT pivot to `lem:310B` Phase A.3, `cor:342D`, or any other
  multi-cycle target this cycle.** Cycle 308's deliverable (P1 + P2)
  is achievable in 1–2 hours of focused work; the multi-cycle pivots
  are reserved for cycles where the immediate next step in the §342
  ↔ §321 chain is blocked.
* **Do NOT use `simp [Lagrange.basis_singleton]` without verifying
  it fires.** Cycle 303's example at line 6286 used this pattern
  successfully on a `[0,1]` integral — should also work on the
  `[0, 1/2]` integral, but if it stalls, try
  `Lagrange.basis_singleton` directly as a `rw` step before `simp`.
* **Do NOT poll Aristotle this cycle.** Cycle 308's deliverable is
  cleanly in manual reach; Aristotle latency would only slow the
  cycle. Reserve Aristotle for cycle 309+ when `C(n)` general
  collocation identity work begins.

## Fallback if P1 stalls

If `butcherShiftedLegendre_collocationA` proves harder than expected
(unlikely — it's a one-line variation of cycle 303's existing
definition), the fallback pivot is **a cleanup cycle on the cycle
305 `lem:342B` positivity/uniqueness theorems**:

* Promote the cycle 303 line 6284 `example` and the cycle 304/305
  in-line lemmas to named theorems where they aren't already (audit
  by `grep -nE "^example" OpenMath/Chapter3/Section342.lean`).
* Extract the `butcherShiftedLegendre_zeros_one_apply` helper as a
  public lemma (since cycle 309+ will want it).
* Audit the non-vacuity witnesses for the cycle 305 theorems; ship
  at least one P3 strengthening (e.g. an `n = 2` non-vacuity for
  `B(4)` exercising cycle 307's bridge at higher `k`).

Sorry count must remain 0; cycle must produce a non-trivial commit
per CLAUDE.md "no zero-change cycles".

## Faithfulness check (mandatory pre-commit per CLAUDE.md)

For each new `def` or `theorem` shipped in cycle 308:

* **`butcherShiftedLegendre_collocationA`** — entity context:
  Butcher §342 collocation A-matrix construction (page 237). The
  formula `Yᵢ = y₀ + h Σⱼ Aᵢⱼ f(Yⱼ)` is interpreted as the
  polynomial-interpolation identity: the polynomial interpolating
  `(cⱼ, f(Yⱼ))` (the Lagrange interpolant) integrates to `Yᵢ − y₀`
  over `[0, cᵢ]`. Lean statement captures: same content (the
  Lagrange basis polynomial `Lⱼ` interpolating `δⱼₖ` at the
  canonical zeros, integrated over `[0, cᵢ]`).
  **Definition smuggling check**: ✓ this is the *primary*
  mathematical meaning of the collocation A-matrix; the `B(2n)` /
  `C(n)` / `D(n)` / `E(n,n)` order conditions on the resulting
  tableau will be *theorems* (cycle 307 bridge for B; cycle 309+
  for C/D/E), not part of the definition.
* **`butcherGaussLegendreRK_one`** — entity context: Butcher §342's
  1-stage Gauss method (= implicit midpoint). Lean statement
  captures: same content (`A = 1/2`, `b = 1`, `c = 1/2`). The
  coincidence with `gaussLegendre1Stage` is the genuineness check.
* **`butcherGaussLegendreRK_one_eq_gaussLegendre1Stage`** —
  identity check: NOT a vacuous theorem because the LHS unfolds
  through `_collocationA`, `_quadratureWeights`, `_zeros` (three
  non-trivial integrals/definitions) and the RHS is the hand-defined
  constant tableau. Closing it requires evaluating each of the
  three integrals/zero-extractions at `n = 1`, none of which is a
  syntactic `rfl`.
* **`butcherShiftedLegendre_collocationA_one_apply`** (P1 named
  theorem): tautology check — NO. The proof routes through
  `Lagrange.basis_singleton` (the basis is `1` on a singleton),
  `intervalIntegral.integral_const` (constant-integrand evaluation),
  and `butcherShiftedLegendre_zeros_one_apply` (the zero is `1/2`).
  None of these are syntactic `rfl`.
* **`butcherShiftedLegendre_zeros_one_apply`** (helper, if shipped):
  routes through cycle 273's `butcherShiftedLegendre_one` (the
  closed form `P_1^* = 2X - 1`) plus
  `butcherShiftedLegendre_zeros_isRoot` (the zero is a root) plus
  `linarith`. Genuine work.

## Cross-references

* `OpenMath/Chapter3/Section342.lean:6229` —
  `butcherShiftedLegendre_quadratureWeights` def (cycle 303). The
  template that `butcherShiftedLegendre_collocationA` varies.
* `OpenMath/Chapter3/Section342.lean:6150` —
  `butcherShiftedLegendre_zeros` def (cycle 302).
* `OpenMath/Chapter3/Section342.lean:6166` —
  `butcherShiftedLegendre_zeros_isRoot` (used by the
  `_zeros_one_apply` helper).
* `OpenMath/Chapter3/Section342.lean:6284–6286` — n=1 non-vacuity
  for `_quadratureWeights` (template for cycle 308's n=1 P1
  example).
* `OpenMath/Chapter3/Section342.lean:6745–6804` — cycle 307's
  bridge theorem and non-vacuity examples (target of P3 lifting).
* `OpenMath/Chapter3/Section321.lean:237–264` — `gaussLegendre1Stage`
  and its `B(2)` / `C(1)` / `D(1)` / `E(1,1)` examples (target of
  P2 coincidence).
* `OpenMath/Chapter3/Section312.lean:66` — `RKTableau` structure.
* `OpenMath/Chapter3/Section342.lean` (cycle 273) — `butcherShiftedLegendre_one`
  closed form `P_1^* = C 2 * X - C 1` (used by `_zeros_one_apply`).
* `extraction/formalization_data/entities/cor_342D.json` — the next
  textbook entity in line after `lem:342B` is fully bridged.
* `lem_310B_plan.md` — multi-cycle fallback target if §342 chain
  stalls.

## Bottom line

Cycle 308's deliverable is **P1 minimum, P2 recommended, P3
optional** — all axiom-clean, zero sorries, ~80–150 LOC. The cycle
extends the §342/§321 lift another concrete step toward
`(butcherGaussLegendreRK n).SatisfiesB (2 * n)` while staying
within a single-cycle budget.
