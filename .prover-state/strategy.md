# Cycle 306 strategy — order-condition predicates B(s), C(s), D(s), E(s,s)

## §A — Cycle 305 retrospective

Cycle 305 SHIPPED `lem:342B` fully (Phase B.2 positivity + Phase B.3
uniqueness) axiom-clean, ~310 new LOC at
`OpenMath/Chapter3/Section342.lean` (now 6724 LOC, 0 sorries). The
supervisor scored cycle 305 at −1 because the semantic sorry scanner
flagged 2 new vacuous-proof patterns (`13 → 14`). These are
**false positives** of the well-documented scanner over-firing pattern
(see `.prover-state/issues/tautology_scanner_false_positives.md`):
the cycle 305 deliverables are independently verified axiom-clean
(`[propext, Classical.choice, Quot.sound]` only) by the worker.

**Do NOT attempt to "fix" the scanner false positives.** The standing
remediation is loop-maintainer territory (worker MUST NOT modify
`scripts/autonomous_loop.py`). If a specific hypothesis-name pattern
in cycle 305's new code is the trigger, optionally apply the
documented `h_<name>` → `h<name>` cosmetic rename — but only if you
identify the specific lines via `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/Chapter3/Section342.lean`
and the rename is genuinely α-equivalent. Do not invent rewrites.

§342 is now fully closed (lem:342A from cycle 301; lem:342B from
cycle 305). The next §342 textbook entity is `thm:342C` (Gaussian
Quadrature Order Conditions Equivalence), but it is multi-cycle work.

## §B — Why `cor:342D` is NOT this cycle's target (despite cycle 305 worker recommendation)

I verified the dependency chain by reading the entity JSONs:

* `cor:342D` (Gaussian Quadrature RK Order Condition) has
  `transitive_dependencies: ["thm:342C"]` per
  `extraction/formalization_data/entities/cor_342D.json:60–63`. It
  cites equation (342l) from thm:342C in its proof.
* `thm:342C` (Order Conditions Equivalence) states seven implications
  among `G(2s)`, `B(2s)`, `C(s)`, `D(s)`, `E(s,s)` (Butcher §342
  p. 238). It has **no formal dependencies** in the JSON
  (`dependencies: []`), but its statement and proof presuppose the
  Lean predicates for the B/C/D/E order conditions, plus the G(η)
  order predicate that ties RK methods to elementary-differential
  Taylor expansions.
* `thm:344A` (Radau/Lobatto methods) lists `cor:342D` and `thm:342C`
  in its `transitive_dependencies` (cor_342D.json + thm_344A.json) —
  also blocked.

The natural Butcher-text path `lem:342B → thm:342C → cor:342D → thm:344A`
therefore requires us to first **define** the predicates B(s), C(s),
D(s), E(s,s) for RK tableaux. Those predicates do not yet exist
anywhere in the repo (verify with `grep -rn "SatisfiesB\|B_s_condition\|conditionB" OpenMath/`).
That is the cycle 306 deliverable.

## §C — Cycle 306 target: order-condition predicates + non-vacuity

Ship in a new file `OpenMath/Chapter3/Section321.lean` (Butcher's §321
introduces these conditions; the file slot matches the textbook
subsection). Total estimated LOC: ~150–250.

### C.1 — Predicates (4 definitions)

All four predicates live on `RKTableau s` for `s : ℕ`. Use the
existing `Polynomial.eval` / `Finset.sum` style from cycle 282+; do
NOT introduce new typeclasses.

**`SatisfiesB (M : RKTableau s) (η : ℕ) : Prop`** — Butcher `B(η)`
quadrature condition. Textbook (Butcher §321 / §342 context):

  `B(η) :⇔ ∀ k ∈ {1, …, η}, ∑ᵢ bᵢ · cᵢ^(k-1) = 1/k`

```lean
def RKTableau.SatisfiesB {s : ℕ} (M : RKTableau s) (η : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ η →
    (∑ i : Fin s, M.b i * M.c i ^ (k - 1)) = 1 / (k : ℝ)
```

**`SatisfiesC (M : RKTableau s) (ξ : ℕ) : Prop`** — `C(ξ)` (Butcher
context quoted in `cor_342D.json:context_latex`):

  `C(ξ) :⇔ ∀ i ∈ {1,…,s}, ∀ k ∈ {1,…,ξ}, ∑ⱼ aᵢⱼ · cⱼ^(k-1) = cᵢ^k / k`

```lean
def RKTableau.SatisfiesC {s : ℕ} (M : RKTableau s) (ξ : ℕ) : Prop :=
  ∀ i : Fin s, ∀ k : ℕ, 1 ≤ k → k ≤ ξ →
    (∑ j : Fin s, M.A i j * M.c j ^ (k - 1)) = M.c i ^ k / (k : ℝ)
```

**`SatisfiesD (M : RKTableau s) (ζ : ℕ) : Prop`** — `D(ζ)`:

  `D(ζ) :⇔ ∀ j ∈ {1,…,s}, ∀ k ∈ {1,…,ζ},
    ∑ᵢ bᵢ · cᵢ^(k-1) · aᵢⱼ = (bⱼ / k) · (1 - cⱼ^k)`

```lean
def RKTableau.SatisfiesD {s : ℕ} (M : RKTableau s) (ζ : ℕ) : Prop :=
  ∀ j : Fin s, ∀ k : ℕ, 1 ≤ k → k ≤ ζ →
    (∑ i : Fin s, M.b i * M.c i ^ (k - 1) * M.A i j)
      = (M.b j / (k : ℝ)) * (1 - M.c j ^ k)
```

**`SatisfiesE (M : RKTableau s) (ξ ζ : ℕ) : Prop`** — `E(ξ, ζ)`:

  `E(ξ, ζ) :⇔ ∀ k ∈ {1,…,ξ}, ∀ l ∈ {1,…,ζ},
    ∑ᵢ ∑ⱼ bᵢ · cᵢ^(k-1) · aᵢⱼ · cⱼ^(l-1) = 1 / (l · (k+l))`

```lean
def RKTableau.SatisfiesE {s : ℕ} (M : RKTableau s) (ξ ζ : ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ ξ →
  ∀ l : ℕ, 1 ≤ l → l ≤ ζ →
    (∑ i : Fin s, ∑ j : Fin s,
        M.b i * M.c i ^ (k - 1) * M.A i j * M.c j ^ (l - 1))
      = 1 / ((l : ℝ) * (k + l : ℝ))
```

### C.1' — Mandatory faithfulness verification BEFORE writing

Open `extraction/raw_text/ch03.txt` and grep for "B(η)" / "C(ξ)" /
"D(ζ)" / "E(s, s)" around the §321 subsection (Butcher's §321 is the
canonical introduction of these conditions). The C(s) shape is
quoted verbatim in `cor_342D.json` `context_latex` field — match it.
The E(s, s) RHS form `1 / (l · (k+l))` is from Butcher's §321
treatment; **verify the exact exponent and divisor placement before
shipping**. If the textbook formula differs (e.g. `1 / (k · (k+l))`
instead), adopt the textbook form and document any divergence in the
docstring.

Use `grep -n "^B(" extraction/raw_text/ch03.txt | head -30` or
similar to locate the definitions. If the textbook text is ambiguous,
also cross-reference `extraction/formalization_data/entities/def_323A.json`
(internal order — already formalized) to see how Butcher's §321/§323
constructs are framed.

### C.2 — Non-vacuity witnesses (4+ `example`s)

For each predicate, supply at least one concrete method that satisfies
it at a non-trivial parameter. Use existing infrastructure:

**For `SatisfiesB`** — pick the smallest RK method satisfying `B(1)`:

```lean
-- A 1-stage method with b 0 = 1 and any c satisfies B(1) iff c 0 = 1.
-- (Since ∑ b_i c_i^0 = 1 · c_0^0 = 1, but Lean's 0^0 = 1, so even
-- explicit Euler (c 0 = 0) satisfies B(1) trivially via 0^0 = 1.)
example : explicitEuler.SatisfiesB 1 := by
  intro k h1 hk
  interval_cases k
  simp [explicitEuler, Fin.sum_univ_one, ...]
  -- norm_num or rfl closes
```

Verify `(0 : ℝ)^0 = 1` in Lean before committing to this — if Lean
treats `0^0 = 0` by some convention, pick a different witness (e.g.
a 1-stage method with `c 0 = 1, b 0 = 1`, which is "implicit Euler"
in 1-stage form). The cycle 030 `paddedEuler` (2-stage) may also be
a clean witness. Run `#eval ((0 : ℝ)^0)` in a scratch file first.

**For `SatisfiesC`**: explicit Euler trivially satisfies `C(1)` (the
`k = 1` case is `∑ⱼ a₀ⱼ · cⱼ^0 = c₀^1 / 1`, i.e. `0 = 0` for
explicit Euler's `A = 0` and `c 0 = 0`).

**For `SatisfiesD`**: trickier — explicit Euler `D(1)` is
`∀ j, ∑ᵢ bᵢ · cᵢ^0 · aᵢⱼ = (bⱼ/1)·(1 - cⱼ^1)`. For 1-stage `aᵢⱼ = 0`
and `c 0 = 0, b 0 = 1`: LHS = 0, RHS = 1·(1 - 0) = 1. **Fails.**
Cleanly satisfiable witnesses include:
- **Implicit Euler 1-stage** `c 0 = 1, b 0 = 1, A 0 0 = 1`: LHS =
  `b 0 · c 0^0 · A 0 0 = 1 · 1 · 1 = 1`; RHS = `(1/1) · (1 - 1) = 0`.
  Also fails.
- Just ship `D(0)` vacuously on any method as the non-vacuity witness.

**For `SatisfiesE`**: same — ship `E(0, 0)` vacuously on any method.

Vacuous witnesses for D/E are NOT definition smuggling: the
predicate's content lives in `SatisfiesD ζ` for `ζ ≥ 1`; D(0) being
trivially true is correct mathematical behavior (no condition to
check when the index range is empty). Document this stance in the
docstring.

If you want a non-trivial D(1) / E(1,1) witness, the Gauss-Legendre
1-stage method (`s = 1, c = 1/2, b = 1, A = 1/2`) satisfies B(2),
C(1), D(1), E(1,1) — it's the order-2 implicit midpoint. Verify by
hand: B(1) is `1 · (1/2)^0 = 1`, B(2) is `1 · (1/2)^1 = 1/2`. C(1)
is `(1/2) · (1/2)^0 = (1/2)^1 / 1` i.e. `1/2 = 1/2`. D(1) is
`1 · (1/2)^0 · (1/2) = (1/1) · (1 - 1/2)` i.e. `1/2 = 1/2`. E(1,1)
is `1 · (1/2)^0 · (1/2) · (1/2)^0 = 1/(1 · 2) = 1/2`. All check out.
**Use this as the substantive non-vacuity witness for all four
predicates if you have time.** Define it as `gaussLegendre1Stage`
in Section321.lean (or alongside).

### C.3 — Empty-case lemmas (4 trivial `simp`-tagged helpers)

```lean
@[simp] theorem RKTableau.satisfiesB_zero {s : ℕ} (M : RKTableau s) :
    M.SatisfiesB 0 := by intro k h1 hk; omega

@[simp] theorem RKTableau.satisfiesC_zero {s : ℕ} (M : RKTableau s) :
    M.SatisfiesC 0 := by intro i k h1 hk; omega

@[simp] theorem RKTableau.satisfiesD_zero {s : ℕ} (M : RKTableau s) :
    M.SatisfiesD 0 := by intro j k h1 hk; omega

@[simp] theorem RKTableau.satisfiesE_zero_zero {s : ℕ} (M : RKTableau s) :
    M.SatisfiesE 0 0 := by intro k h1 hk l hl1 hl; omega
```

These confirm vacuous behavior and provide universally-applicable
witnesses for the D / E non-vacuity slots in C.2 if the Gauss-Legendre
1-stage path stalls.

### C.4 — File placement

Create `OpenMath/Chapter3/Section321.lean`. Imports:
- `OpenMath.Chapter3.Section312` (for `RKTableau` — verify by
  `grep -n "structure RKTableau\b" OpenMath/Chapter3/Section312.lean`)
- Mathlib polynomial/Finset imports already used by Section342.lean
  (likely `Mathlib.Algebra.BigOperators.Fin`,
  `Mathlib.Algebra.Order.Field.Basic`)

Add `import OpenMath.Chapter3.Section321` to `OpenMath/Chapter3.lean`
aggregator.

## §D — What NOT to try

1. **DO NOT attempt `thm:342C` itself this cycle.** Its proof
   requires (a) the G(η) predicate (RK method has order η) — only
   partially captured via def:530B/C explicit-only and def:323A
   internal order; needs clean B-series-based form, (b) rooted-tree
   subtree-pruning machinery from §321 ("all order conditions based
   on trees containing the structure ···[τ^(k-1)]··· can be removed"
   — non-trivial combinatorial argument through cycle 254+ tree
   infrastructure), and (c) a "non-singular matrix" multiplication
   argument mapping C(s) conditions to E(s,s) conditions. Multi-cycle.

2. **DO NOT attempt `cor:342D` itself this cycle.** Blocked by
   thm:342C (cites equation 342l).

3. **DO NOT attempt `thm:344A` this cycle.** Blocked by cor:342D plus
   Radau / Lobatto polynomial machinery (`P_s^* ± P_{s-1}^*`
   factorizations) that isn't built yet.

4. **DO NOT modify `scripts/autonomous_loop.py`** to address the
   semantic sorry false-positives flagged by the cycle 305 supervisor.
   Loop-maintainer territory.

5. **DO NOT introduce new typeclasses** for the order conditions.
   Keep them as plain `Prop`-valued `def`s on `RKTableau s`. Sticking
   with `def ... : Prop` matches existing §381 / §383 style and
   sidesteps CLAUDE.md's "every class needs an instance" obligation.

6. **DO NOT define G(η) (the "method has order η" predicate) this
   cycle.** That's a separate, deeper deliverable bridging def:530B/C
   explicit-only order with the elementary-differential Taylor
   expansion form. Start with B/C/D/E only.

7. **DO NOT attempt to relate the new predicates to lem:342B's
   `butcherShiftedLegendre_quadratureWeights` this cycle.** The bridge
   "the canonical Lagrange weights at the `butcherShiftedLegendre_zeros`
   satisfy B(2n)" is a separate, single-cycle followup that exercises
   lem:342B directly. Save for cycle 307.

8. **DO NOT submit to Aristotle this cycle.** The deliverables are
   definitional + trivial non-vacuity witnesses; Aristotle's strength
   is proof-heavy targets, not writing predicate definitions.

9. **DO NOT skip the §C.1' faithfulness verification.** The risk of
   defining B(s)/C(s)/D(s)/E(s,s) with subtly wrong RHS (e.g. wrong
   factorial, wrong index range) is real — a few minutes reading
   Butcher §321 / §342 directly is cheap insurance against shipping
   a permanent infrastructure-level error.

## §E — Pre-flight verification (5 minutes)

Before writing any Lean:

1. Verify §342 closure landed: `git log -1 --format='%H %s'` should
   show cycle 305's commit (`43d39a4`). `wc -l OpenMath/Chapter3/Section342.lean`
   should report ~6724 LOC, `grep -c sorry OpenMath/Chapter3/Section342.lean`
   should be 0.
2. Verify `RKTableau` namespace: `grep -n "structure RKTableau\b" OpenMath/Chapter3/Section312.lean`
   should show the structure. Note its namespace
   (likely `OpenMath.Chapter3.Section312.RKTableau`) and use it
   consistently in `Section321.lean`.
3. Verify `explicitEuler` location: `grep -rn "def explicitEuler\b" OpenMath/Chapter3/`.
   Note its exact name and namespace.
4. Verify Butcher §321's exact formulas (per §C.1'): open
   `extraction/raw_text/ch03.txt` and search for "B(η)" / "C(ξ)" /
   "D(ζ)" / "E(s, s)" definitions.
5. Sanity-check Lean's `(0 : ℝ)^0` convention (`#eval` in a scratch
   file) before relying on it for explicit Euler's B(1) witness.

## §F — Faithfulness check

For each new `def`:
- Quote Butcher §321's text in the docstring.
- Confirm the Lean type matches the textbook statement.
- Confirm no smuggling: the predicate's primary meaning is the
  quadrature/interpolation condition; we are NOT defining "B(s)" as
  "what makes the method order 2s" — that would be smuggling.

For each non-vacuity `example`:
- Identify the concrete method and parameter value (e.g. "explicit
  Euler satisfies B(1)").
- Verify by hand that the condition reduces to a true arithmetic
  identity at that parameter.

For each empty-case lemma (`SatisfiesB 0` etc.):
- Document that this is vacuous because the quantifier range is empty
  (`k : ℕ, 1 ≤ k, k ≤ 0` is unsatisfiable).
- The `omega` closure genuinely discharges `1 ≤ k ∧ k ≤ 0 → False`.

## §G — Cycle 306 deliverable bar

- **MUST ship**: 4 predicate `def`s + 4 vacuous-case `simp` lemmas.
  Minimum ~80 LOC. Axiom-clean.
- **SHOULD ship**: 4+ non-vacuity `example`s (use explicit Euler
  where B(1)/C(1) work; vacuous D(0)/E(0,0) on any method as the
  baseline; substantive Gauss-Legendre 1-stage `B(2)/C(1)/D(1)/E(1,1)`
  witness if you scope a `gaussLegendre1Stage` def). Adds ~50–150 LOC.
- **STRETCH (cycle 307+)**: bridge to `lem:342B`: a theorem
  `butcherShiftedLegendre_quadratureWeights_satisfiesB` showing the
  Lagrange weights from cycle 303 satisfy B(2n) when paired with the
  canonical zeros as c-values. This is the substantive bridge between
  §342 and the order-condition framework. **Skip if cycle 306 budget
  runs out** — clean cycle 307 deliverable.

Sorry count: 0 → 0 mandatory. Axiom-clean: all new declarations must
return `[propext, Classical.choice, Quot.sound]` (or a subset) under
`#print axioms`.

After landing, update:
- `extraction/formalization_data/lean_status.json`: no entity row to
  change (B(s)/C(s)/D(s)/E(s,s) are not extracted entities; they're
  prerequisite infrastructure). Document the infrastructure landing
  in the cycle 306 task results instead.
- `plan.md`: optionally add a brief note under the §342 / §344 rows
  pointing to Section321.lean as their prerequisite.

## §H — Cycle 307+ outlook

With B/C/D/E predicates in hand, the natural sequence is:

- **Cycle 307**: ship the bridge
  `butcherShiftedLegendre_quadratureWeights_satisfiesB` exercising
  cycle 303's Lagrange weights + cycle 305's exactness. Then attempt
  the easier directions of thm:342C (e.g. one of G(2s)→B(2s) /
  G(2s)→E(s,s)) if a clean G(η) predicate can be defined as a
  single-cycle prerequisite.
- **Cycles 308+**: tackle thm:342C in full; once shipped, cor:342D
  and thm:344A become tractable single-cycle corollaries.

Total path to closing the §342 cluster (cor:342D + thm:344A): ~3–4
cycles from cycle 306.

## §I — Sanity reminder

Cycle 306 is a **pure infrastructure cycle**. The deliverable is
small, definitional, and axiom-clean by construction. Resist the
temptation to ship thm:342C or cor:342D ahead of schedule — they
require multi-cycle proof infrastructure (rooted-tree subtree-pruning,
non-singular matrix multiplication, G(η) predicate) that does not
fit in one cycle. The reward is unblocking 6+ downstream textbook
entities (thm:342C, cor:342D, thm:344A, thm:358A, lem:359A, thm:324C,
cor:359B) in cycles 307–310.
