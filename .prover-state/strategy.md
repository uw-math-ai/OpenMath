# Cycle 254 strategy — `lem:310B` Phase A.0 (B-series term scaffold)

## TL;DR

Cycle 253 saturated Butcher Table 310(II) row r=5 with 9 axiom-clean
α-witnesses. The task results explicitly direct cycle 254 to **pivot to
`lem:310B` Phase A** and **do not extend the witness battery to r=6**.

`lem:310B` itself (the Elementary Differential Weight Formula) is
genuinely multi-cycle: per its `dependencies` field it requires
`thm:306A` (Taylor's theorem — a multinomial expansion theorem that is
itself unformalised and non-trivial) plus labeled-tree infrastructure
(currently absent — needed to state the LHS series (310i) which is a
sum over labeled rooted trees with orbit divisions). Attempting full
closure in one cycle would either stall or require sorry-first
scaffolds, which the cycle 149/150 and cycle 200/201 rollback precedents
forbid.

**Cycle 254 target**: ship Phase A.0 of the `lem:310B` infrastructure:
define the per-tree B-series term function `bseriesTerm` (the summand
of equation (310i), an order-`r(t)` term with weight `1/σ(t)` and value
`F[t](y₀)`), and ship the trivial `t = τ` case of `lem:310B` (the
"obvious" half per Butcher's own proof) plus the θ-rewriting scaffold
that the full proof goes through. Axiom-clean, sorry-clean,
single-cycle, load-bearing prerequisite for any further `lem:310B`
work.

## §A — What to ship

### P1 (REQUIRED) — `bseriesTerm` definition (Section310.lean)

Add the per-tree B-series summand to `OpenMath/Chapter3/Section310.lean`
immediately after the existing `elementaryDiff` definition (currently
ending at line 199, just before the trailing `end OpenMath.Chapter3.Section310`).
Add the new declarations *before* the trailing `end` so they live in
the same namespace block.

Definition (Butcher §310 equation (310i) summand form):

```lean
/-- The per-tree B-series term `(h^r(t) / σ(t)) • F(t)(y₀)`, the
summand of Butcher's series (310i). For `f` smooth and `y₀ : E`, this
is the contribution of the rooted tree `t` to the elementary-differential
expansion of one ODE step. -/
noncomputable def bseriesTerm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) (t : RootedTree) : E :=
  (h ^ RootedTree.order t / (RootedTree.symmetry t : ℝ)) •
    elementaryDiff f y₀ t
```

Justification for placing the `(σ(t) : ℝ)` cast in the denominator
literally rather than via a `Polynomial.C`-style wrapper: cycle 250's
`alphaWeight` already adopts this convention
(`OpenMath/Chapter3/Section301.lean:305`); reuse it for consistency.
`RootedTree.symmetry_pos` (cycle 017) gives `0 < σ(t)` for
positivity-driven downstream consumers — note for cycle 255 that the
cast denominator is non-zero, so `field_simp`-style rewriting is safe.

### P2 (REQUIRED) — Trivial-tree identity (`t = τ` case of `lem:310B`)

```lean
/-- `lem:310B` t = τ case: at the trivial tree, the B-series term
reduces to `h • f y₀`. Butcher's proof of Lemma 310B describes this
case as "obvious"; in our σ-faithful formalisation it reduces to:
σ(τ) = 1 (cycle 017), r(τ) = 1 (cycle 017), and `iteratedFDeriv ℝ 0 f
y₀` collapsing to `f y₀` (the `Fin 0`-indexed empty-tuple input to a
0-fold derivative). -/
theorem bseriesTerm_vertex
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) :
    bseriesTerm f y₀ h RootedTree.vertex = h • f y₀ := by
  unfold bseriesTerm
  rw [show RootedTree.order RootedTree.vertex = 1 from rfl,
      show RootedTree.symmetry RootedTree.vertex = 1 from rfl]
  -- Goal: (h ^ 1 / (1 : ℝ)) • elementaryDiff f y₀ vertex = h • f y₀
  simp [pow_one, div_one]
  -- Goal: elementaryDiff f y₀ vertex = f y₀
  -- vertex = mk [] so elementaryDiff unfolds to iteratedFDeriv ℝ 0 f y₀
  -- evaluated on the empty `Fin 0 → E` tuple, which is f y₀.
  show elementaryDiff f y₀ (RootedTree.mk []) = f y₀
  unfold elementaryDiff
  simp [iteratedFDeriv_zero_apply]
```

**Risk R-P2.1**: `RootedTree.vertex` may not be a direct `mk []`
synonym in the cycle 017 file. Check first via `lean_local_search
"vertex"` in `OpenMath/Chapter3/Section301.lean`. If `vertex` is
defined as `RootedTree.mk []`, the `show elementaryDiff f y₀ (mk [])`
step works by `rfl`; if `vertex` is named differently, replace with
the actual identifier.

**Risk R-P2.2**: `iteratedFDeriv_zero_apply` may have a different
Mathlib name in the current pin. Backup: use `lean_loogle` with type
pattern `iteratedFDeriv _ 0 _ _ _ = _`, or `lean_local_search
"iteratedFDeriv_zero"`. Candidate names to try in `lean_multi_attempt`
at the failing `simp` line: `["simp [iteratedFDeriv_zero_apply]",
"simp [iteratedFDeriv_zero_eq_comp]", "rfl",
"exact iteratedFDeriv_zero_apply _ _"]`.

**Risk R-P2.3**: `order vertex = 1` and `symmetry vertex = 1` may
not be definitional. The cycle 017 `tau_values` at
`Section301.lean:267` proves these. If `show ... from rfl` fails,
swap to `rw [tau_values]` (extracting both equalities) or use inline
`have h_order : ... := by simp [...]` / `have h_sigma : ... := by
simp [...]`. Verify by `lean_hover_info` on `order` and `symmetry`
to check definitional reducibility.

### P3 (REQUIRED) — θ-reweighting scaffold

```lean
/-- `lem:310B` rearrangement core: at every rooted tree `t`, the
B-series term is invariant under multiplication by the elementary
weight `θ(t)` of the exact-solution operator. Since `θ ≡ 1` (cycle
249, `theta_eq_one`), this is mathematically trivial — but it is the
pointwise algebraic identity Butcher's `lem:310B` proof goes through
to relate the labeled and unlabeled forms of (310i).

NOT the full statement of `lem:310B` — the full lemma asserts a
re-summation identity between a labeled-tree-orbit sum (LHS, requires
labeled-tree machinery not yet built) and the θ-weighted unlabeled
sum (RHS). Cycle 254 ships only the pointwise scaffold; the
re-summation requires `thm:306A` (Taylor's theorem) plus labeled-tree
infrastructure. -/
theorem bseriesTerm_eq_theta_smul_bseriesTerm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (h : ℝ) (t : RootedTree) :
    bseriesTerm f y₀ h t = (RootedTree.theta t) • bseriesTerm f y₀ h t := by
  rw [RootedTree.theta_eq_one t, one_smul]
```

**Risk R-P3.1**: `theta_eq_one`'s qualified path. Per grep,
cycle 249 placed `theta` and `theta_eq_one` inside
`namespace OpenMath.Chapter3.Section310` (the file's own namespace),
with `theta` itself inside what is effectively the `RootedTree`
namespace at file scope. Inside Section310's namespace block, write
just `theta_eq_one t` (no qualifier). If you have to qualify
externally, use the dot-notation `t.theta` and fully qualified
`OpenMath.Chapter3.Section310.theta_eq_one` — verify via
`lean_local_search "theta_eq_one"`.

**Risk R-P3.2**: Reading the cycle 249 grep output more carefully —
the `def theta` is at line 137, and `theorem theta_eq_one` is at
line 154. Both are at indent level 2 (inside a `mutual` block?
indent suggests nesting). Inspect cycle 249's namespace structure
with `Read OpenMath/Chapter3/Section310.lean offset=120 limit=80`
before writing P3. If `theta_eq_one` is inside a `mutual` block,
it may need `(t)` as an explicit argument, not dot-notation.

### P4 (REQUIRED) — Three non-vacuity witnesses

After the three new top-level declarations (and BEFORE the trailing
`end OpenMath.Chapter3.Section310`), add three concrete `example`
blocks. They must be in the same namespace block as `bseriesTerm` so
the name resolves without qualification:

```lean
-- §310 B-series term non-vacuity witnesses (cycle 254).

example (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesTerm f y₀ h RootedTree.vertex = h • f y₀ :=
  bseriesTerm_vertex f y₀ h

example (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesTerm f y₀ h RootedTree.cherry =
      RootedTree.theta RootedTree.cherry • bseriesTerm f y₀ h RootedTree.cherry :=
  bseriesTerm_eq_theta_smul_bseriesTerm f y₀ h RootedTree.cherry

example (f : ℝ → ℝ) (y₀ h : ℝ) :
    bseriesTerm f y₀ h RootedTree.broom₃ =
      RootedTree.theta RootedTree.broom₃ • bseriesTerm f y₀ h RootedTree.broom₃ :=
  bseriesTerm_eq_theta_smul_bseriesTerm f y₀ h RootedTree.broom₃
```

These should close via the named theorems above (no `by` block
needed; direct term-mode `exact` shape). They provide regression
oracles for cycle 255+ work.

**Risk R-P4.1**: `RootedTree.cherry` / `RootedTree.broom₃`
definitions. Per cycle 017 they are concrete constants in
`Section301.lean`, exercised in cycle 251–253 examples. Use the same
qualification as cycle 251–253. If `cherry` and `broom₃` are defined
in a different namespace (e.g. directly under `OpenMath.Chapter3.Section301`
rather than `RootedTree`), adjust the qualification — but the
cycle 251–253 examples consistently use `cherry` and `broom₃` bare,
which means they should be in scope here too.

### P5 (STRETCH — DO NOT BLOCK ON) — Order-r homogeneity in h

Only if P1–P4 land in under ~75% of cycle time:

```lean
/-- B-series term is order-`r(t)` homogeneous in the step size `h`.
A useful algebraic identity for future cycle 255+ work on summing
B-series terms across trees of equal order. -/
theorem bseriesTerm_smul_h
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (y₀ : E) (c h : ℝ) (t : RootedTree) :
    bseriesTerm f y₀ (c * h) t =
      c ^ RootedTree.order t • bseriesTerm f y₀ h t := by
  unfold bseriesTerm
  rw [mul_pow]
  rw [show (c ^ RootedTree.order t * h ^ RootedTree.order t) /
        (RootedTree.symmetry t : ℝ) =
      c ^ RootedTree.order t *
        (h ^ RootedTree.order t / (RootedTree.symmetry t : ℝ)) from by ring]
  rw [mul_smul]
```

**Risk R-P5.1**: the `ring` step is over ℝ-with-explicit-division.
If it stalls (unlikely on a single rational expression), swap to
`field_simp [Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp
RootedTree.symmetry_pos)]; ring`. **Abort P5 cleanly if either form
stalls — P5 is stretch, not load-bearing.**

## §B — What NOT to do (BINDING)

* **Do NOT attempt the full `lem:310B`.** Per the entity JSON it
  depends on `thm:306A` (unformalised, heavy multinomial Taylor) and
  on labeled-tree machinery (absent). The full statement (310i) cannot
  even be stated in Lean today. Cycle 254 ships *only* the trivial
  `t = τ` case + the θ-rewriting scaffold.

* **Do NOT introduce sorry-first scaffolds for `lem:310B`** (statement
  with `sorry` body). The cycle 149/150 rollback (def:530B Path A) and
  cycle 200/201 rollback (thm:381H scaffold) establish that sorry-first
  deliverables get rolled back. Sorry count must stay at 0 across
  cycle 254.

* **Do NOT extend the α-witness battery to r=6.** Per the cycle 253
  task results: "Butcher Table 310(II) stops at r=5, and the r=6 count
  is 20 trees (treadmill territory)."

* **Do NOT introduce `TruncatedRootedTree` + `Fintype` machinery.**
  These are genuinely needed for `lem:310B` Phase A.1+, but the
  `Fintype` instance on subtype-of-nested-inductive is multi-cycle.
  Cycle 254 defers this.

* **Do NOT attempt to compile `OpenMath/Chapter4/Section441.lean`.**
  43+ consecutive GPFS timeouts since cycle 182 (~12 days). Skip
  without re-running the smoke test.

* **Do NOT attempt `lem_311A_order_two`** (the p=2 extension of cycle
  248's `lem_311A_order_one`). Multi-cycle per cycle 248 consultant
  analysis.

* **Do NOT attempt `thm:306A` (Taylor's theorem).** Multinomial
  expansion theorem; multi-cycle infrastructure work.

* **Do NOT attempt `def:381F` / `thm:381H` deferred-direction Banach
  fixed-point bridges** per `thm_381H_deferred.md`. Multi-cycle.

* **Do NOT raise `maxHeartbeats` above 200000.**

* **Do NOT introduce `axiom`/`constant` declarations.**

* **Do NOT edit `scripts/autonomous_loop.py`** (loop-maintainer
  territory).

* **Do NOT poll any Aristotle project this cycle.** No submissions
  are planned. If a planned cycle 255+ submission is queued by a
  future cycle, the single-poll-after-30-min rule from CLAUDE.md
  applies — not this cycle.

* **Do NOT touch the cycle 251–253 alphaWeight witnesses** in
  Section301.lean. They are regression oracles.

## §C — Verification commands

After P1–P4 (P5 if stretch lands), run these in order:

```bash
# 1. Section310 compiles standalone.
time timeout 180 lake env lean OpenMath/Chapter3/Section310.lean
# Expected: clean exit (~5–15s warm, ≤120s clean).

# 2. Section301 still compiles (regression check on cycle 250–253 work).
time timeout 180 lake env lean OpenMath/Chapter3/Section301.lean
# Expected: clean exit, ≤ 15s warm.

# 3. Aggregator builds.
time timeout 300 lake env lean OpenMath/Chapter3.lean

# 4. Sorry count unchanged at 0.
grep -c sorry OpenMath/Chapter3/Section310.lean
grep -c sorry OpenMath/Chapter3/Section301.lean

# 5. Tautology scanner sweep.
rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/Chapter3/Section310.lean
# Expected: no matches.

# 6. Axiom check on each new theorem (USE `lean_verify` MCP, NOT
#    `#print axioms` on a standalone file — per CLAUDE.md and the
#    cycle 192 stale-cache discovery, `#print axioms` on a standalone
#    Lean invocation can produce false-positive `sorryAx` results
#    until `lake build` refreshes the cache).
#    Use lean_verify on:
#      - OpenMath.Chapter3.Section310.bseriesTerm  (definition)
#      - OpenMath.Chapter3.Section310.bseriesTerm_vertex
#      - OpenMath.Chapter3.Section310.bseriesTerm_eq_theta_smul_bseriesTerm
#      - (P5 stretch) OpenMath.Chapter3.Section310.bseriesTerm_smul_h
# Expected for each: [propext, Classical.choice, Quot.sound] only.
```

If step 1 stalls past 180s for a 4-theorem change of this size, the
GPFS pathology has spread beyond Section441 — escalate via a fresh
issue file (do not delete `cycle_182_gpfs_slowness.md`; append).

## §D — Risk inventory

| Risk | Severity | Mitigation |
|---|---|---|
| R-P2.1 — `RootedTree.vertex` vs `mk []` mismatch | low | Check cycle 017 file; use whichever name resolves. Both should compile under definitional unfolding. |
| R-P2.2 — `iteratedFDeriv_zero_apply` name drift | medium | `lean_loogle` / `lean_local_search` for current Mathlib name. Backup: `lean_multi_attempt` with three candidates. |
| R-P2.3 — `order vertex = 1` / `σ vertex = 1` not `rfl`-closable | medium | Inline `simp [...]` proofs of `h_order` / `h_sigma`; route through cycle 017's `tau_values`. |
| R-P3.1 — `theta_eq_one` qualified name | low | Inside Section310's namespace block, write just `theta_eq_one t`. If qualification needed, use the fully qualified path. |
| R-P3.2 — `theta_eq_one` mutual-block argument shape | low | Inspect Section310.lean lines 120–200 before writing P3. |
| R-P4.1 — `RootedTree.cherry` / `RootedTree.broom₃` qualification | low | Per cycle 251–253, both are in scope as `cherry` and `broom₃`. Match their usage exactly. |
| R-P5.1 — `ring` over ℝ-with-division stalls | low (stretch only) | Swap to `field_simp; ring`. Abort P5 if both stall. |
| R-namespace-end | low | `bseriesTerm` declarations must go INSIDE the existing namespace block, BEFORE the trailing `end OpenMath.Chapter3.Section310` (line ~199). The P4 examples can be either inside (term mode `exact`) or outside (would need full qualification). Prefer inside for terseness. |

## §E — Faithfulness check

Cycle 254 introduces:

* `bseriesTerm` — pure scaffold definition. Encodes the (310i)
  summand verbatim with σ-faithfulness divergence inherited from
  cycle 017 (recursive (301b) definition vs Butcher §300's automorphism-
  group definition). Same divergence cycle 250's `alphaWeight`
  inherits; documented in `Section301.lean`'s file docstring and
  `.prover-state/issues/symmetry_group_equivalence.md`.

* `bseriesTerm_vertex` — the `t = τ` half of `lem:310B`. Butcher's
  proof calls this "obvious"; our Lean form is the algebraic
  identity `bseriesTerm f y₀ h vertex = h • f y₀`, which is true by
  definition under σ(τ)=1, r(τ)=1, and `iteratedFDeriv ℝ 0`-collapse.

* `bseriesTerm_eq_theta_smul_bseriesTerm` — the θ-rewriting scaffold
  that Butcher's full lem:310B proof relies on after applying
  thm:306A. **NOT** the full statement of `lem:310B`; it's the
  pointwise prerequisite identity. Documented explicitly in the
  docstring: "NOT the full statement of `lem:310B` — the full lemma
  asserts a re-summation identity between a labeled-tree-orbit sum
  (LHS, requires labeled-tree machinery not yet built) and the
  θ-weighted unlabeled sum (RHS)."

`lean_status.json` row for `lem:310B`: **DO NOT MARK AS FORMALIZED**.
Cycle 254 ships scaffolding only. Status stays `unformalized`. The
`plan.md` row stays `[ ]`.

The cycle 250 `alphaWeight` row reflects (302a) as a definition
divergence (a closed-form replacing Butcher §302's labeled-counting
definition). `bseriesTerm` does NOT introduce a parallel divergence —
the (310i) summand IS literally `(h^r(t) / σ(t)) • F(t)(y₀)` in
Butcher, so the Lean definition is a faithful transcription.

## §F — Cycle 255+ outlook

After cycle 254 lands:

* **Cycle 255 candidates** (highest leverage first):
  - Define `TruncatedRootedTree N := { t : RootedTree // order t ≤ N }`
    plus minimal API (val coercion, monotone embedding to higher N).
    Avoid attempting `Fintype` instance (multi-cycle).
  - Ship a "B-series partial sum" definition that sums `bseriesTerm`
    over a hand-enumerated `Finset` of small trees (e.g., the four
    r ≤ 3 trees, then the eight r ≤ 4 trees). This gives a working
    partial B-series without `Fintype`.
  - Aristotle batch for the `iteratedFDeriv ℝ 1 f y ↔ fderiv ℝ f y`
    bridge (cycle 248 task results' P2(a) blocker); single-poll
    after 30 min.

* **Cycle 256+**: with trunc-trees + partial-sum infrastructure in
  hand, attempt the small-r form of `lem:310B` (state and prove for
  `TruncatedRootedTree 2` or 3, mechanically expanded) as a stepping
  stone toward the general form.

* **Multi-cycle `lem:310B` general form**: ~5–8 cycles (labeled tree
  theory + `thm:306A` Taylor + the orbit-counting combinatorial
  bridge per Butcher's proof). Plan in a dedicated scoping doc when
  cycle 256+ lands the small-r case.

## §G — Bottom-line directive

Cycle 254 deliverable: P1 + P2 + P3 + P4. Ship as one ~80 LOC
addition to `OpenMath/Chapter3/Section310.lean`. Single-cycle scope,
axiom-clean, sorry-clean. P5 only if time permits.

NO Aristotle. NO sorries. NO multi-cycle infrastructure commitments.
NO `TruncatedRootedTree` / `Fintype` attempts. NO labeled tree
theory. NO `thm:306A` attempts.

If P1–P4 stall in the first half of the cycle, abort and ship a
minimal alternative: a single new named theorem of the form
`bseriesTerm_pos_smul_homogeneity` (rewrite of P5 with a non-
negativity flavor), or alternatively retreat to a 3-line
`bseriesTerm_zero` theorem proving `bseriesTerm f y₀ 0 t = 0`
whenever `0 < order t` (a trivial scaling fact). Sorry count stays
0 either way.

## §H — Pre-flight checklist

Before starting P1, verify by `Read` / `Grep` (these are cheap and
prevent the most common cycle-stall failure modes):

1. **`Section310.lean` namespace structure at lines 120–200.** Confirm
   `theta` lives at file scope inside `namespace OpenMath.Chapter3.Section310`,
   not inside a sub-namespace. Confirm `theta_eq_one` is accessible
   bare-named from inside the same namespace.

2. **`Section301.lean::tau_values` at line 267.** Confirm it states
   `order vertex = 1 ∧ symmetry vertex = 1 ∧ density vertex = 1` (or
   similar). If the structure differs, P2's `show ... from rfl`
   strategy may need adjustment.

3. **`RootedTree.vertex` definition.** Confirm in Section301.lean
   that `vertex` is defined as `RootedTree.mk []` (or whichever
   constructor form). If it's a separate `def`, the `show`
   manipulation in P2 needs that intermediate `unfold`.

4. **`iteratedFDeriv_zero_apply` Mathlib name.** Run
   `lean_loogle "iteratedFDeriv _ 0"` or `lean_local_search
   "iteratedFDeriv_zero"` BEFORE attempting P2's body. If the name
   differs, pre-load `lean_multi_attempt` candidates.

If checklist items reveal mismatches with the strategy as written,
adapt P2/P3 locally rather than escalating — the deliverable is the
mathematical content (B-series term + trivial case + θ-scaffold),
not the literal Lean text in this strategy.
