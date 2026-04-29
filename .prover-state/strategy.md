# Cycle 023 Strategy

## Decision summary

**Target this cycle: `thm:343A` — "The reflection of the reflection of a
Runge–Kutta method is the original method."** (§343, page 220–221.)

**Deviation from cycle 022's recommendation:** Cycle 022's task results
recommended `thm:381G` ("Irreducible Runge–Kutta Stage Distinguishability").
Re-reading `extraction/formalization_data/entities/thm_381G.json` and the
proof on page 303 shows two genuine multi-cycle obstructions cycle 022
underestimated:

1. The proof's *Y-stages* clause ("there exists a Lipschitz ODE such that
   `Y_i ≠ Y_j`") **requires `thm:314A` ("Independence of the elementary
   differentials")** — listed as a transitive dependency in the entity
   JSON, currently `unformalized`. That clause cannot close without §314
   infrastructure.
2. The proof's *Φ-clause* ("there exists a tree `t` with `Φ_i(t) ≠ Φ_j(t)`")
   needs the textbook's algebra-of-vectors / partition-basis argument
   (`Ã = A`, characteristic functions span, closure under matrix-A
   multiplication via tree induction). That is real linear algebra over ℝ^s,
   estimated 2–3 cycles of focused work even with Aristotle.

CLAUDE.md says **"Proved in full (no sorry's in committed code, unless
mid-restructuring)"**. Scaffolding `thm:381G` with sorry's that cannot close
this cycle would violate that. So we pivot to a target that (a) is in
plan.md, (b) is genuinely 1-cycle scope, and (c) makes solid progress.

`thm:343A` is the clean choice. It has **no listed dependencies**, the
textbook proof is "easy to verify… we present without proof" (Butcher
page 221), and the entire argument reduces to `ring` after definitional
unfolding.

`thm:381G` is **not abandoned** — it is deferred to a later cycle once the
partition-algebra infrastructure (or an alternative non-algebraic proof) is
sketched out. Treat it as a multi-cycle research item, not a one-shot
target.

## What `thm:343A` says (verbatim from
`extraction/formalization_data/entities/thm_343A.json`)

> The reflection of the reflection of a Runge–Kutta method is the original
> method.

Butcher §343 (`extraction/raw_text/ch03.txt` lines 4970–5037) defines the
reflection of `(A, b, c)` component-wise:

* `ĉ_i = (Σ_j b_j) - c_i`
* `â_{ij} = b_j - a_{ij}`
* `b̂_j = b_j`

(Derivation: subtract (343c) from (343b) to express stages in terms of `y_n`,
rearrange (343c) to express `y_{n-1}` in terms of `y_n`, then negate all
coefficients to recover a forward-pointing tableau.)

Reflecting twice:

* `ĉ̂_i = (Σ_j b̂_j) - ĉ_i = (Σ_j b_j) - ((Σ_j b_j) - c_i) = c_i`
* `â̂_{ij} = b̂_j - â_{ij} = b_j - (b_j - a_{ij}) = a_{ij}`
* `b̂̂_j = b̂_j = b_j`

Each line closes by `ring` (over `ℝ`). The whole theorem is one structure
extensionality plus three `ring` calls.

## Concrete cycle 023 plan

### Step 1 — file location

Create `OpenMath/Chapter3/Section343.lean`. Open the relevant namespaces:

```lean
import OpenMath.Chapter3.Section312

namespace OpenMath.Chapter3.Section343

open OpenMath.Chapter3.Section312

end OpenMath.Chapter3.Section343
```

`Section343.lean` is freestanding; it imports only `Section312` (for
`RKTableau`). No dependency on `Section381` or any other §3 module.

After creating the file, add the import line to
`OpenMath/Chapter3.lean` (the chapter aggregator) so `lake build` picks it
up. (If `OpenMath/Chapter3.lean` does not exist, the file just needs to be
reachable from `OpenMath.lean` — check with
`Glob "OpenMath/**/*.lean"` early in the cycle and follow the existing
pattern from `Section381.lean`'s registration.)

### Step 2 — define `reflection`

Inside `namespace OpenMath.Chapter3.Section312.RKTableau` (so the function is
available as `M.reflection`):

```lean
/-- Butcher §343 — the *reflection* of a Runge–Kutta method, sometimes
called the *adjoint method*.

Given the tableau `(A, b, c)`, the reflection has tableau `(Â, b̂, ĉ)`
defined component-wise by

* `â_{ij} = b_j - a_{ij}`,
* `b̂_j = b_j`,
* `ĉ_i = (Σ_j b_j) - c_i`.

Derivation (Butcher page 220): subtract (343c) from (343b) to express
each stage value `Y_i` in terms of `y_n` (the result), and rearrange
(343c) to express `y_{n-1}` in terms of `y_n`. Reverse all signs to
recover a forward-pointing tableau. -/
def reflection {s : ℕ} (M : RKTableau s) : RKTableau s where
  A i j := M.b j - M.A i j
  b j   := M.b j
  c i   := (∑ j : Fin s, M.b j) - M.c i
```

This is a fully constructive (computable) definition; no `noncomputable`
needed, no `Classical.choose`. Be sure to write `(∑ j : Fin s, M.b j)` (not
`Finset.sum Finset.univ`) so that the term is a plain real expression.

### Step 3 — prove `thm:343A`

```lean
/-- Butcher §343 Theorem 343A — the reflection is an involution. -/
theorem reflection_reflection {s : ℕ} (M : RKTableau s) :
    M.reflection.reflection = M := by
  cases M with
  | mk A b c =>
    simp only [reflection]
    refine ⟨?_, ?_, ?_⟩
    · funext i j; ring
    · funext j; rfl
    · funext i
      show (∑ j : Fin s, b j) - ((∑ j : Fin s, b j) - c i) = c i
      ring
```

Some uncertainty around the exact extensionality shape:

* `RKTableau` is a `structure` with three fields `A`, `b`, `c`. After
  `cases M with | mk A b c => …`, the goal becomes
  `{ A := …, b := …, c := … } = { A := A, b := b, c := c }`. Either
  `RKTableau.mk.injEq.mpr ⟨_, _, _⟩` or `refine ⟨?_, ?_, ?_⟩` (under
  `mk.injEq` rewriting) should close this. If neither does, the worker
  should use `lean_multi_attempt` at the goal position with these candidates:
  ```
  ["rfl", "ext", "ext i j",
   "apply RKTableau.mk.injEq.mpr",
   "constructor", "refine ⟨?_, ?_, ?_⟩",
   "obtain ⟨A, b, c⟩ := M; rfl",
   "show _ = _; rfl"]
  ```
* `funext` on `Fin s → Fin s → ℝ` may need `funext i; funext j` (two calls)
  rather than `funext i j` — `lean_multi_attempt` will reveal the right
  form.

If the structural equality is fiddly, an alternative shape is to prove
field equality piecewise as three `rfl`-lemmas, then combine using a
single structure-literal rewrite:

```lean
theorem reflection_A_apply (M : RKTableau s) (i j : Fin s) :
    M.reflection.A i j = M.b j - M.A i j := rfl

theorem reflection_b_apply (M : RKTableau s) (j : Fin s) :
    M.reflection.b j = M.b j := rfl

theorem reflection_c_apply (M : RKTableau s) (i : Fin s) :
    M.reflection.c i = (∑ j : Fin s, M.b j) - M.c i := rfl
```

These three `rfl`-lemmas are the API surface; the involution then follows
by a structure-literal reconstruction or by `RKTableau.ext` (if such a
lemma exists — check with `lean_local_search "RKTableau.ext"`; structures
get an auto-generated `.mk.injEq` lemma but not always `.ext`).

### Step 4 — non-vacuous witness

CLAUDE.md requires "at least one concrete witness/instance in the same
cycle" for new definitions. Provide either:

(a) The implicit midpoint method (a 1-stage method that **is** its own
reflection — a *symmetric* method). Define
```lean
def implicitMidpoint : RKTableau 1 where
  A := fun _ _ => (1/2 : ℝ)
  b := fun _   => 1
  c := fun _   => 1/2
```
Then prove `implicitMidpoint.reflection = implicitMidpoint`. Note: this is
*not* an instance of `reflection_reflection` per se (which says any
method's double-reflection equals itself); it is an additional fact
specifically about the symmetric method. It demonstrates that
`reflection` has fixed points.

(b) The 1-stage `RKTableau.explicitEuler` (already in cycle 017's
infrastructure): show that `RKTableau.explicitEuler.reflection.reflection
= RKTableau.explicitEuler` directly via `reflection_reflection`. This is
trivial (just an instance of the main theorem) and demonstrates that the
infrastructure works on a known concrete tableau.

**Recommendation: do (a) AND (b).** (a) gives the more interesting
"reflection has a fixed point" witness; (b) takes one line and confirms
the involution works on `explicitEuler`. Total cost: ~10 lines.

If the `Fin 1`-sum unfolding for (a) is fiddly, defer (a) to cycle 024 and
ship just (b) — that still satisfies the "concrete witness" rule for the
new `reflection` definition.

### Step 5 — pre-commit checklist

After verifying the file builds, run the CLAUDE.md pre-commit checklist:

1. **Sorry scanner**: `rg '\bsorry\b' OpenMath/` — must be empty.
2. **Tautology scanner**: `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/`
   — must be empty.
3. **Single-file build**:
   `lake env lean OpenMath/Chapter3/Section343.lean` — must exit cleanly.
4. **Full build**: `lake build` — must succeed.
5. **Axiom check**: `#print axioms` for the new `reflection` definition,
   `reflection_reflection` theorem, and the witness — must show only
   `[propext, Classical.choice, Quot.sound]` (or even just `[]` if the
   constructive definition avoids choice).

### Step 6 — update bookkeeping

* `extraction/formalization_data/lean_status.json`: set the
  `thm:343A` row to:
  ```json
  {
    "id": "thm:343A",
    "status": "formalized",
    "lean_file": "OpenMath/Chapter3/Section343.lean",
    "lean_symbol":
      "OpenMath.Chapter3.Section343.reflection_reflection",
    "notes": "Reflection defined component-wise per Butcher §343; involution by ring."
  }
  ```
  (Use the existing schema — open the file and follow the row format
  already present for cycle 022's entries. The `lean_symbol` may instead
  live in `OpenMath.Chapter3.Section312.RKTableau` if you place the theorem
  there; pick whichever namespace you used and report it accurately.)
* `plan.md`: flip the `thm:343A` row from `[ ]` to `[x]`. Increment the
  Chapter 3 progress counter (was "23/175 done"; should become 24/175 if
  this cycle delivers `thm:343A` only).

## Faithfulness checklist (run these as you go)

For `def RKTableau.reflection` (new definition of a named concept —
"reflection" / "adjoint method"):

- [ ] Quote Butcher §343 (raw text `ch03.txt` lines 5021–5033 give the
      tableau form; lines 4980–5005 give the derivation).
- [ ] Confirm component-wise formulas match: `â_{ij} = b_j - a_{ij}`,
      `b̂_j = b_j`, `ĉ_i = (Σ_j b_j) - c_i`. Note the `ĉ` formula uses
      `Σ b_j` (not 1) — under consistency `Σ b_j = 1`, but def:343 doesn't
      assume consistency. **Faithfulness flag: do NOT silently substitute
      `1` for `Σ b_j`** in the `c` field of `reflection`. Document this in
      the docstring.
- [ ] Definition-smuggling check: the textbook calls this the "reflection"
      and gives an explicit formula. Our Lean term matches that formula
      verbatim (modulo Lean syntax). No characterisation theorem is being
      smuggled in.

For `theorem reflection_reflection`:

- [ ] Tautology check: conclusion `M.reflection.reflection = M` does not
      appear among hypotheses (no hypotheses in this signature). **Pass.**
- [ ] Identity check: proof is `cases ⋯; ⟨ring; rfl; ring⟩` — substantive
      computation, not `exact h`. **Pass.**
- [ ] Hypothesis-strength check: only `M : RKTableau s` is needed, and the
      textbook hypothesis "given a Runge–Kutta method" matches. **Pass.**
- [ ] Absent-theorem check: any `-- the proof of XYZ is by ring` comments
      should be backed by an actual proof. **Pass** as long as you don't
      promise auxiliary lemmas you don't write.

For `def implicitMidpoint` (if you choose the (a) witness):

- [ ] Quote Butcher §371 (raw text `ch03.txt` lines 8320–8325): "the
      implicit mid-point rule" with `b_1 = 1`, `c_1 = a_{11} = 1/2`.
- [ ] Confirm tableau: `A = (1/2)`, `b = (1)`, `c = (1/2)`.
- [ ] Note: cycle 023 does NOT prove `implicitMidpoint` is symplectic
      (def:370A is not in scope this cycle). The witness exists only to
      demonstrate that `reflection` is a non-trivial transformation with a
      meaningful fixed point.

## What NOT to do this cycle

- **Do NOT pursue `thm:381G`.** Per the deviation justification above —
  multi-cycle scope. If you want to do scoping work for `thm:381G`, write
  an issue file in `.prover-state/issues/thm_381G_scoping.md` describing
  the partition-algebra-Ã=A subgoals, but **do not** start writing Lean
  code for them this cycle.
- **Do NOT pursue `def:381F`.** Blocked on `reducedMethod` construction
  (`.prover-state/issues/reduced_method_deferred.md`). Defer until that
  resolves.
- **Do NOT formalize `def:370A` or `def:357B`** this cycle. Both involve
  the matrix `M = diag(b)A + A·diag(b)^? - bb^T` and Butcher's literal
  formula appears to have a transpose ambiguity (the standard symplectic
  condition is `m_{ij} = b_i a_{ij} + b_j a_{ji} - b_i b_j`, but Butcher's
  literal `diag(b)A + A·diag(b) - bb^T` gives `(b_i + b_j) a_{ij} - b_i b_j`
  — the formulas agree only when `s = 1`, and disagree for the Gauss-2
  method which is symplectic in the standard sense). This is a
  **faithfulness divergence** that needs careful resolution and should not
  be rushed into. If you want to start `def:370A` or `def:357B`, that's a
  separate planner decision for a future cycle.
- **Do NOT raise `maxHeartbeats`.** CLAUDE.md is explicit. The
  `reflection_reflection` proof is `ring` — it will not blow heartbeats.
- **Do NOT introduce `axiom`/`constant`.** No infrastructure gap forces
  one.
- **Do NOT modify `scripts/autonomous_loop.py`.** Per CLAUDE.md and per
  the cycle-014/015 consultant notes, the scanner's known bugs (D1, D2)
  are the loop maintainer's responsibility and tracked in
  `.prover-state/issues/tautology_scanner_false_positives.md`.
- **Do NOT chase scanner false positives.** The scanner is currently
  clean on the codebase (cycle 022 verified — no `h_*`-named closers
  anywhere). If a new false positive appears, apply the cosmetic rename
  trick (`h_<name>` → `h<name>`) and proceed.
- **Do NOT use Aristotle this cycle.** The proof is so short
  (one structure-extensionality + three `ring` calls) that submitting to
  Aristotle is unnecessary overhead. CLAUDE.md says "submit ~5 jobs per
  cycle in batch" but only when the proofs are non-trivial enough to
  benefit from Aristotle's free compute. Save Aristotle quota for cycles
  where it matters (e.g. when `thm:381G` or §314 work begins).

## Stretch goal (only if `thm:343A` closes in <30 minutes)

If the worker delivers `thm:343A` quickly, an optional stretch is to add
the reflection-tableau API lemmas
(`reflection_A_apply`, `reflection_b_apply`, `reflection_c_apply`) plus
an explicit fixed-point witness for `implicitMidpoint`. These are all
`rfl` — no risk of running over the cycle budget.

**Do NOT extend further** (e.g. into `thm:343B`'s simplifying-assumption
preservation, or into formalizing `B(η)`, `C(η)`, `D(η)`, `E(η,ζ)`).
Those require building out §321's simplifying-assumption framework, which
is a separate multi-cycle effort.

## After the cycle — task results

Write `.prover-state/task_results/cycle_023.md` with the standard sections
(per CLAUDE.md "Task Results Format"):

* **Worked on**: `thm:343A` (reflection involution).
* **Approach**: define `reflection` component-wise; prove involution by
  structure extensionality + `ring`.
* **Result**: SUCCESS / FAILED.
* **Faithfulness check**: per the §"Faithfulness checklist" above.
* **Dead ends**: any `lean_multi_attempt` shapes that didn't work for the
  structure-extensionality goal.
* **Discovery**: anything learned about Lean's `RKTableau` extensionality
  that's worth recording.
* **Suggested next approach**: think hard about cycle 024. Reasonable
  next candidates (in rough priority order):
  - `thm:381G` Φ-only (with proper multi-cycle scoping) — start the
    partition-algebra infrastructure with a clear sorry-decomposition
    plan and an issue file.
  - `def:370A` — once the symplectic-matrix transpose ambiguity is
    resolved (consult the consultant subagent or fetch a second source
    such as Hairer–Wanner Vol. II for the canonical formula).
  - A §300 combinatorial entity (e.g. `thm:302C`'s `An = (n-1)!,
    Bn = n^{n-1}` count formulas), which would require defining `α(t)`
    and `β(t)` as labelling counts — substantial but self-contained
    combinatorial work.

Be honest about what worked and what didn't.
