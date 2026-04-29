# Cycle 026 Results

## Worked on

`def:355A` — Butcher Definition 355A (§355, "Order arrows and the Ehle
barrier", page 264). Encodes:

* the auxiliary function `φ(z) = R(z) · exp(-z)`,
* the *order web* (locus where `φ` is real and positive),
* the *principal order web* (connected component of `0` in the order
  web), and
* *up arrows* / *down arrows* (rays from `0` along which `φ` is
  strictly increasing / decreasing).

New file: `OpenMath/Chapter3/Section355.lean`. New module imported from
`OpenMath/Chapter3.lean`.

## Approach

Followed the planner's primary target (no fallback needed). Pure
sorry-free definition — no Aristotle submission was required. Workflow:

1. Read `extraction/formalization_data/entities/def_355A.json`. Quoted
   the textbook statement verbatim in the file docstring.
2. Designed the Lean encoding around four `def`s:
   `phi`, `orderWeb`, `principalOrderWeb`, plus the predicates
   `IsUpArrow` and `IsDownArrow`. `R : ℂ → ℂ` is left as an explicit
   parameter (no coupling to `RKTableau` this cycle, per planner DO-NOT
   list).
3. Encoded "real and positive" as
   `(phi R z).im = 0 ∧ 0 < (phi R z).re` — the standard rephrasing.
4. Encoded the principal order web with `connectedComponentIn`.
5. Encoded the arrows as predicates on `γ : ℝ → ℂ` requiring `γ 0 = 0`,
   `γ t ∈ orderWeb R` for `t > 0`, and `StrictMonoOn`/`StrictAntiOn` of
   the real value of `φ ∘ γ` on `[0, ∞)`. `t = 0` is excluded from the
   order-web membership clause because Butcher's "ray emanating from
   `0`" includes the origin as an endpoint, but `0 ∈ orderWeb R` only
   when `R(0)` is real and strictly positive (which is not part of the
   definition).
6. Concrete witness: `R(z) := exp(z)` gives `φ(z) = exp(z)·exp(-z)
   = exp(0) = 1`. Proved `phi_exp`, `orderWeb_exp = univ`,
   `0 ∈ orderWeb exp`, and `0 ∈ principalOrderWeb exp` via
   `mem_connectedComponentIn`.

Compiler hiccup: `phi` initially failed code-generation because
`Complex.exp` has no executable code — fixed by marking `phi` as
`noncomputable`.

## Result

SUCCESS.

* `lake env lean OpenMath/Chapter3/Section355.lean` — clean exit.
* `lake build` — clean (2831 jobs).
* Scanner `rg ':=\s*h_\w+\s*$|exact\s+h_\w+\s*$|:=\s*id\s*$' OpenMath/`
  — zero hits.
* `#print axioms` on every new declaration shows only
  `[propext, Classical.choice, Quot.sound]`.

Bookkeeping done:

* `OpenMath/Chapter3.lean` — added `import OpenMath.Chapter3.Section355`.
* `plan.md` — flipped `def:355A` to `[x]` with file path; bumped
  `Progress: 26 / 175` → `Progress: 27 / 175`.
* `extraction/formalization_data/lean_status.json` — set `def:355A`
  to `formalized` with `lean_symbol: OpenMath.Chapter3.Section355.orderWeb`.

No Aristotle submission needed (no `sorry` introduced).

## Faithfulness check

For each new `def` and `lemma` introduced this cycle:

### `phi` (auxiliary, supporting `orderWeb`)

* Textbook source (`def_355A.json`):
  > `φ(z) = R(z) exp(−z)`
* Lean: `noncomputable def phi (R : ℂ → ℂ) (z : ℂ) : ℂ := R z * Complex.exp (-z)`.
* Captures: SAME content. Direct transcription of the textbook formula.

### `orderWeb`

* Textbook source (`def_355A.json`):
  > "The locus of points in the complex plane for which `φ(z) = R(z)
  > exp(−z)` is real and positive is said to be the 'order web' for the
  > rational function `R`."
* Lean: `def orderWeb (R : ℂ → ℂ) : Set ℂ :=
    { z : ℂ | (phi R z).im = 0 ∧ 0 < (phi R z).re }`.
* Captures: SAME content. "Real and positive" is encoded as
  "imaginary part is `0` and real part is strictly positive". Strict
  positivity is the standard reading of "positive" here (vs
  non-negative); the textbook uses this throughout §355.

### `principalOrderWeb`

* Textbook source (`def_355A.json`):
  > "The part of the order web connected to `0` is the 'principal
  > order web'."
* Lean: `def principalOrderWeb (R : ℂ → ℂ) : Set ℂ :=
    connectedComponentIn (orderWeb R) 0`.
* Captures: SAME content. Mathlib's `connectedComponentIn s x` is "the
  connected component of `x` in the subspace topology on `s`" — exactly
  Butcher's "the part of the order web connected to `0`".

### `IsUpArrow`

* Textbook source (`def_355A.json`):
  > "The rays emanating from `0` with increasing value of `φ` are 'up
  > arrows'."
* Lean: predicate on `γ : ℝ → ℂ` requiring `γ 0 = 0`, `γ t ∈ orderWeb R`
  for `t > 0`, and `StrictMonoOn (fun t => (phi R (γ t)).re) (Set.Ici 0)`.
* Captures: SAME content with one explicit reformulation: an "arrow"
  is encoded as a function `γ : ℝ → ℂ` rather than a set, since
  Butcher's "ray emanating from `0`" needs a parameterization to define
  "increasing along it" anyway. Continuity is intentionally NOT
  required at this layer (the §355B-G theorems can refine to continuous
  / smooth arrows on demand). The strict-monotone condition encodes
  "with increasing value of `φ`" — strict to match Butcher's geometric
  picture (an arrow with constant `φ` is not an arrow). The order-web
  membership clause uses `0 < t` rather than `0 ≤ t` because `0` is
  in the order web only when `R(0)` is real and strictly positive,
  which is not part of the definition; for typical RK methods
  (`R(0) = 1`) the two formulations coincide.

### `IsDownArrow`

* Textbook source (`def_355A.json`):
  > "Those emanating from `0` with decreasing `φ` are 'down arrows'."
* Lean: same as `IsUpArrow` with `StrictAntiOn` in place of
  `StrictMonoOn`.
* Captures: SAME content. The two predicates are completely symmetric.

### Lemmas (`phi_exp`, `orderWeb_exp`, `zero_mem_orderWeb_exp`,
`zero_mem_principalOrderWeb_exp`)

These are the concrete-witness lemmas for the exact-flow stability
function `R(z) := exp(z)`. They are not in the textbook explicitly but
discharge the CLAUDE.md non-vacuity requirement: the order web and
principal order web are non-empty for at least one `R` (in fact, the
order web equals `Set.univ` for `R = exp`).

### Tautology / identity / smuggling / hypothesis-strength check

* No theorem conclusion appears verbatim as one of its hypotheses.
* No proof is a single `exact h` re-export of a hypothesis; the four
  witness lemmas all compute on the specific `R = exp`.
* No `class` or `structure` was introduced this cycle — all four
  predicates are `def`s, and the two `Prop`-valued ones (`IsUpArrow`,
  `IsDownArrow`) are predicates on a free curve `γ`, not structures
  with hypothesis-shaped fields.
* No hypotheses anywhere are stronger than the textbook requires; the
  predicates take a free `R : ℂ → ℂ` and a free `γ : ℝ → ℂ`.

## Dead ends

None. The first attempt compiled after fixing the `noncomputable`
issue on `phi`.

## Discovery

* `Complex.exp` is `noncomputable` in Mathlib, so any `def` that uses
  it must also be marked `noncomputable` (or `@[reducible]` won't
  save you — code generation runs anyway). `Complex.exp_add` rewrites
  `exp(x) * exp(y) = exp(x + y)`; combined with `simp` on `z + (-z) = 0`
  and `exp 0 = 1`, the witness `phi_exp` is a one-line proof.
* `mem_connectedComponentIn : x ∈ s → x ∈ connectedComponentIn s x`
  is the canonical entry point for "0 is in the principal order web".
  Found via `loogle "mem_connectedComponentIn"` — the lemma exists
  exactly under that name in `Mathlib.Topology.Connected.Basic`.
* The strategy file's "down arrow of order p at z₀" framing was a
  misreading; the JSON definition does NOT mention `p` or `z₀`. The
  notion of "order p" attaches at `thm:355B`, not `def:355A`. Verified
  against the JSON before encoding, per the strategy's own instruction.

## Suggested next approach

The planner should consider continuing the §35x chain. Two natural
next targets:

1. **`thm:355B`** ("Up/down arrows tangent to specific rays at the
   origin"). This is the first §355 theorem and depends only on
   `def:355A` plus a Taylor-expansion analysis of `R(z) - exp(z)`.
   Likely needs the polynomial-in-`r` expansion machinery (a small
   helper lemma about `Complex.exp z = 1 + z + z²/2 + ...` style; the
   precise Mathlib spelling is `Complex.exp_taylor` / `expSeries`).
   Aristotle is likely to handle the algebra once the structure is in
   place.
2. **`thm:302C`** ("Rooted Tree Enumeration Formulas"). The strategy's
   declared fallback this cycle. Pure combinatorial induction on
   `RootedTree` plus `Nat.factorial` arithmetic. Builds directly on
   `Section301.lean` infrastructure that already exists.

Both are tractable in one cycle. `thm:355B` continues the §35x cluster
that the past three cycles have been building; `thm:302C` is a
side-quest that closes a gap in §302 (combinatorics of rooted trees,
which feeds order-condition theory in §31x and §32x).

The DO-NOT list still applies: avoid `lem:351A`, `thm:351B`,
`thm:353A` (need `(I − zA)⁻¹`), `lem:383A`-`C` (group infrastructure
not built), and the `IsAStable ↔ IsAlphaStable (π/2)` bridge (Real.tan
totalisation trap).
