# Issue: `compose_isRKOneStep_iff` — Gap A scoping for thm:382A

**Cycle**: 212 (scoping doc only — no Lean code attempted this cycle).
**Status**: Pre-positions cycle 213+ to implement the structural bridge for thm:382A
(well-definedness of `[·]` on Equivalent classes per Butcher §382).
**Predecessor doc**: `.prover-state/issues/thm_382A_path.md` (cycle 211 — identifies
this as "Gap A").

## 1. Target statement (precise)

The structural identity claimed by Butcher (§382, p. 285): a single step of
`M₁.compose M₂` factors through an intermediate point.

Forward direction (compose → M₁-then-M₂): given `(M₁.compose M₂).IsRKOneStep
f y₀ H y_final` for sufficiently small `H` (Lipschitz `f`), there exists
`y_mid` such that `M₁.IsRKOneStep f y₀ H y_mid` and `M₂.IsRKOneStep f y_mid H
y_final`.

Reverse direction (M₁-then-M₂ → compose): given `M₁.IsRKOneStep f y₀ H y_mid`
and `M₂.IsRKOneStep f y_mid H y_final`, also `(M₁.compose M₂).IsRKOneStep f y₀
H y_final`.

For the textbook (§382), neither smallness nor Lipschitz are explicitly
needed for the *structural* identity — it's a finite-stage algebraic fact.
However, the *forward* direction's `y_mid` is constructed by feeding the
top-block stages of the composite into `IsRKOneStep_exists` (cycle 205), which
*does* need smallness + Lipschitz. The reverse direction is a pure algebraic
assembly with no smallness/Lipschitz needed.

So the cleanest split:

- **Forward** (cycle 213a, ≥50 LOC, *needs Lipschitz + small H*): existential
  extraction of `y_mid` via `IsRKOneStep_exists` on `M₁` at the top-block
  stage tuple of the composite.
- **Reverse** (cycle 213b, ~40 LOC, *no smallness needed*): block-by-block
  Fin.append assembly of the compose stage tuple from `M₁` and `M₂` stage
  tuples.

Both directions can ship in cycle 213 if the LOC budget allows; otherwise
reverse-first is preferred (cleaner, no analysis dependencies).

## 2. C-scaling analysis — RESOLVED

The critical question flagged by `thm_382A_path.md` (Gap A): does one step
of `M₁.compose M₂` at size `H` correspond to (a) two sub-steps at size `H/2`,
or (b) two sub-steps at size `H` each?

**Answer: (b). Both sub-steps run at the same `H`.**

### Derivation (from `compose` def at `Section381.lean:2480`)

The composite output is `y_final = y₀ + H · Σ_i (M₁.compose M₂).b i · f((Y_top
‖ Y_bot) i)`. Since `(M₁.compose M₂).b = Fin.append M₁.b M₂.b`:

```
y_final = y₀ + H · [Σⱼ M₁.b j · f(Y_top j) + Σⱼ M₂.b j · f(Y_bot j)]
        = (y₀ + H · Σⱼ M₁.b j · f(Y_top j))           ← this is y_mid
          + H · Σⱼ M₂.b j · f(Y_bot j)                ← M₂'s contribution
```

Reading the parenthesized line: `y_mid = y₀ + H · Σⱼ M₁.b j · f(Y_top j)`.
This is exactly what `M₁.IsRKOneStep f y₀ H y_mid` requires (cf.
`IsRKOneStep` at `Section381.lean:923-928`): the step size in M₁'s
formula is **`H`**, not `H/2`.

Similarly, the bottom-block stage equations `Y_bot i = y₀ + H · Σⱼ ((M₁.compose
M₂).A (natAdd i) j) · f((Y_top ‖ Y_bot) j)` unfold via cycle 209's
`compose_A_botLeft = M₁.b j` and `compose_A_botRight = M₂.A i j`:

```
Y_bot i = y₀ + H · [Σⱼ M₁.b j · f(Y_top j) + Σⱼ M₂.A i j · f(Y_bot j)]
        = y_mid + H · Σⱼ M₂.A i j · f(Y_bot j)
```

Again, the step size in M₂'s stage equation is **`H`**, not `H/2`.

### Textbook consistency (§382, p. 285)

Butcher writes (382b–e) using the symbol `h` throughout. The first method
takes one step of size `h`: `y₁ = y₀ + h·Σⱼ bⱼ·Fⱼ`, then the second method
takes another step of size `h`: `y₂ = y₁ + h·Σⱼ b̄ⱼ·F̄ⱼ`. The composite
tableau (382a) at "step size `h`" produces `y₂` — i.e. the composite advances
**two h-worth of time in one step**. This is consistent with the bottom-block
abscissas `(Σⱼ bⱼ) + c̄ᵢ = 1 + c̄ᵢ` exceeding `[0, 1]`: under preconsistency
`Σⱼ bⱼ = 1`, the bottom abscissas live in `[1, 2]` — naturally interpretable
as time fractions of a "2h-long step" but expressed in units of h.

**Takeaway for Lean formalization**: the step-size parameter `H` in
`(M₁.compose M₂).IsRKOneStep f y₀ H y_final` is the *same `H`* that appears
in both `M₁.IsRKOneStep f y₀ H y_mid` and `M₂.IsRKOneStep f y_mid H y_final`.
No `H/2` rescaling. Time-axis interpretation is irrelevant for the
*structural* identity — only the algebraic block-equation match matters.

## 3. Proposed Lean signature (cycle 213 entry point)

```lean
/-- *Compose factors through `M₁`-then-`M₂`.* For Lipschitz `f` and step
size `H` sufficiently small, every one-step output of `M₁.compose M₂`
factors through an intermediate point that is a one-step output of `M₁`,
with the final point a one-step output of `M₂` from that intermediate.
Conversely, sequential `M₁` / `M₂` one-step outputs at step size `H` yield
a one-step output of `M₁.compose M₂` at step size `H` (no smallness
required for the reverse direction).

The threshold `H₀` is the M₁-stage smallness threshold from
`IsRKOneStep_exists` (cycle 205), forced by the existential extraction of
`y_mid`. The reverse direction is purely algebraic — see
`compose_of_isRKOneStep` below for the unbounded version. -/
theorem compose_isRKOneStep_iff {s₁ s₂ : ℕ}
    (M₁ : RKTableau s₁) (M₂ : RKTableau s₂)
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N] [CompleteSpace N]
    (f : N → N) (L : NNReal) (hL : LipschitzWith L f) (y₀ : N) :
    ∃ H₀ > (0 : ℝ),
      ∀ H : ℝ, 0 < H → H ≤ H₀ → ∀ y_final : N,
        (M₁.compose M₂).IsRKOneStep f y₀ H y_final ↔
          ∃ y_mid : N,
            M₁.IsRKOneStep f y₀ H y_mid ∧
            M₂.IsRKOneStep f y_mid H y_final
```

For the reverse direction alone (cleaner, no smallness):

```lean
/-- *Reverse direction of `compose_isRKOneStep_iff` (algebraic, no
smallness).* Sequential `M₁`/`M₂` one-step outputs at step size `H`
assemble into a one-step output of `M₁.compose M₂` at the same `H`. -/
theorem compose_of_isRKOneStep {s₁ s₂ : ℕ}
    (M₁ : RKTableau s₁) (M₂ : RKTableau s₂)
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (f : N → N) (y₀ : N) (H : ℝ) (y_mid y_final : N)
    (h₁ : M₁.IsRKOneStep f y₀ H y_mid)
    (h₂ : M₂.IsRKOneStep f y_mid H y_final) :
    (M₁.compose M₂).IsRKOneStep f y₀ H y_final
```

Stage-equation smallness for the *forward* direction comes from feeding the
top-block stage tuple of the composite (which is automatically a fixed point
of `M₁.RKStageMap H f y₀` because the top-block `A` rows are verbatim
`M₁.A` — cycle 209's `compose_A_topLeft`) and matching it against
`M₁.IsRKOneStep_exists`'s witness via cycle 204's
`RKStageMap_fixedPoint_unique`.

## 4. Proof sketch (markdown only — no Lean)

### 4.1 Reverse direction (algebraic, ~40 LOC)

Given:
- `h₁ : M₁.IsRKOneStep f y₀ H y_mid` — unpacks as `⟨Y₁, hY₁_stage, hY₁_out⟩`
  with `Y₁ : Fin s₁ → N` satisfying `Y₁ i = y₀ + H · Σⱼ M₁.A i j · f(Y₁ j)`
  and `y_mid = y₀ + H · Σᵢ M₁.b i · f(Y₁ i)`.
- `h₂ : M₂.IsRKOneStep f y_mid H y_final` — unpacks as `⟨Y₂, hY₂_stage,
  hY₂_out⟩` similarly with `Y₂ : Fin s₂ → N`.

Construct the composite stage tuple:

```lean
set Y_compose : Fin (s₁ + s₂) → N := Fin.append Y₁ Y₂
```

Witness `(M₁.compose M₂).IsRKOneStep f y₀ H y_final` via `⟨Y_compose, ?_, ?_⟩`.

**Goal 1: stage equation `Y_compose i = y₀ + H · Σⱼ (M₁.compose M₂).A i j ·
f(Y_compose j)`** for all `i : Fin (s₁ + s₂)`.

Case-split on `i = Fin.castAdd s₂ i₁` (top block) vs `i = Fin.natAdd s₁ i₂`
(bottom block) via `Fin.addCases`:

- **Top** (`i = Fin.castAdd s₂ i₁`): LHS = `Y_compose (castAdd s₂ i₁) = Y₁
  i₁` (by `Fin.append_castAdd`). RHS unfolds via cycle 209's
  `compose_A_topLeft` and `compose_A_topRight`: the sum splits into
  `Σⱼ₁ M₁.A i₁ j₁ · f(Y₁ j₁) + Σⱼ₂ 0 · f(Y₂ j₂) = Σⱼ₁ M₁.A i₁ j₁ · f(Y₁ j₁)`.
  Combine with `hY₁_stage i₁` to close.
- **Bottom** (`i = Fin.natAdd s₁ i₂`): LHS = `Y_compose (natAdd s₁ i₂) = Y₂
  i₂` (by `Fin.append_natAdd`). RHS unfolds via `compose_A_botLeft = M₁.b j`
  and `compose_A_botRight = M₂.A i₂ j`: the sum is `Σⱼ₁ M₁.b j₁ · f(Y₁ j₁)
  + Σⱼ₂ M₂.A i₂ j₂ · f(Y₂ j₂)`. The first sum equals `(y_mid - y₀)/H` (by
  `hY₁_out` rearranged: `H · Σⱼ M₁.b j · f(Y₁ j) = y_mid - y₀`). Combining
  with `hY₂_stage i₂` (which gives `Y₂ i₂ = y_mid + H · Σⱼ M₂.A i₂ j ·
  f(Y₂ j)`):
  ```
  y₀ + H · (Σⱼ₁ M₁.b j₁ · f(Y₁ j₁) + Σⱼ₂ M₂.A i₂ j₂ · f(Y₂ j₂))
    = y₀ + (y_mid - y₀) + H · Σⱼ₂ M₂.A i₂ j₂ · f(Y₂ j₂)
    = y_mid + H · Σⱼ₂ M₂.A i₂ j₂ · f(Y₂ j₂)
    = Y₂ i₂                                          ← by hY₂_stage i₂
  ```

**Goal 2: output equation `y_final = y₀ + H · Σᵢ (M₁.compose M₂).b i ·
f(Y_compose i)`**.

`(M₁.compose M₂).b = Fin.append M₁.b M₂.b`. The sum splits via `Fin.sum_univ_addCases`
(or whatever Mathlib's name is — likely `Fin.sum_univ_add` or
`Fin.sum_append`; verify with `lean_loogle "Fin.append"` in cycle 213):

```
Σᵢ (Fin.append M₁.b M₂.b) i · f((Fin.append Y₁ Y₂) i)
  = Σᵢ₁ M₁.b i₁ · f(Y₁ i₁) + Σᵢ₂ M₂.b i₂ · f(Y₂ i₂)
```

Then:
```
y₀ + H · (Σᵢ₁ M₁.b i₁ · f(Y₁ i₁) + Σᵢ₂ M₂.b i₂ · f(Y₂ i₂))
  = (y₀ + H · Σᵢ₁ M₁.b i₁ · f(Y₁ i₁)) + H · Σᵢ₂ M₂.b i₂ · f(Y₂ i₂)
  = y_mid + H · Σᵢ₂ M₂.b i₂ · f(Y₂ i₂)               ← by hY₁_out
  = y_final                                          ← by hY₂_out
```

### 4.2 Forward direction (existential, ~70 LOC, smallness + Lipschitz)

Given `(M₁.compose M₂).IsRKOneStep f y₀ H y_final` — unpacks as `⟨Y_compose,
hY_compose_stage, hY_compose_out⟩` with `Y_compose : Fin (s₁ + s₂) → N`.

Set `Y_top := fun i₁ => Y_compose (Fin.castAdd s₂ i₁)` and `Y_bot := fun i₂
=> Y_compose (Fin.natAdd s₁ i₂)`.

**Claim A: `Y_top` is a fixed point of `M₁.RKStageMap H f y₀`.** From the
top-block stage equations of `hY_compose_stage` and cycle 209's
`compose_A_topLeft` / `compose_A_topRight = 0`:

```
Y_top i₁ = Y_compose (castAdd s₂ i₁)
        = y₀ + H · Σⱼ (M₁.compose M₂).A (castAdd s₂ i₁) j · f(Y_compose j)
        = y₀ + H · Σⱼ₁ M₁.A i₁ j₁ · f(Y_compose (castAdd s₂ j₁))
                                          ← top-right is 0, dropping that block
        = y₀ + H · Σⱼ₁ M₁.A i₁ j₁ · f(Y_top j₁)
        = M₁.RKStageMap H f y₀ Y_top i₁
```

**Claim B: under smallness, `M₁`'s fixed-point uniqueness produces `y_mid`.**
Take `H₀ := 1 / (2 · ((L : ℝ) · C₁ + 1))` where `C₁ := Σᵢ Σⱼ |M₁.A i j|`
(the same threshold pattern as cycle 207's `pReduced_equivalent`). Under
`H ≤ H₀`, `M₁.RKStageMap` is contracting (cycle 204's
`RKStageMap_contracting`).

Set `y_mid := y₀ + H · Σᵢ M₁.b i · f(Y_top i)`. Then `M₁.IsRKOneStep f y₀
H y_mid` is witnessed by `⟨Y_top, Claim A, rfl⟩`.

**Claim C: `Y_bot` satisfies `M₂`'s stage equation at base `y_mid`.** From
the bottom-block stage equations of `hY_compose_stage` and cycle 209's
`compose_A_botLeft = M₁.b j` and `compose_A_botRight = M₂.A i j`:

```
Y_bot i₂ = Y_compose (natAdd s₁ i₂)
        = y₀ + H · Σⱼ (M₁.compose M₂).A (natAdd s₁ i₂) j · f(Y_compose j)
        = y₀ + H · (Σⱼ₁ M₁.b j₁ · f(Y_top j₁) + Σⱼ₂ M₂.A i₂ j₂ · f(Y_bot j₂))
        = (y₀ + H · Σⱼ₁ M₁.b j₁ · f(Y_top j₁)) + H · Σⱼ₂ M₂.A i₂ j₂ · f(Y_bot j₂)
        = y_mid + H · Σⱼ₂ M₂.A i₂ j₂ · f(Y_bot j₂)
        = M₂.RKStageMap H f y_mid Y_bot i₂
```

So `Y_bot` satisfies `M₂`'s stage equation at base `y_mid`.

**Claim D: `y_final` matches `M₂`'s output formula at base `y_mid`.** From
`hY_compose_out` and `(M₁.compose M₂).b = Fin.append M₁.b M₂.b`:

```
y_final = y₀ + H · Σᵢ (Fin.append M₁.b M₂.b) i · f(Y_compose i)
       = y₀ + H · (Σᵢ₁ M₁.b i₁ · f(Y_top i₁) + Σᵢ₂ M₂.b i₂ · f(Y_bot i₂))
       = y_mid + H · Σᵢ₂ M₂.b i₂ · f(Y_bot i₂)
```

So `M₂.IsRKOneStep f y_mid H y_final` is witnessed by `⟨Y_bot, Claim C,
rfl⟩`.

Combined: `⟨y_mid, ⟨Y_top, Claim A, rfl⟩, ⟨Y_bot, Claim C, rfl⟩⟩` closes the
forward direction.

## 5. LOC estimate breakdown

| Component | Estimated LOC |
|-----------|---------------|
| Stage-block assembly: `Fin.append_castAdd`, `Fin.append_natAdd`, `Fin.sum_append` | ~10 LOC (mostly Mathlib lookups) |
| Block-sum split lemma (compose-specific helper) | ~30 LOC |
| Reverse direction (Goal 1 + Goal 2 case-splits) | ~40 LOC |
| Forward direction (Claims A–D) | ~50 LOC |
| Smallness threshold construction | ~10 LOC |
| Docstring + housekeeping | ~10 LOC |
| **Total** | **~150 LOC** |

**Multi-cycle risk**: the cycle 211 worker estimated 100–150 LOC and flagged
this as "possibly 2 cycles". Cycle 213 should target the *reverse direction
only* first (~40 LOC, no smallness analysis) as the smaller, cleaner
deliverable. Cycle 214 ships the forward direction.

## 6. Cross-references

- **Cycle 205** (`IsRKOneStep_exists`, line ~1770 of Section381.lean):
  Banach-existence wrapper feeding the forward direction.
- **Cycle 209** (`compose_A_topLeft` / `topRight` / `botLeft` / `botRight`,
  lines 2521–2539; `compose_b_castAdd` / `b_natAdd` / `c_castAdd` /
  `c_natAdd`, lines 2501–2519): block-unfolding simp lemmas.
- **Cycle 204** (`RKStageMap_fixedPoint_unique`, line ~1721): uniqueness of
  fixed points feeding the existential extraction in the forward direction.
- **Cycle 207** (`pReduced_equivalent`, line ~1924): stage-equation
  manipulation pattern — block-split a sum, rewrite via simp lemmas, close
  via `Finset.sum_congr` + `rfl`/`ring`/`smul_comm`. Models the proof
  shape for the reverse direction here.
- **Cycle 207** smallness threshold construction (`refine ⟨1/(2·((L:ℝ)·C+1)),
  …⟩`): models the `H₀` construction for the forward direction.

## 7. Recommended cycle 213 entry point

**Priority sequence**:

1. **P1** (cycle 213 ship target): state both theorems with `sorry` bodies,
   verify the file compiles. **~5 minutes, ~30 LOC of statement-only +
   sorry**.
2. **P2** (cycle 213 ship target): close `compose_of_isRKOneStep` (the reverse
   direction). **~40 LOC of proof**.
3. **P3 stretch** (likely cycle 214): close the forward direction of
   `compose_isRKOneStep_iff`. **~70 LOC of proof**.

If cycle 213 ships P1 + P2 (sorry-first scaffold + reverse direction
proven), the file's sorry count rises to 1 (the forward direction). Cycle
214 closes that sorry. Total scope: 2 cycles of focused work.

## 8. Non-blockers

- **No HEq plumbing**: both directions operate at fixed `(s₁, s₂)`. No
  associativity / heterogeneous-stage shifts are required (those would
  surface in `compose_assoc`, which cycle 210 deferred — see
  `.prover-state/issues/compose_assoc_HEq_plumbing.md`).
- **No new structure / class definitions**: this is a theorem about
  existing infrastructure (`IsRKOneStep`, `compose`).
- **Axiom-clean expected**: the reverse direction uses only algebraic
  identities (Finset.sum manipulations + `Fin.append` definition unfolds);
  the forward direction uses cycle 204/205's analysis machinery, which is
  itself axiom-clean.

## 9. Open questions for cycle 213+ worker

- **`Fin.sum_append` exists?** Likely Mathlib has `Fin.sum_univ_castAdd` /
  `Fin.sum_univ_natAdd` style decomposition. If not, build it as a helper
  lemma (~10 LOC: `Finset.sum_attach` + case-split via `Fin.addCases`).
  Search: `lean_loogle "Fin.append.*∑"` or `"∑.*Fin.append"`.
- **`Fin.append_castAdd` / `Fin.append_natAdd`** are standard. Confirm via
  `lean_local_search "Fin.append"` and `lean_hover_info`.
- **Smallness threshold form**: cycle 207 used `1/(2·((L:ℝ)·C+1))`. For
  the forward direction here, the M₁-only stages need `1/(2·((L:ℝ)·C₁+1))`
  where `C₁ := Σᵢ Σⱼ |M₁.A i j|`. (Smaller threshold than the composite's
  full `C` because only M₁'s rows need to be a fixed point — the
  composite's block structure already handles M₂ via `Claim C` without
  invoking smallness on M₂'s stage map.)

## 10. Why both directions matter

The thm:382A statement `[m₁ · m₂] = [m̂₁ · m̂₂]` requires showing `m₁ · m₂
≡ m̂₁ · m̂₂` (the (382g) reformulation). The Equivalent predicate (def:381A)
is *universally quantified over outputs*: it states `∀ y, y',
(m₁ · m₂).IsRKOneStep f y₀ h y → (m̂₁ · m̂₂).IsRKOneStep f y₀ h y' → y = y'`.

To exhibit the equivalence on a specific f-Lipschitz problem, one direction
unpacks `(m₁ · m₂).IsRKOneStep` into the M₁-then-M₂ form (**forward**), uses
`m₁ ≡ m̂₁` to swap M₁'s output, then re-packs into `(m̂₁ · m̂₂).IsRKOneStep`
(**reverse**).

So both directions are load-bearing for the thm:382A proof. Cycle 214's
thm:382A direct closure cannot proceed with only the reverse direction
alone.
