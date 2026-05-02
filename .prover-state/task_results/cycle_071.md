# Cycle 071 Results

## Worked on

* Butcher `thm:405A` — `LinearMultistepMethod.convergent_isStable`
  (`OpenMath/Chapter4/Section405.lean:101`).
* Cycle 071's deliverable: scaffold + 5 helper lemmas in
  `Section404.lean` per the cycle 071 strategy.

## Approach

1. **(submission)** Submitted a single Aristotle job
   (`runningMaxAbs_helpers.lean`, project
   `e72dd934-8435-4249-9354-ca8ac7d102d3`) bundling the four target
   sub-lemmas (`runningMaxAbs_atTop_of_unbounded`,
   `runningMaxAbs_record_above`, `hom_recurrence_const_smul`,
   `unbounded_homogeneous_contra`).
2. **(infrastructure)** Added five new declarations to
   `Section404.lean` (after `stable_consistent_isConvergent`,
   inside the existing `OpenMath.Chapter4.Section404` namespace):
   * `LinearMultistepMethod.runningMaxAbs` (def — running maximum
     of `|y i|` over `i ≤ n`).
   * `LinearMultistepMethod.runningMaxAbs_monotone` (manual: tiny
     `monotone_nat_of_le_succ` + `le_max_left`).
   * `LinearMultistepMethod.runningMaxAbs_ge_abs` (manual: cases on
     `n` + `le_max_right`).
   * `LinearMultistepMethod.runningMaxAbs_atTop_of_unbounded`
     (manual: `Filter.tendsto_atTop_atTop.mpr` + record-then-
     monotone chase).
   * `LinearMultistepMethod.IsHomogeneousSolution.const_smul`
     (manual: `Finset.mul_sum` + `ring`).
   * `LinearMultistepMethod.runningMaxAbs_record_above` (Aristotle).
   * `LinearMultistepMethod.unbounded_homogeneous_contra` (Aristotle).
3. **(scaffold)** Replaced the lone `sorry` at
   `Section405.lean:100` with the full proof structure for
   `convergent_isStable`: `intro y hy; by_contra h_bnd; push_neg`,
   running-max setup using the new helpers, trivial-IVP setup
   `f ≡ 0, yex ≡ 0, x = 1`, application of `hConv`, contradiction
   via `unbounded_homogeneous_contra`.
4. **(stretch closure)** Discharged `hY_props` inside the scaffold
   (initial-data match via `Nat.ceil_natCast`/`one_div_one_div`,
   recurrence via `IsHomogeneousSolution.const_smul` +
   `isLMMSolution_zero_iff`).

## Result

**SUCCESS — scaffold + 5 helpers + 4 of 5 nested sub-claims closed.**
Remaining single `sorry` in the cycle is `hstart_tendsto` inside
`convergent_isStable`, deferred to cycle 072+ (the limit-of-step-
function calculation `Nat.ceil (1/h) → ∞` as `h → 0⁺` is non-trivial
filter chasing and was *not* in cycle 071's planned scope).

* `lake env lean OpenMath/Chapter4/Section404.lean` — clean (no
  errors, no sorry warnings).
* `lake env lean OpenMath/Chapter4/Section405.lean` — clean (one
  expected sorry warning at line 101 for the still-incomplete
  `convergent_isStable`).
* `lake build` — full mathlib + project rebuild succeeds.

Aristotle delivered all four target sub-lemmas in ~30 min. Two were
ported verbatim with minor namespace adjustments
(`runningMaxAbs_record_above`, `unbounded_homogeneous_contra`); the
other two (`runningMaxAbs_atTop_of_unbounded`, `const_smul`) had
already been proved manually with cleaner tactics.

## Faithfulness check

### Helpers (infrastructure, not Butcher entities)

* `runningMaxAbs`, `runningMaxAbs_monotone`, `runningMaxAbs_ge_abs`,
  `runningMaxAbs_atTop_of_unbounded`, `runningMaxAbs_record_above`,
  `IsHomogeneousSolution.const_smul`,
  `unbounded_homogeneous_contra` — these are pure infrastructure
  for `thm:405A`. No formalization-data row exists; no faithfulness
  comparison applicable. Each carries a docstring explaining its
  role in the `thm:405A` proof.

### `LinearMultistepMethod.convergent_isStable` (`thm:405A`)

* Entity ID `thm:405A`; textbook statement (from
  `extraction/formalization_data/entities/thm_405A.json`):
  > A convergent linear multistep method is stable.
* Lean statement: same content. Hypothesis is `M.IsConvergent`;
  conclusion is `M.IsStable`. Verbatim match.
* Hypothesis strength check: only `M.IsConvergent`, matching
  Butcher's text. ✓
* Tautology check: conclusion (`M.IsStable`,
  `∀ y, IsHomogeneousSolution y → ∃ C, ∀ n, |y n| ≤ C`) does *not*
  appear among the hypotheses. ✓
* Identity check: proof is non-trivial (sorry-first scaffold +
  5 helper lemmas). ✓
* Definition smuggling check: `runningMaxAbs` is a generic ℕ-indexed
  helper, not a rebadging of `IsStable` or any Butcher concept. ✓
* Proof-side deviation: the Lean proof follows Butcher's argument
  almost verbatim. The only encoding choices are
  - the recursive `runningMaxAbs` definition (vs. `Finset.sup'`),
  - the step-function `start h i := if 0 < h then ... else 0`
    (vs. continuous extension).
  Both are documented in the theorem's docstring.

### `IsHomogeneousSolution.const_smul`

* Pure linearity statement: if `y` solves the homogeneous
  recurrence, so does `c · y`. Not in the textbook explicitly;
  required as a lemma to recover homogeneity of the rescaled
  sequence `y / ζ_m`. ✓ no entity row.

## Dead ends

None significant. The Aristotle proofs ported cleanly; the only
adjustments were:
* `le_or_lt` → `le_or_gt` (Mathlib renamed).
* `runningMaxAbs_atTop_of_unbounded`'s Aristotle proof used `refine'`
  + nested chains; the pre-existing manual proof was kept (cleaner).
* `unbounded_homogeneous_contra`'s `hζ_monotone` is unused (Aristotle
  derives the positivity-eventual hypothesis from `hζ_atTop` directly);
  underscored to suppress the linter warning.

## Discovery

* **`Nat.ceil_natCast`** discharges `Nat.ceil ((m : ℝ)) = m` for
  `m : ℕ` cleanly; saved boilerplate in `hY_props`.
* **`Filter.eventually_atTop`** combined with
  `hζ_atTop.eventually_gt_atTop 0` gives a positivity threshold for
  ζ in one line — used inside `unbounded_homogeneous_contra`.
* **`Metric.tendsto_atTop`** (vs. `Filter.tendsto_nhds`) gives the
  ε-formulation directly when extracting "from some point on,
  `|f n| < ε`"; preferred over `nhds`-side formulations for ratio
  arguments.
* Aristotle is excellent at "induction + record argument" sub-lemmas
  given a clear goal: `runningMaxAbs_record_above` would have taken
  ~45 LOC manually but Aristotle landed it in one shot.

## Suggested next approach

**Cycle 072 closes `convergent_isStable` by discharging the lone
remaining `hstart_tendsto` sorry.** The argument:

1. Decompose `Tendsto (fun h => start h i) (𝓝 0) (𝓝 0)` into
   left- and right-hand limits via
   `nhds_within_Iic_eq_nhds_within … ⊓ nhds_within_Ici_eq_…`
   (or `tendsto_nhds_iff` + a `cases`/`rcases h ≤ 0`).
2. **Left side** (`h ≤ 0`): `start h i = 0` (the `if` branch is
   `else`), so `Tendsto (fun _ => 0) … (𝓝 0)` by
   `tendsto_const_nhds`.
3. **Right side** (`h > 0`): `start h i = y i.val / ζ ⌈1/h⌉`. As
   `h → 0⁺`, `1/h → ∞`, so `Nat.ceil (1/h) → ∞` (via
   `Nat.ceil_le_ceil` + monotonicity), so `ζ (Nat.ceil (1/h)) → ∞`
   by `runningMaxAbs_atTop_of_unbounded.comp`. Then
   `y i.val / ζ (Nat.ceil (1/h)) → 0` by
   `Filter.Tendsto.div_atTop` + `tendsto_const_nhds`.
4. Glue via `Filter.tendsto_nhds_iff` or
   `nhdsWithin_Ici_le`/`nhdsWithin_Iic_le`.

This is ~30–60 LOC of pure filter chasing. Submit to Aristotle as a
standalone lemma at the start of cycle 072 (the bundled hypotheses
are minimal: `(y i.val : ℝ)`, the `runningMaxAbs y` predicate, and
the unboundedness fact).

After cycle 072 lands `hstart_tendsto`, `thm:405A` is fully closed,
`thm:243A`'s iff packager is fully proven, the cross-chapter
Ch.2→Ch.4 deferral closes, and Section405 has zero sorries. Cycle
073 should pick up Chapter 4 §410 (criteria for order) per the
cycle-072 outlook in the strategy.
