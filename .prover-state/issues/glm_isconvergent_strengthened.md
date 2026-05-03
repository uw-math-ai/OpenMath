# Issue: `IsConvergent` (def:512A) strengthened with stage-limit clause

## Faithfulness deviation (proposed cycle 098)

The formal predicate `GeneralLinearMethod.IsConvergent`
(`OpenMath/Chapter5/Section512.lean:138`) is strengthened to also
require that the **internal stage** sequence at the diagonal index
converges to `(fun _ => yex(x))` (i.e. all-stages-equal-to-the-exact-
solution at the target time). This addition is option (iii) of
`u_prime_equals_u_bridge.md`.

## Textbook statement (`extraction/formalization_data/entities/def_512A.json`)

> "A general linear method `(A, U, B, V)`, is 'convergent' if for any
> initial value problem … there exist a non-zero vector `u ∈ ℝ^r` and
> a starting procedure `φ` … such that for any `x > x₀`, the sequence
> of vectors `y^{[n]}`, computed using `n` steps with stepsize
> `h = (x − x_0)/n` … converges to `u y(x)`." (Butcher 2008, p. 409)

The textbook constrains only the *output* sequence `Y n n`. Our
strengthening additionally constrains the *stage* sequence at the
final micro-step.

## Proposed shape (cycle 098)

Add a new universally quantified parameter
`Y_int : ℕ → Fin s → ℝ` to the inner conclusion (the stage at the
n-th micro-step of the n-step run), require the stage equation
`Y_int n i = h_n • (∑ A i j · f (Y_int n j)) + ∑ U i j · Y n n j`
as a hypothesis, and add a new conclusion clause
`Tendsto Y_int atTop (nhds (fun _ => yex x))`. The existing
`M.IsGLMSolution` per-step clause remains; the new `Y_int` is a
*separate* stage parameter at the diagonal.

## Why this is needed

`U·u' = 𝟙` (the second half of the `u' = u` bridge) is provably
NOT extractable from the current `IsConvergent` (cycle 097
analysis): the `U` matrix appears only in the per-step *stage*
equation, but the current conclusion constrains only the *output*
diagonal `Y n n`. The strengthening exposes the stage limit so
that, applied to the trivial IVP (`f ≡ 1`, `yex = id`, `x = 1`),
the limit `Y_int n → 𝟙` plus the stage equation forces
`(U *ᵥ u') = 𝟙`. This unblocks `cesaro_residual_tendsto_zero`.

## Mathematical justification

For any well-defined GLM applied to a smooth solution, all
internal stages approximate `yex` at shifted abscissae
`x_n + h · c_i`; as `h → 0` all shifts collapse and every stage
component tends to `yex(x)`. The textbook tacitly uses this in
identifying `u' = u`.

## Downstream consumers

| Consumer | Cycle | Update needed |
|---|---|---|
| `convergent_isStable` (§513) | 093 | Construct `Y_int n := M.U *ᵥ Y n n` (stage-eq trivialised by `f ≡ 0`); ignore stage-limit conclusion |
| `convergence_witness_isVfixed` (§514) | 096 | Construct `Y_int n i := (1/n) • (∑ M.A i ·) + (M.U *ᵥ Y n n) i` (stage-eq holds by definition); ignore stage-limit conclusion |
| `cesaro_residual_tendsto_zero` (§514) | 094 | Stays as `sorry`; the strengthening enables future closure (cycle 099+) |
| §512 sanity helpers | 091 | Unaffected (characterise `IsGLMSolution`, not `IsConvergent`) |

## Cross-references

* `u_prime_equals_u_bridge.md` — option (iii) chosen here.
* `is_convergent_strengthened.md` — LMM precedent for a
  faithfulness-divergent strengthening of `IsConvergent`.
