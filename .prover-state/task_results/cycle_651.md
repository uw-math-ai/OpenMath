# Cycle 651 Results

## Worked on
§521 — `LMM.bdf4_toGLM_not_isAStable` in `OpenMath/LMMAsGLM.lean`, the
second negative BDF A-stability transport from classical LMM A-stability
to the GLM embedding.

## Approach
Added the theorem immediately after `bdf3_toGLM_not_isAStable` using the
same BDF iff bridge:

```lean
toGLM_isAStable_iff_of_bdf bdf4 ?hbdf ?hβ
```

The BDF predicate is the direct finite case split:
`fin_cases l <;> simp [bdf4, Fin.last] at hl ⊢`.

For the denominator hypothesis, the concrete BDF4 coefficient is
`bdf4.β (Fin.last 4) = 12 / 25`. After rewriting an assumed
`1 - z * (12 / 25 : ℂ) = 0`, taking real parts gives
`1 - z.re * (12 / 25) = 0`, contradicting `z.re ≤ 0` by `linarith`.
The closing recipe is exactly the BDF3 one:
`congrArg Complex.re`, `simp [Complex.sub_re, Complex.mul_re]`, then
`linarith`.

Followed the sorry-first workflow: first inserted the theorem with the
two bridge side goals as `sorry`, verified that the scaffold compiled,
then closed both goals. Lean LSP confirmed both planned snippets closed
their goals before the final edit.

## Result
SUCCESS — `bdf4_toGLM_not_isAStable` landed with no `sorry`.
`PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean
OpenMath/LMMAsGLM.lean` compiles cleanly.

`PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build` also
completed successfully. It replayed existing modules and emitted
pre-existing linter warnings elsewhere, but no warning or error came
from the new `LMMAsGLM.lean` theorem. A no-live-sorry scan over
`OpenMath/` returned no matches.

Also appended a cycle-history note to `plan.md` under `## Active
Frontier`.

## Dead ends
Aristotle was attempted but did not return a usable project id:

- `submit_directory` on the project timed out during the tool call.
- A smaller `submit_prompt` with the local BDF3 pattern also timed out.

Because no Aristotle job id was returned, there was no result to wait on
or incorporate. The proof was then completed manually from the adjacent
BDF3 theorem and checked with Lean LSP plus `lake env lean`.

## Discovery
BDF4 is a literal copy of the BDF3 negative GLM proof once the last
coefficient is corrected to `12 / 25`. The cycle-650 suggested-next note
mentioned `8 / 25`, but the live `bdf4` definition in
`OpenMath/MultistepMethods.lean` has
`β = ![0, 0, 0, 0, 12/25]`, and the new proof uses the live coefficient.

## Suggested next approach
BDF5 and BDF6 GLM negative A-stability transports should wait until the
classical scalar results `bdf5_not_aStable` and `bdf6_not_aStable` exist.
The BDF iff bridge would make the GLM transports short, but the missing
work is the classical Dahlquist-barrier algebraic certificate for those
higher-order BDF methods, not additional GLM infrastructure.
