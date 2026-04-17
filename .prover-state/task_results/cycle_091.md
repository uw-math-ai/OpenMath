# Cycle 091 Results

## Worked on
BDF5 zero-stability in `OpenMath/MultistepMethods.lean`, focusing on the quartic `unit_roots_simple` branch.

## Approach
Read `.prover-state/strategy.md`, inspected the existing BDF4 proof pattern, and harvested the available Aristotle outputs before editing.

Submitted a fresh batch of five Aristotle jobs:
- `88eb67cd-008a-4bb3-b7f4-2927409cc2ff` — full `MultistepMethods.lean`
- `0d77c17e-90a3-4791-8fd8-414236787b14` — standalone no-unit-root proof
- `ed67004b-7717-448b-9bb4-bf057f60db1e` — standalone roots-in-disk proof
- `03871885-d900-49e7-b8a2-7d6265ec8a58` — helper lemma for the quadratic case
- `82e5498d-b0d2-481d-9aa5-6d7b1a15287c` — reversed quartic helper

Slept for 30 minutes as required, then checked the results once.

The useful Aristotle artifact was `03871885-d900-49e7-b8a2-7d6265ec8a58`, which gave the clean integer linear-combination proof that
`125 ξ^2 - 100 ξ + 125 = 0` together with the quartic implies `ξ = 5 / 4`.

I incorporated that algebra into a new helper lemma
`bdf5_quartic_eq_five_fourths`, and then simplified the BDF5 `unit_roots_simple`
branch to the intended structure:
- conjugate the quartic on `‖ξ‖ = 1` to get the reversed quartic
- subtract to obtain
  `(ξ - 1) * (ξ + 1) * (125 * ξ ^ 2 - 100 * ξ + 125) = 0`
- rule out `ξ = ±1` directly
- invoke `bdf5_quartic_eq_five_fourths` in the quadratic case
- contradict `‖ξ‖ = 1` using `ξ = 5 / 4`

I did not change the existing `roots_in_disk` branch because it was already filled
in the worktree before this cycle.

## Result
PARTIAL

Code changes were made in `OpenMath/MultistepMethods.lean` and the BDF5
unit-circle branch is now substantially simpler and closer to the planner’s
recommended argument.

Verification was blocked by the local toolchain/cache state:
- `lake env lean OpenMath/MultistepMethods.lean` failed immediately because
  `/tmp/OpenMath-lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean`
  does not exist.
- `lake exe cache get!` failed because the NVMe clang toolchain requires
  `GLIBC_2.29`, which is unavailable on this host.
- Falling back to the elan-managed toolchain did not produce a completed check
  during this cycle.

## Dead ends
- The fresh Aristotle reversed-polynomial job (`82e5498d-...`) collapsed back to
  `grind`, so I did not use it directly.
- The fresh full no-unit-root proof (`0d77c17e-...`) raised heartbeats above the
  project limit and was not incorporated verbatim.
- The fresh roots-in-disk job (`ed67004b-...`) and the full-file job
  (`88eb67cd-...`) were still `IN_PROGRESS` at the single post-sleep check.

## Discovery
- The planner snapshot was stale with respect to the live worktree: both BDF5
  branches were already filled when this cycle started, but the existing
  `unit_roots_simple` proof used a longer cubic/quadratic elimination chain.
- The auxiliary quadratic route from the planner is viable and much shorter once
  the integer linear combination is isolated.
- The current environment has a reproducible verification blocker unrelated to
  the BDF5 proof itself: missing `Mathlib.olean` in the temp lake package tree,
  plus a `GLIBC_2.29` mismatch in the NVMe clang path.

## Suggested next approach
- Fix the local Lake/mathlib cache state first so that `lake env lean` works again.
- Once verification is restored, re-run `lake env lean OpenMath/MultistepMethods.lean`
  and either keep the simplified BDF5 proof or adjust minor syntax issues if any appear.
- Harvest Aristotle jobs `88eb67cd-...` and `ed67004b-...` later only if the
  current `roots_in_disk` branch needs replacement.
