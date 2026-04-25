# Cycle 385 Results

## Worked on
Split Adams-Bashforth and Adams-Moulton method declarations out of
`OpenMath/MultistepMethods.lean` into the new module `OpenMath/AdamsMethods.lean`.

Moved declarations:
- Definitions: `adamsBashforth2`, `adamsMoulton2`, `adamsBashforth3`,
  `adamsMoulton3`, `adamsBashforth4`, `adamsMoulton4`, `adamsBashforth5`
- Consistency / explicitness / implicitness:
  `adamsBashforth2_consistent`, `adamsBashforth2_explicit`,
  `adamsMoulton2_consistent`, `adamsMoulton2_implicit`,
  `adamsBashforth3_consistent`, `adamsBashforth3_explicit`,
  `adamsMoulton3_consistent`, `adamsMoulton3_implicit`,
  `adamsBashforth4_consistent`, `adamsBashforth4_explicit`,
  `adamsMoulton4_consistent`, `adamsMoulton4_implicit`,
  `adamsBashforth5_consistent`, `adamsBashforth5_explicit`
- Order theorems:
  `adamsBashforth2_order_two`, `adamsMoulton2_order_three`,
  `adamsBashforth3_order_three`, `adamsMoulton3_order_four`,
  `adamsBashforth4_order_four`, `adamsMoulton4_order_five`,
  `adamsBashforth5_order_five`
- Zero-stability theorems:
  `adamsBashforth2_zeroStable`, `adamsMoulton2_zeroStable`,
  `adamsBashforth3_zeroStable`, `adamsMoulton3_zeroStable`,
  `adamsBashforth4_zeroStable`, `adamsMoulton4_zeroStable`,
  `adamsBashforth5_zeroStable`

## Approach
Performed a pure cut-and-paste extraction of the Adams blocks, preserving the
existing root-level declaration names from the live source. Added
`import OpenMath.AdamsMethods` to `OpenMath/DahlquistEquivalence.lean`, the only
downstream Lean consumer found by `rg "adamsBashforth|adamsMoulton" --type lean`.

Updated `plan.md` so Section 1.2 points Adams methods at
`OpenMath/AdamsMethods.lean` and the AM5 current target names the new file.

Aristotle was not applicable for this pure file-split refactor, so no Aristotle
jobs were submitted.

## Result
SUCCESS.

Line counts after split:
- `OpenMath/MultistepMethods.lean`: 2631 lines
- `OpenMath/AdamsMethods.lean`: 390 lines
- `OpenMath/DahlquistEquivalence.lean`: 605 lines

No proofs were modified; the moved proof bodies are unchanged. Only module
placement, a new module docstring/header, the Dahlquist import, and plan text
were changed.

Verification:
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/MultistepMethods.lean`
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/AdamsMethods.lean`
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake env lean OpenMath/DahlquistEquivalence.lean`
- `PATH=/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH lake build`

All passed. I also ran `lake build OpenMath.MultistepMethods` and
`lake build OpenMath.AdamsMethods` between individual `lean` checks to refresh
stale `.olean` files for imports.

## Dead ends
The first `lake env lean OpenMath/AdamsMethods.lean` attempt reported duplicate
Adams declarations because the imported `OpenMath.MultistepMethods` `.olean`
still contained the pre-split declarations. Rebuilding `OpenMath.MultistepMethods`
refreshed the artifact and resolved the duplicate-declaration errors.

## Discovery
The live source exports Adams method declarations at root level, not under
`namespace LMM`; `#check LMM.adamsBashforth2` fails while `#check
adamsBashforth2` succeeds. The split preserves these existing names to avoid
renaming downstream declarations.

## Suggested next approach
Cycle 386 should add AM5 in `OpenMath/AdamsMethods.lean`, reusing the AB5
zero-stability proof shape after re-checking the live consistency signs.
