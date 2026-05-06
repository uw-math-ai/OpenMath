# Cycle 148 Aristotle submission

## Project ID
`2c4630b2-2998-4d4a-af88-c2f83fbd9eda` (submitted 2026-05-06T01:18:52 UTC)

## Goal

Close `doublyCompanionMatrix_det_factorization` for **general** `n : ℕ`
— Butcher Theorem 550A in full generality. This is a long-shot
fire-and-forget submission per the cycle 148 strategy:

- Cycle 138 Job A on general-n: cancelled at 24h / 6%.
- Cycle 141 Aristotle general-n attempt: stalled past usefulness.
- Cycle 147 n=5 adjacent attempt: IN_PROGRESS at 5% at last poll.

A hit closes thm:550A entirely; a miss costs zero worker time.

## Files

- `general_n.lean` — self-contained snippet defining
  `doublyCompanionMatrix`, `alphaPoly`, `betaPoly`, **all six**
  closed n=1..6 concrete-`n` proofs verbatim as in-context templates,
  followed by a strong-induction sketch (three attack vectors:
  cofactor expansion, eigenvalue density, `Fin.induction`) and the
  general-`n` `sorry`'d target.

## Polling discipline

Per the cycle 148 strategy: **do NOT poll this project during cycle
148**. A future cycle (149+) may check it once. The single-poll rule
applies (CLAUDE.md / strategy snapshot).
