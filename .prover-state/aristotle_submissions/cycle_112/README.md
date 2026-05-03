# Cycle 112 Aristotle Submissions

Three sub-lemmas decomposing `aux_515D_output_tendsto` (the §515D
capstone helper) into independent pieces:

* `sub_A_recurrence.lean` — abstract per-step recurrence (linear in error
  + quadratic-in-h residual ⇒ closed-form geometric bound).
* `sub_B_gronwall.lean` — specialization of the Section404 helper
  `discrete_gronwall_exp_bound` to the §515 shape (k=1).
* `sub_C_squeeze.lean` — squeeze argument: `δ n` bounded by
  exp-times-tendsto-zero plus const/n ⇒ `δ n → 0`.

Sub-lemma C is also being **hand-proved** in the project file as the
"sure win" sub-lemma (Aristotle is the backup). A and B are the
harder ones where Aristotle is the primary.

## Project IDs

* sub_A: `30a9790c-0f76-4cd1-9e22-88b1d960e40a`
* sub_B: `3b6bb5e0-997c-4886-9196-17def738cc84`
* sub_C: `c70294ce-40f5-470a-a701-00629f6ee088`

Submitted: 2026-05-03 21:25 UTC. Poll once near end of cycle.
