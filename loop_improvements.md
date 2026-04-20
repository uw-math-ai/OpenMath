# Agentic Loop Improvement Suggestions

Derived from the April 2026 audit of the OpenMath Lean codebase.
Root cause: Lean verifies logical consistency but not mathematical faithfulness.
All existing gates (sorry count, build) pass for tautologies and dishonest definitions.

---

## 1. Extend the `task_results` format with a faithfulness section

Add a mandatory `## Faithfulness check` field to every cycle result:

```markdown
## Faithfulness check
For each new `def` or `theorem`:
- Textbook statement (quoted from `formalization_data/entities/<id>.json`):
  > ...
- Lean statement captures: [same content / weaker / stronger / different]
- If different: justification for divergence
```

The **Planner** should reject cycles where this field is missing or where the worker
claims a definition is "equivalent" without proof.

---

## 2. Add a tautology/vacuity check as a mechanical gate

Before committing, scan for patterns that indicate vacuous proofs:

```python
TAUTOLOGY_PATTERNS = [
    r":=\s*h_\w+\s*$",       # proof is just returning a named hypothesis
    r":=\s*id\s*$",           # proof is identity
    r"exact\s+h_\w+\s*$",    # exact on a direct hypothesis
]
```

For `structure` definitions: after introducing any `structure` with `Prop` fields,
the Evaluator should verify that each field that looks like a conclusion (not an input
assumption) can be independently proved. If not, it must be marked `sorry` with an
explicit comment — not silently placed as a hypothesis.

---

## 3. Worker pre-commit checklist (add to CLAUDE.md)

Add to the **Prove remaining** step:

> **Before committing any `def` or structure:**
> 1. Open `extraction/formalization_data/entities/<id>.json` and quote the textbook statement.
> 2. Confirm the Lean type matches it. If you're using an equivalent reformulation,
>    prove the equivalence explicitly.
> 3. **Check for hypothesis smuggling**: if your structure has a `Prop` field that is
>    supposed to be a consequence (not an input), it must be either proved inline or
>    left as `sorry` with a comment.
> 4. **Check for tautologies**: if the proof of any theorem is a single `exact`,
>    `id`, or returns one of its own hypotheses, this is a red flag — escalate to an issue.

---

## 4. Evaluator prompt additions

The Evaluator currently judges progress by git diff and task results. Add:

```
For each new theorem in the diff:
- Does the conclusion appear verbatim as one of the hypotheses? → flag TAUTOLOGY
- Does a new `def` encode a named mathematical concept (convergence, stability, etc.)?
  If so, does the definition match the textbook's? → flag DEFINITION_MISMATCH
- For new `structure` definitions: are any fields labeled as "consequence" or
  "conclusion" but placed as hypotheses? → flag SMUGGLED_HYPOTHESIS

Score each flag as -1 (regress the progress score).
```

---

## 5. Track "semantic sorry count" separately from `sorry` keyword count

The current VeriRefine gate counts `sorry` keywords. Add a parallel count:

```
semantic_sorry_count = number of theorems whose proofs are vacuous per the above checks
```

Track in `.prover-state/history.jsonl`. A cycle that decreases `sorry` count but
increases `semantic_sorry_count` counts as **no net progress**.

---

## 6. Worker must load formalization data for the target entity

Add to the **Strategy Phase**:

> Before writing any Lean code for entity `<id>`, read:
> - `extraction/formalization_data/entities/<id>.json` — statement, proof, context
> - The `dependencies` list — to verify you are not assuming conclusions from dependencies
>
> The Lean `theorem` statement must be derivable from the `statement_latex` field.
> If you cannot match it, file an issue explaining the gap rather than weakening
> the statement.

---

## 7. Consultant trigger: definition divergence

Currently the Consultant is triggered when the Worker is stuck for ≥4 cycles.
Add a second trigger:

> If the Evaluator flags `DEFINITION_MISMATCH` or `SMUGGLED_HYPOTHESIS`, escalate
> to the Consultant immediately (don't wait 4 cycles). The Consultant's job is to
> answer: "What is the correct Lean formulation of this mathematical concept, and
> how does it differ from what was written?"

---

## Priority order

| Priority | Item |
|----------|------|
| 1 (highest) | #3 — worker pre-commit checklist in CLAUDE.md (zero compute cost, catches every audit finding) |
| 2 | #6 — mandatory formalization data loading before writing Lean |
| 3 | #1 — faithfulness section in task_results |
| 4 | #4 — Evaluator prompt additions |
| 5 | #5 — semantic sorry count in history.jsonl |
| 6 | #2 — mechanical tautology gate (grep/static scan) |
| 7 | #7 — Consultant trigger for definition divergence |

The single highest-leverage change is #3: it costs nothing computationally and directly
addresses every critical issue found in the audit (tautologies, definition smuggling,
axiomatized content, misnamed theorems).
