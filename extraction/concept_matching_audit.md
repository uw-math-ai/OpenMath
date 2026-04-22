# Concept Matching Audit

Comprehensive audit of all 75 concepts in the `introduces` field, identifying
cases where direct string matching fails to find legitimate references.

> **STATUS (2026-04-21):** The polysemy/homonym problem described in §5 is now
> solved at the source. `pipeline/fix_introduces.py` re-extracts every entity's
> `introduces` field via DeepSeek with a peer-aware prompt, producing
> globally-unique qualified names (e.g. `def:142B` introduces
> `"convergent matrix (spectral radius)"`, not bare `"convergent"`).
> A regression assertion in `pipeline/build_formalization_data.py` fails
> Phase 8 if any `uses_concept` edge ever links two entities sharing a
> display name in `statement_names.json`. The chapter-proximity heuristic in
> `extract_references.py` is still present and still used for non-homonym
> alias matches, but it is no longer the disambiguation mechanism for
> polysemic terms — qualified names are.
>
> The match counts in the tables below are from the *bare-name* era and are
> retained as historical reference.

## Summary

| Category | Count | Example |
|----------|-------|---------|
| Long phrases needing strip | 6 | "Lipschitz condition in its second variable" → "Lipschitz condition" |
| pdftotext hyphen-space artifacts | 2 | "P-reducible" → "P -reducible" (with space) |
| LaTeX dash variants | 2 | "Runge–Kutta" vs "Runge--Kutta" vs "Runge-Kutta" |
| Plural forms | 5 | "elementary differential" → "elementary differentials" |
| Zero direct matches | 5 | "contraction mapping principle" (0), needs "contraction mapping" |
| Polysemic concepts (multiple defs) | 7 | "stable" (defs 142A, 403A, 510C) |

## All 75 Concepts with Match Counts

Legend: `full` = exact string match; `→ alias=N` = aliased form found N times
when direct match fails.

### Chapter 1

| Entity | Concept | Full | Alias |
|--------|---------|------|-------|
| def:110A | Lipschitz condition in its second variable | 2 | `Lipschitz condition` = 11 |
| def:110A | Lipschitz constant | 4 | — |
| def:110A | contraction mapping principle | **0** | `contraction mapping` = 1 |
| thm:111A | companion matrix | 4 | — |
| thm:111A | inhomogeneous term | 1 | — |
| def:112A | one-sided Lipschitz condition | 2 | — |
| def:112A | one-sided Lipschitz constant | 2 | — |
| def:142A | stable | 34 | (polysemic; see below) |
| def:142A | power-boundedness | 2 | — |
| def:142B | convergent | 17 | (polysemic) |

### Chapter 3

| Entity | Concept | Full | Alias |
|--------|---------|------|-------|
| def:310A | elementary differential | 1 | `differentials` (plural) = 6 |
| def:312A | internal weights | 1 | — |
| def:312A | derivative weights | 1 | — |
| def:323A | internal order q | 4 | — |
| def:350A | A(α)-stable | 2 | — |
| def:350A | S(α) | 3 | — |
| def:355A | order web | 2 | — |
| def:355A | up arrows | 13 | — |
| def:355A | down arrows | 12 | — |
| def:356A | AN-stable | 3 | — |
| def:356A | irreducibility in the sense of Dahlquist and Jeltsch | 1 | `DJ-irreducibility` = 2 |
| def:356A | DJ-irreducibility | 2 | — |
| def:356B | DJ-reducible | 1 | — |
| def:356B | reduced method | 4 | — |
| def:357A | B-stability | 1 | — |
| def:357B | algebraically stable | 6 | — |
| def:370A | symplectic | 3 | — |
| def:381A | equivalent | 25 | (polysemic) |
| def:381B | Φ-equivalent | 2 | — |
| def:381C | 0-reducible | 2 | — |
| def:381C | 0-reduced method | 1 | — |
| def:381D | P -reducible | 4 | (pdftotext artifact) |
| def:381E | irreducible | 4 | — |
| def:381E | reduced method | 4 | — |
| def:381F | P -equivalent | 2 | (pdftotext artifact) |
| def:388D | C(ξ) | 4 | — |
| def:388F | D(ξ) | 5 | — |

### Chapter 4

| Entity | Concept | Full | Alias |
|--------|---------|------|-------|
| def:402A | convergent | 17 | (polysemic) |
| def:403A | stable | 34 | (polysemic) |
| def:403A | stability | 59 | (polysemic) |
| def:403A | zero-stability | 1 | — |
| def:403A | stability in the sense of Dahlquist | 1 | `stability` = 59 (polysemic!) |
| def:404A | preconsistent | 8 | — |
| def:404B | consistent | 9 | (polysemic) |
| def:406A | local truncation error | 4 | — |
| def:422B | underlying one-step method | 2 | — |
| def:442A | principal sheet | 4 | — |
| def:442A | A-stable | 18 | (polysemic with def:520E) |
| def:451A | G-stable | 2 | — |

### Chapter 5

| Entity | Concept | Full | Alias |
|--------|---------|------|-------|
| def:510A | preconsistent | 8 | (polysemic with def:404A) |
| def:510A | preconsistency vector | 3 | — |
| def:510B | consistent | 9 | (polysemic with def:404B) |
| def:510C | stable | 34 | (polysemic) |
| def:512A | convergent | 17 | (polysemic) |
| def:520A | stability matrix | 8 | — |
| def:520C | stability function | 14 | (polysemic with def:542A) |
| def:520C | stability region | 5 | — |
| def:520C | instability region | 3 | — |
| def:520E | A-stable | 18 | (polysemic with def:442A) |
| def:520F | L-stable | 1 | — |
| def:521A | stability order | 5 | — |
| def:521A | complexity of the stability function | 1 | — |
| def:525A | G-symplectic | 2 | — |
| def:530A | degenerate | 1 | — |
| def:530A | non-degenerate | 3 | — |
| def:530B | order relative to a starting method | **0** | `order` (149) — too generic |
| def:530C | order | 149 | **TOO GENERIC** — most are unrelated uses |
| def:530C | general linear method | 21 | — |
| def:530C | non-degenerate starting method | 1 | — |
| def:530C | order relative to a starting method | **0** | same issue |
| def:542A | stability function | 14 | (polysemic) |
| def:542A | Runge–Kutta stability | 2 | dash-variant |
| def:542A | RK stability | 5 | — |
| def:542A | annihilation conditions | 1 | — |
| def:551A | inherently Runge--Kutta stable | **0** | `--` is LaTeX artifact |

## Special Cases by Category

### 1. Trailing Qualifier Strip

Full phrase too specific; shorter form is actually used:

| Full | Shorter form | Gain |
|------|--------------|------|
| `Lipschitz condition in its second variable` | `Lipschitz condition` | 2→11 |
| `stability in the sense of Dahlquist` | `stability` | 1→59 ⚠ polysemic |
| `contraction mapping principle` | `contraction mapping` | 0→1 |
| `irreducibility in the sense of Dahlquist and Jeltsch` | `irreducibility` | 1→3 |
| `order relative to a starting method` | (no good short form) | 0 |
| `complexity of the stability function` | `stability function` | 1→14 ⚠ polysemic |

**Patterns to strip**: `\sin\s+its\s+\w+\s+variable$`, `\sin\s+the\s+sense\s+of\s.+$`, `\s+principle$`, `\s+relative\s+to.*$`.

### 2. pdftotext Space-Injection in Hyphenated Terms

pdftotext inserts a space before hyphens when the character is a lone letter,
producing `P -reducible` instead of `P-reducible`:

| Concept | Actual text form |
|---------|------------------|
| P-reducible | `P -reducible` (4 matches) |
| P-equivalent | `P -equivalent` (2 matches) |

The `introduces` field has already captured the `P -reducible` form
(with the space) because it was extracted from pdftotext. So the matching
already works. But **future-proofing**: generate both variants.

### 3. Dash Type Variants

| Source | Character | Example |
|--------|-----------|---------|
| pdftotext | en-dash `–` (U+2013) | "Runge–Kutta" (59 matches) |
| LaTeX | double-hyphen `--` | "Runge--Kutta" (converted to en-dash by TeX but raw text has `--`) |
| ASCII | hyphen `-` | "Runge-Kutta" |
| em-dash | `—` (U+2014) | rare |

**Concepts affected**:
- def:542A: `Runge–Kutta stability` (works with en-dash)
- def:551A: `inherently Runge--Kutta stable` (0 matches because `--` isn't in pdftotext output)

**Solution**: generate aliases for all dash variants.

### 4. Plural Forms

| Singular | Plural | Gain |
|----------|--------|------|
| elementary differential (def:310A) | elementary differentials | 1→6 |
| elementary weight (def:312A) | elementary weights | already plural in introduces |
| general linear method (def:530C) | general linear methods | 21→22 |
| method | methods | widespread |
| reduced method | reduced methods | — |
| starting method | starting methods | — |

**Solution**: for concepts ending with common nouns (method, condition,
weight, differential, constant, tree), add the plural `+s` form.

### 5. Polysemic Concepts (multi-definition) — RESOLVED via qualified names

Several bare names are introduced by 2+ entities for genuinely distinct
concepts (e.g. `convergent` is matrix-convergence in Ch.1, LMM-convergence
in Ch.4, GLM-convergence in Ch.5). The previous attempt to handle this with
chapter-proximity disambiguation **silently produced wrong edges** —
e.g. `def:142B → def:402A` via `convergent`, structurally false.

The fix lives in `pipeline/fix_introduces.py` (Phase post-2):
1. **Pass 1** — for every entity, DeepSeek re-extracts `introduces` from
   the full statement with an explicit instruction to qualify each name
   with topical context ("matrix", "linear multistep method", etc.) so it
   is globally unique within a numerical-ODE textbook.
2. **Pass 2** — any term still appearing in 2+ entities after Pass 1 is
   batched with its colliders and DeepSeek is asked to assign mutually
   distinct qualified replacements. Iterates until convergence (≤5 rounds).
3. Results cached by `(entity_id, statement_text_hash)` in
   `raw_text/introduces_cache.json`. Re-runs are free unless underlying
   text changes.

After running, the 8 originally-known homonym groups now have unique
qualified introduces (representative examples):

| Original bare term | def:NNNX | Post-fix qualified name |
|---|---|---|
| `convergent` | def:142B | `convergent matrix (spectral radius)` |
| `convergent` | def:402A | `convergent linear multistep method` |
| `convergent` | def:512A | `convergent general linear method (definition)` |
| `consistent` | def:404B | `consistent linear multistep method` |
| `consistent` | def:510B | `consistent general linear method` |
| `reduced method` | def:356B | `reduced method (from DJ-reduction)` |
| `reduced method` | def:381E | `fully reduced Runge–Kutta method` |
| `A-stable` | def:442A | `A-stable linear multistep method` |
| `A-stable` | def:520E | `A-stable general linear method` |

**Belt-and-suspenders**: `pipeline/build_formalization_data.py`
(`_assert_no_homonym_concept_edges`) fails Phase 8 if any `uses_concept`
edge has source/target sharing a `statement_names.json` display name. This
prevents regressions when entities are added later via `extensions/`.

**Do not** add bare polysemic names back to `introduces` — the matcher
will re-create the wrong edges.

### 6. Overly Generic (special handling)

One concept is too generic to be usable:

| Concept | Definition | Matches | Issue |
|---------|------------|---------|-------|
| `order` | def:530C | 149 | "order" is a math-wide term for "order of convergence", "order of method", "order p", etc. Most 149 matches are unrelated to def:530C's specific definition "order relative to a starting method". |

**Decision**: Keep `order` in a small blocklist to prevent spurious edges.
Users can still reference order-related concepts via more specific phrases
(e.g., "order relative to a starting method").

### 7. Substring Collision Prevention

`\bstable\b` matches inside `A-stable` because `-` is a word-boundary char.

**Affected pairs** (all need longest-match-wins):

| Specific form | Generic form | Matches in |
|---------------|--------------|------------|
| A-stable | stable | Runge-Kutta, GLM |
| AN-stable | stable | non-autonomous |
| A(α)-stable | stable | angle |
| L-stable | stable | strong |
| G-stable | stable | one-leg |
| BN-stable | stable | nonlinear |
| algebraically stable | stable | — |
| zero-stability | stability | LMM |
| Runge–Kutta stability | stability | GLM |
| RK stability | stability | GLM |
| inherently Runge-Kutta stable | stable | GLM |

**Solution**: Use `(?<![\w\-])...(?![\w\-])` (hyphen-aware word boundary) AND
longest-match-wins with position consumption (specific forms win over generic).

## Alias Generation Rules (Implementation)

To be added to `_generate_aliases` in `extract_references.py`:

```python
def _generate_aliases(term: str) -> list[tuple[str, bool]]:
    """Returns [(variant, is_full)] where is_full=True means exact introduces name."""
    aliases = [(term, True)]  # Mark full name

    # A. Dash normalization
    for src, dst in [("–", "-"), ("—", "-"), ("--", "-"), ("-", "–")]:
        if src in term:
            aliases.append((term.replace(src, dst), False))

    # B. pdftotext hyphen-space variant (for single-letter prefix)
    m = re.match(r"^([A-Z])-(.+)$", term)
    if m:
        aliases.append((f"{m.group(1)} -{m.group(2)}", False))
    # Reverse: if text has "P -reducible", also try "P-reducible"
    m = re.match(r"^([A-Z])\s+-(.+)$", term)
    if m:
        aliases.append((f"{m.group(1)}-{m.group(2)}", False))

    # C. Trailing qualifier strip
    for pat in [
        r"\s+in\s+its\s+\w+\s+variable\b.*$",
        r"\s+with\s+respect\s+to\b.*$",
        r"\s+in\s+the\s+sense\s+of\b.*$",
        r"\s+principle$",
        r"\s+relative\s+to\b.*$",
    ]:
        stripped = re.sub(pat, "", term, flags=re.IGNORECASE).strip()
        if stripped != term and len(stripped) > 3:
            aliases.append((stripped, False))

    # D. Plurals
    PLURAL_MAP = {
        "method": "methods", "condition": "conditions",
        "differential": "differentials", "weight": "weights",
        "constant": "constants", "tree": "trees", "equation": "equations",
    }
    for sing, plur in PLURAL_MAP.items():
        if term.endswith(sing):
            aliases.append((term[:-len(sing)] + plur, False))

    return aliases
```

## Matcher Rules (Implementation)

To be added/updated in `_find_concept_references`:

1. **Hyphen-aware word boundary**: `(?<![\w\-])` and `(?![\w\-])`
2. **Longest-match-wins**: Sort all potential matches by length descending,
   consume text positions, shorter matches can't overlap
3. **Full-match priority**: If `concept_map[term]` has any `is_full=True` entries,
   only use those; fall back to aliases only when no full match exists
4. **Chapter-proximity disambiguation**: among eligible targets, pick the one
   from the same/nearest-preceding chapter (already implemented)

## Blocklist (minimal)

```python
GENERIC_TERMS = {
    # Articles & pronouns
    "the", "that", "this", "a", "an",
    # Generic noun classes (never introduced as concepts)
    "method", "methods", "problem", "condition", "function",
    "equation", "system", "variable",
    # Specific over-matching concept
    "order",  # def:530C — 149 matches, almost all unrelated
}
# Removed from blocklist (now un-banned):
# "stable", "stability", "convergent", "consistent", "equivalent", "lipschitz"
```
