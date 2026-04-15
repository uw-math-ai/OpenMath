# DeepSeek Prompt Library

All DeepSeek API prompts used in the extraction pipeline, documented
for tracking and reuse.

---

## 1. LaTeX Conversion (`convert_to_latex.py`)

**Strategy**: Convert raw pdftotext of a formal statement to proper LaTeX.
One API call per statement. ~$0.11 for 175 statements.

**See**: `extraction/latex_conversion_guide.md` for full constraints and
prompt template.

**Key insight**: Must explicitly ban tikzpicture, tabular, \hline, and
`|` in array column specs to avoid plasTeX crashes.

---

## 2. LLM Reference Extraction (`extract_references_llm.py`) — REDESIGNED

**Strategy (v2)**: Target gets FULL context (complete LaTeX with proof).
Catalog entries are minimized:
- **Named entities** (have `introduces` concepts or a name): one-line summary
- **Unnamed entities** (no concepts, no name): include their LaTeX body (no proof)

This focuses DeepSeek's attention on substantive dependencies rather than
overwhelming it with irrelevant detail.

**Input**:
- Target: full LaTeX body + proof (no truncation)
- Catalog: 174 entities, most condensed to 1 line
**Output**: JSON array of dependency IDs, e.g., `["def:110A", "thm:142C"]`

**Prompt** (system):
```
You are a mathematical dependency analyzer for a Lean 4 formalization
project. Given a target theorem, definition, or lemma along with a catalog
of available prior definitions and theorems, identify which ones are
directly used or required to understand or prove the target.
```

**Prompt** (user):
```
# Target: {kind} {number}: {name}

{full_latex_with_proof}

# Catalog of available definitions and theorems

{catalog}

# Instructions

Identify the MINIMAL set of dependencies directly used by the target above.
Be strict and conservative — include ONLY entities that are:
- Explicitly cited by name or number in the target
- Required to state the target (concepts appearing in the statement body)
- Required to prove the target (results used in the proof)

Do NOT include:
- The target itself
- Entities that merely discuss similar or related concepts
- Entities from the same subsection unless the target explicitly uses them
- Background material or general context

Most theorems have 0-5 direct dependencies. If you list more than 10,
you are probably being too permissive.

Reply with ONLY a JSON array of IDs, e.g., ["def:110A", "thm:142C"].
If no dependencies, reply with: []
```

**Catalog entry formats**:

```
# Named entity (most concise):
- def:110A: introduces "Lipschitz condition in its second variable", "Lipschitz constant"

# Named without concepts:
- thm:212A: Global truncation error bound

# Unnamed entity (include LaTeX body, no proof):
- thm:XXXX:
  \begin{theorem}
  ... LaTeX body ...
  \end{theorem}
```

**Key differences from v1**:
- Target has full context (was 500+800 char truncation)
- Catalog is distilled (was 150 char snippets for all 175 entities)
- Stricter "MINIMAL set" wording with explicit "most have 0-5 deps" hint
- LaTeX format (was raw pdftotext)

**Result**: ~47% size reduction per call, much fewer false positives.

**Cost**: ~$0.21 for 175 statements.

---

## 3. Missing Context Extraction (`extract_context.py`)

**Strategy**: For each statement, send it + 1500 chars of preceding
subsection text. Ask DeepSeek to identify variables, equations, and
setup notation needed to understand the statement.

**Input**: Preceding text (1500 chars) + statement text (1000 chars)
**Output**: JSON with `variables`, `equations`, `preamble` fields

**Prompt** (system):
```
You are a mathematical context analyzer for a formalization project.
Your task is to identify what external context is needed to understand
a formal statement from a textbook.
```

**Prompt** (user):
```
Below is a formal {kind} from Butcher's "Numerical Methods for ODEs",
along with the text that precedes it in the same subsection.

**Preceding text (last ~1500 chars before the statement):**
{preceding_text}

**{KIND} {number}:**
{statement_text}

Identify what context from the preceding text is needed to fully
understand this statement. Return a JSON object with:

1. "variables": list of {"name": "f", "definition": "f : [a,b] × R^N → R^N"}
2. "equations": list of {"tag": "100a", "content": "y'(x) = f(x, y(x))"}
3. "preamble": 1-3 sentence summary of essential setup/notation

If self-contained: {"variables": [], "equations": [], "preamble": ""}

Output ONLY valid JSON, no markdown fences, no explanations.
```

**Cost estimate**: ~$0.15 for 175 statements.

---

## 4. Concept/Term Extraction (`fix_introduces.py`)

**Strategy**: For definitions/theorems missing the `introduces` field,
ask DeepSeek to identify the named concepts/terms that the statement
formally defines or introduces.

**Input**: LaTeX body (1500 chars)
**Output**: JSON array of strings, e.g., `["Lipschitz condition", "Lipschitz constant"]`

**Prompt** (system):
```
You are a mathematical terminology extractor. Given a definition or theorem
from a numerical methods textbook, identify the named concepts or terms
that it introduces or formally defines.
```

**Prompt** (user):
```
Below is {kind} {number} from Butcher's "Numerical Methods for ODEs":

{latex_body}

List the specific named concepts or terms that this {kind} introduces or
formally defines. These are typically:
- Terms in single quotes ('term' or 'term')
- Terms in italic emphasis (\emph{term} or \textit{term})
- Proper names introduced by phrases like "is called X", "is said to be X",
  "we define X", "is symplectic", "is L-stable"

Do NOT include:
- General mathematical objects used but not defined (variables like f, y, A)
- Named theorems or references to other results
- Generic descriptive words (method, property, condition)
- Words that are used but not being defined here

Return a JSON array of strings. If none, return [].
Example: ["Lipschitz condition", "Lipschitz constant"]
```

**Two-method approach**:
1. Method A: Parse `\emph{}` and `\textit{}` directly (zero cost, catches 6-10 cases)
2. Method B: DeepSeek for definitions still missing after Method A (~$0.004)

**Result**: 45/45 definitions now have `introduces` (was 34/45).

**Cost**: ~$0.004 for ~10 DeepSeek calls.

---

## 5. Statement Name Inference (`extract_names.py`)

**Strategy**: For statements without an explicit name or subsection-based name,
use DeepSeek to propose a concise descriptive name from the mathematical content.

**Input**: Statement text (800 chars) + subsection title
**Output**: 3-8 word descriptive name (plain text)

**Prompt** (system):
```
You are a mathematical terminology expert. Given a formal statement from
a numerical methods textbook, propose a concise descriptive name.
```

**Prompt** (user):
```
Propose a short descriptive name (3-8 words) for this {kind} from Butcher's
"Numerical Methods for ODEs". The name should capture the main result or
concept, not restate the number.

**Subsection**: {subsection_title}

**{KIND} {number}**:
{statement_text}

Examples of good names:
- "Global truncation error bound"
- "Convergence iff consistency and stability"
- "Dahlquist equivalence theorem"
- "Existence and uniqueness of solutions"

Respond with ONLY the name, no punctuation, no quotes, no "Theorem" prefix.
```

**3-tier resolution strategy**:
1. Tier 1: use `introduces` field (35 statements, zero cost)
2. Tier 2: use subsection title for primary statements (60 statements, zero cost)
3. Tier 3: DeepSeek inference (80 statements, ~$0.02)

**Cost**: ~$0.02 for 80 statements.

---

## General Prompt Design Principles

1. **Structured output**: Always request JSON with a specific schema.
   Include an example in the prompt.
2. **Negative instructions**: Explicitly say what NOT to include
   (prevents hallucination of false dependencies).
3. **Length limits**: Keep input text under ~2000 chars per field to
   control costs and reduce noise.
4. **Temperature**: Use 0.1 for all extraction tasks (faithful, not creative).
5. **Incremental saves**: Always save after each API call so `--resume` works.
6. **Banned patterns**: For LaTeX output, always ban tikz/tabular/hline
   (see latex_conversion_guide.md).
