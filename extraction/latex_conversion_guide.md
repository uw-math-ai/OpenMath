# LaTeX Conversion Guide for LeanBlueprint

Lessons learned from converting 175 formal statements from Butcher's
"Numerical Methods for ODEs" to LaTeX for use with LeanBlueprint/plasTeX.

## plasTeX Constraints

plasTeX (the Python LaTeX processor used by LeanBlueprint) is NOT a full
LaTeX engine. It cannot handle many packages and constructs that pdflatex
supports.

### Banned Environments (cause crashes or render as raw text)
- `tikzpicture`, `tikz`, `pgfplots` — no drawing support
- `figure`, `wrapfigure` — no float support
- `table` — no float support (use inline `array` instead)
- `tabular` — unreliable; use `array` in math mode instead
- `algorithm`, `algorithmic` — no algorithm support
- `verbatim`, `lstlisting`, `minted` — no code listing support

### Banned Commands (strip or replace)
- `\hline`, `\cline{}` — crashes plasTeX; remove from all arrays/tables
- `\toprule`, `\midrule`, `\bottomrule` — booktabs not supported
- `\rowcolor{}`, `\cellcolor{}` — colortbl not supported
- `\caption{}` — only works inside floats (which are banned)
- `\centering` — harmless but useless without floats
- `\draw`, `\node`, `\path` — TikZ commands
- `\multicolumn` — unreliable in plasTeX

### Array Column Specifications
- **No pipe separators**: `\begin{array}{c|c|c}` crashes plasTeX
- Use `\begin{array}{ccc}` instead (no `|` characters)
- This applies to Butcher tableaux: write `\begin{array}{cc}` not `\begin{array}{c|cc}`

### What to Use for Diagrams/Figures
- Replace with a text comment: `% [Figure: description of what it shows]`
- Or describe the diagram in prose

### What to Use for Code/Algorithms
- Use `itemize` or `enumerate` listing the algorithm steps
- Or describe the algorithm in prose

### What to Use for Tables
- Use `array` environment inside math mode (no `|`, no `\hline`)
- Example: `\[\begin{array}{ccc} a & b & c \\ d & e & f \end{array}\]`

## Statement Structure Requirements

### Environment Titles
- Always include `[title]` in `\begin{theorem}[title]`
- plasTeX uses this for section navigation and cross-referencing
- Without it, theorem numbering and page splitting can break
- Example: `\begin{theorem}[212A]` not just `\begin{theorem}`

### Statement Body Length
- Keep statement bodies under ~5000 characters
- plasTeX accumulates state across the document; very large blocks (>10K chars)
  corrupt the parser state for all subsequent environments
- If the original statement is long, keep the core definition/theorem and
  omit extended discussion, examples, remarks, and figures

### Balanced Environments
- Every `\begin{X}` must have a matching `\end{X}`
- Unmatched environments corrupt plasTeX state for the rest of the document
- This is the #1 cause of "Unknown environment" errors downstream

### Proof Environments
- `\begin{proof}...\end{proof}` is supported via amsthm
- Always close proofs properly
- If truncating a long proof, ensure `\end{proof}` is present

## Content Scope Rules

### Only Convert the Statement
- Convert ONLY the formal statement (theorem/definition/lemma body)
- Do NOT include surrounding discussion, examples, or remarks
- Do NOT include tables, figures, or code from the textbook context
- Do NOT append content that appears after `\end{theorem}` in the source

### Proof Scope
- If a proof is included, convert only the proof body
- Omit figures/tables referenced in the proof
- If the proof is very long (>3000 chars), summarize the key steps

## Prompt Template for DeepSeek

```
Convert this {kind} (numbered {number}) from a numerical methods
textbook into LaTeX.

CONSTRAINTS:
1. Wrap in \begin{{{kind}}}[{number}]...\end{{{kind}}}
2. Convert all math notation to LaTeX
3. Do NOT use: tikzpicture, figure, table, tabular, algorithm,
   verbatim, lstlisting, \hline, \cline, or | in array column specs
4. Use \begin{{array}}{{ccc}} for tables (no pipes, no hlines)
5. For diagrams, write: % [Figure: description]
6. Keep the output concise — state the theorem/definition precisely
   but omit extended discussion, examples, and remarks
7. Keep under 3000 characters
8. Output ONLY the LaTeX code, no explanations

Statement text:
---
{text}
---
```

## Prompt Template for Proof Conversion

```
Also convert the proof:

ADDITIONAL CONSTRAINTS FOR PROOFS:
1. Wrap in \begin{{proof}}...\end{{proof}}
2. Same constraints as above (no tikz, tabular, hline, etc.)
3. If the proof references a figure or table, describe it in text
4. Keep under 3000 characters; summarize if necessary

Proof text:
---
{proof_text}
---
```

## Post-Processing Checklist (applied in generate_blueprint.py)

1. Strip content after the last `\end{kind}` or `\end{proof}`
2. Remove any remaining banned environments (`\begin{figure}...\end{figure}`)
3. Strip `\hline`, `\cline`, `\toprule`, `\midrule`, `\bottomrule`
4. Replace `|` in `\begin{array}{...}` column specs
5. Convert `\begin{tabular}` to `\begin{array}` and `\end{tabular}` to `\end{array}`
6. Clean up excessive blank lines
7. Add `[title]` to `\begin{theorem}` if missing
8. Warn (not truncate) if output exceeds 5000 chars — fix at conversion
   time by reconverting with a concise prompt, not by truncation

**No truncation fallback**: Truncating LaTeX mid-stream almost always
creates unbalanced environments that corrupt plasTeX state for all
subsequent statements. Always fix oversized output by reconverting.
