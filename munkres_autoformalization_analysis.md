# Analysis: Munkres' Topology Autoformalized in Isabelle/HOL

**Paper**: [arXiv 2604.07455v1](https://arxiv.org/html/2604.07455v1) (April 8, 2026)
**Authors**: Dustin Bryant, Jonathan Julian Huerta y Munive, Cezary Kaliszyk, Josef Urban
**Code**: [JUrban/isa_top_autoform1](https://github.com/JUrban/isa_top_autoform1)
**Date of analysis**: 2026-04-10

## Why this matters for us

This is the closest reference to what we want to build. Same tooling (Claude Code + CLAUDE.md + automated loop), same problem shape (formalize a textbook/reference in a proof assistant), same scale (tens of thousands of lines, zero sorry target). Their pipeline is simpler than ours and they succeeded — 85K lines, 806 results, zero sorry, ~$160 on subscription, one month.

---

## 1. System Architecture

```
tmux loop script
  └── re-issues "Read CLAUDE.md and follow instructions" when agent finishes/stalls
      └── Claude Opus 4.6 (Claude Code, 1M context)
          ├── reads CLAUDE.md (evolving instruction file, 8 revisions)
          ├── reads top1.tex (Munkres' LaTeX source, 7,956 lines)
          ├── edits .thy files (Isabelle theory files)
          ├── runs isabelle build -D . (verification, 5,186 runs)
          ├── runs isabelle process_theories (bulk sledgehammer, 3,266 runs)
          ├── runs isabelle eval_at -t (per-line timing profiler)
          ├── runs isabelle desorry (automated sorry elimination)
          └── git commit (1,152 total commits)
```

That's it. No multi-agent coordination, no planner/evaluator split, no structured state files. Just a tmux script that re-issues the same prompt and a CLAUDE.md that evolved 8 times.

### The Outer Loop

The tmux script monitors the Claude Code session and re-issues `"Read CLAUDE.md and follow instructions"` whenever the agent finishes or stalls. This is described as "the same mechanism used in the Megalodon experiment."

- **626 automated sessions**
- **83.1% of prompts were automated** (the loop re-firing)
- **16.9% were manual interventions** (59 corrections out of 764 total messages)
- Median session duration: **13.0 minutes**
- Mean session duration: **24.5 minutes**
- Max session duration: **263 minutes** (4.3 hours)

### Two-Phase Strategy

- **Phase 1** (ChatGPT 5.2 via Codex CLI, March 2-13): Bulk formalization of all definitions and theorem statements. Proofs left as `sorry`. 268 commits.
- **Phase 2** (Claude Opus 4.6 via Claude Code, March 21 - April 3): Systematic proof development and sorry elimination. 884 commits. Final push: 355 commits over March 30 - April 3.

---

## 2. The CLAUDE.md System (4 versions found in repo)

This is the most interesting part. The CLAUDE.md is not a static document — it's an evolving set of rules, each added in response to a specific observed failure mode. It went through 8 revisions.

### Root `CLAUDE.md` (simplest, earliest)
- Basic: formalize gradually, build early and often, use sorry strategically
- Timeout discipline: "if a tactic touches quantifiers/large disjunctions/many rewrite rules, assume it can explode"

### `etc/CLAUDE_ISA_TOP.md` (statement-only phase)
- "Formalize ALL definitions and statements, NO proofs"
- Every item must cite source: `(** from S48 Lemma 48.1 ... **)`
- No infrastructure lemmas not in the textbook

### `tst/CLAUDE.md` (the evolved working version — most important)

**ABSOLUTE RULE**: New proof code must ONLY use `sorry` initially. No exceptions.

The sorry-first workflow:
1. Write proof structure with `sorry` at every step
2. Build to verify structure compiles
3. Annotate all sorry'd steps with `sledgehammer [timeout = 10]`
4. Run `isabelle process_theories` (bulk, outside session timeout) to collect all ATP suggestions
5. Pick fastest proof per step, replace sorry blocks
6. Only run `isabelle build -D .` for final verification

**Other critical rules**:
- 120-second session timeout (in ROOT file) — "a hard constraint on proof complexity" that forces decomposition
- Never use blast/auto/simp directly in new proofs — only via sledgehammer suggestions
- Session split: Top0 (Chapters 2-4, cached heap image) + Top1 (Chapters 5-8, incremental)
- Speed optimization: put `sledgehammer [timeout=10]` + sorry on EVERY step of a slow proof, run once, pick fastest alternatives
- "A tactic that sledgehammer reports as '1 ms' can still cause a 100s kernel slowdown" — always verify with `eval_at -t`
- Focus on sections 12-50, skip exercises

### How CLAUDE.md evolved (8 revisions, each from a specific failure)

The paper describes the failure modes that prompted each revision:

| Failure Mode | Occurrences | Rule Added |
|---|---|---|
| Tactic explosion (uncontrolled auto/blast/simp) | 9 | "ABSOLUTE RULE: sorry first, no exceptions" |
| Inefficient tool use (repeated isabelle runs) | 6 | Batch sledgehammer via process_theories |
| Cherry-picking easy goals | 4 | "stop jumping around looking for low hanging fruit; we have to do it all" |
| Resource management (backgrounding heavy processes) | 3 | Never background isabelle processes |
| Slow builds | Multiple | Session split + heap caching |

Quote from the paper: *"how did you again manage to smuggle in uncontrolled slow by calls??? we were through this multiple times"*

---

## 3. Custom CLI Tools

These are the most operationally important artifacts. Built by the agent itself (meta-tooling).

### `isabelle eval_at` (~370 lines Scala)

Per-line evaluation tool. Three modes:
- **State mode**: `isabelle eval_at Foo.thy 42` — shows proof state at line 42
- **Injection mode**: `isabelle eval_at Foo.thy 15 'sledgehammer'` — runs command after line 15
- **Timing mode**: `isabelle eval_at -t Foo.thy [line]` — per-line timing profiler

Automatically derives the correct logic session from theory imports. Generates ML scripts that replay Toplevel transitions.

### `isabelle desorry` (~400 lines Scala)

Automated sorry elimination. Finds all sorry'd steps, runs Sledgehammer on each in parallel, replaces in-place.

Two-phase ML architecture:
- Phase 1 (Pure context): Replays transitions, collects proof states at sorry positions
- Phase 2 (HOL theory context): Runs Sledgehammer concurrently on all collected states
- Communication between phases via global ML refs

Safety: saves `.backup` file before modifying; atomic rename.

### Why these tools matter for us

The sorry-first workflow only works if you can efficiently batch-process sorry's. In Lean 4, the equivalent would be:
- `eval_at` → `lean_goal` + `lean_multi_attempt` (we already have these via lean-lsp MCP)
- `desorry` → No equivalent. We rely on the agent trying tactics one by one, or Aristotle for batch proving. A Lean `desorry` tool that runs `omega`/`simp`/`aesop`/`exact?` on all sorry positions in parallel would be valuable.

---

## 4. State Management

**There is almost none.** Each session starts with "Read CLAUDE.md and follow instructions." The agent discovers state from:

1. **CLAUDE.md** — what to do and how
2. **The codebase** — what's already formalized (read .thy files, grep for sorry)
3. **Git history** — what was recently done (though the paper doesn't mention the agent using git log)
4. **top1.tex** — what the target is

No `plan.md`, no `attempts.md`, no `strategy.md`, no issue tracker. The simplicity is striking.

**What persists between sessions**:
- The .thy files (the formalization itself)
- CLAUDE.md (updated by human ~8 times over the project)
- Git commits (1,152 total)
- Isabelle heap images (cached chapters)

**What doesn't persist**:
- Exploration notes
- Failed attempt memory
- Strategy decisions
- Progress assessments

### How they get away with no inter-session state

Three factors:
1. **Short sessions** (median 13 min) — less context to lose
2. **Clear progress signal** (sorry count) — the agent can always see what's done and what isn't
3. **The CLAUDE.md workflow is self-directing** — "find sorry's, batch-replace via sledgehammer" doesn't need memory of what was tried before because the approach is always the same (sledgehammer everything, decompose failures)

---

## 5. Stuck Detection and Escalation

**Almost none, by design.** The system relies on:

1. **The tmux loop** — if the agent stalls, just re-issue the prompt. Fresh start.
2. **Human intervention** — 59 corrections across the project (16.9% of prompts). Most common:
   - Correcting tactic explosion (9 times)
   - Redirecting from easy goals to hard ones (4 times)
   - Fixing resource management (3 times)
   - Fixing inefficient tool use (6 times)
3. **The sorry-first workflow itself** — if sledgehammer fails a step, decompose into finer `have` blocks and retry. This is a mechanical escalation built into the methodology, not the tooling.

**No evaluator, no planner, no progress scoring, no stuck detection heuristic.** The authors accepted ~17% human intervention rate and found it manageable.

---

## 6. Progress Tracking

- **Git commits**: The primary record. Sorry count and build time tracked in commit messages: `"-- 15 sorry's, 16s"`, `"-- 1 sorry remaining!"`, `"hfst_in + hsnd_in FULLY PROVED"`
- **Sorry count**: Greppable directly from the code
- **Build time**: Tracked via `eval_at -t` and recorded in commits
- **Session log**: 92,524 JSONL records, 1.3 GB compressed. Contains all 50,119 assistant messages, 17,925 bash commands. Analyzed post-hoc, not used during execution.
- **No dashboard or automated reporting** during execution

---

## 7. Key Design Decisions

### Decision 1: Sorry-first workflow (most important)

The LLM writes ONLY proof structure (sorry at every step). ATPs (sledgehammer → blast/metis/simp) handle proof search. The LLM never writes tactics directly.

**Why**: Emerged from "a rather painful evolutionary process." Prevents tactic explosion — the #1 failure mode. The paper notes: "an LLM trained on a modified corpus with proof methods removed would be very useful and likely much better behaved."

**Implication for us**: In Lean 4, this would mean: the agent writes `have h1 : ... := by sorry; have h2 : ... := by sorry; exact sorry` and then tries `omega`, `simp`, `aesop`, `exact?` on each sorry. We partially do this but not as a strict rule.

### Decision 2: Batch proving via process_theories

Instead of running sledgehammer on each sorry one at a time, annotate ALL sorry's with `sledgehammer [timeout=10]`, run `process_theories` once, and collect all suggestions in a single pass.

**Why**: Running sledgehammer serially in a loop wastes hours. A single process_theories run handles everything at once, outside the 120-second session timeout.

**Implication for us**: We don't have an equivalent bulk proving mechanism. `lean_multi_attempt` tests tactics on ONE position. Aristotle proves ONE lemma. A bulk `desorry` for Lean that tries `omega`/`simp`/`aesop`/`exact?`/`decide` on every sorry in a file simultaneously would be a significant capability upgrade.

### Decision 3: No multi-agent, no planner, no evaluator

Just one agent, one loop, one CLAUDE.md. The simplicity is a feature:
- No coordination overhead
- No conflicting state updates
- No agent-to-agent communication bugs
- The human provides the ~17% of interventions that require judgment

**Implication for us**: Maybe we're overengineering with Planner/Worker/Evaluator. Their system worked for 85K lines with just a loop and evolving instructions. The question is whether our math (algebraic geometry, sheaf cohomology) is harder than topology to the point where we need the extra infrastructure.

### Decision 4: 120-second session timeout as hard constraint

Not an Isabelle limitation — a deliberate CLAUDE.md rule. Forces the agent to decompose long proofs into small lemmas.

**Implication for us**: Our `maxHeartbeats 200000` serves the same purpose. Both are "compilation budget" constraints that force modularity.

### Decision 5: Evolving CLAUDE.md as "training"

Each CLAUDE.md revision addresses a specific failure. After 8 revisions, the instruction set was sufficient for 83% automation. The CLAUDE.md IS the control system.

**Implication for us**: Our CLAUDE.md + slash commands serve the same purpose but are more complex. Their simpler approach suggests we might benefit from consolidating our slash commands into a single, well-evolved CLAUDE.md workflow.

### Decision 6: Explicit carrier sets instead of type classes

They chose `is_topology_on` predicates instead of Isabelle's `topological_space` type class. This was pragmatic for the LLM but created "a parallel universe" that doesn't interoperate with Isabelle's library.

**Implication for us**: We use Mathlib's existing type classes (TopologicalSpace, Noetherian, etc.) which is harder for the LLM but produces Mathlib-compatible code.

---

## 8. Results

| Metric | Value |
|---|---|
| Lines of code | 85,472 |
| Definitions | 199 |
| Proved results | 806 |
| Sections covered | 39 (chapters 2-8) |
| Sorry count | 0 |
| Duration | ~24 active days |
| Commits | 1,152 |
| Sessions | 626 (median 13 min, mean 24.5 min) |
| Human interventions | 59 / 764 total prompts (16.9%) |
| API cost (list price) | $8,895 |
| API cost (subscription) | ~$160 |
| Tokens (output) | 2.66M |
| Tokens (cache-read) | 17.2B |
| isabelle build runs | 5,186 |
| process_theories runs | 3,266 |
| File edits | 7,135 |
| File reads | 4,962 |
| Helper-to-Munkres ratio | ~3.1:1 (611 helpers for 195 Munkres results) |

---

## 9. Limitations They Acknowledge

1. **No library integration**: "Parallel universe of definitions" that doesn't interoperate with Isabelle's standard library
2. **LLM never registered automation attributes**: 8,160 manual `unfold` calls — the LLM didn't extend the simplifier
3. **Tactic distribution is non-standard**: 8,879 blast vs 576 auto reflects LLM-specific patterns
4. **Some definitions too weak**: `is_topology_on` defined without requiring T subset P(X)
5. **Missing some characterizations**: Incomplete coverage vs. Munkres' originals
6. **No proof optimization**: Correct but verbose; no compression/golfing pass
7. **Deprecated idioms and duplicate warnings** left uncleaned

---

## 10. Comparison with Our System

| Aspect | Munkres/Isabelle | Aristotle/Lean |
|---|---|---|
| **Proof assistant** | Isabelle/HOL | Lean 4 / Mathlib |
| **LLM** | Claude Opus 4.6 + ChatGPT 5.2 | Claude Opus 4.6 |
| **Outer loop** | tmux script re-issues prompt | Cron / manual `/loop` |
| **Instructions** | Single CLAUDE.md (8 revisions) | CLAUDE.md + 13 slash commands |
| **Session length** | Median 13 min | Variable (minutes to hours) |
| **Multi-agent** | No | No (but considering it) |
| **State between sessions** | None (just the code) | plan.md + critique.md + LOG.md |
| **Stuck escalation** | Human (17%) + decompose sorry | Human + Aristotle external prover |
| **Proof search** | Sledgehammer (ATPs) | Manual tactics + Aristotle |
| **Bulk proving** | `process_theories` + `desorry` | None equivalent |
| **External prover** | Sledgehammer (built-in) | Aristotle (remote API) |
| **Build time control** | Session timeout 120s + heap caching | maxHeartbeats 200000 |
| **Statement guard** | None (CLAUDE.md rule) | None |
| **Scale** | 85K lines, 806 results | ~6K lines, 1 theorem |
| **Human intervention** | 17% of prompts | ~10% of prompts |
| **Cost** | ~$160 (subscription) | Unknown |

---

## 11. What We Should Learn

### Things they got right that we should adopt

1. **Sorry-first as an absolute rule.** Not a suggestion — a hard constraint. The agent writes structure, ATPs fill in proofs. This prevents the #1 failure mode (tactic explosion / spinning on a single sorry for hours).

2. **Batch proving.** Their `process_theories` + `desorry` pipeline tries every sorry in parallel. We should build or adopt something equivalent for Lean — a script that runs `omega`/`simp`/`aesop`/`exact?` on every sorry in a file.

3. **Short sessions.** Median 13 minutes. This naturally avoids context accumulation. The tmux loop just re-fires the prompt. Compare with our concern about context degradation in long `/babysit` loops.

4. **Simple architecture works.** No planner, no evaluator, no multi-agent. Just one agent, one loop, one evolving CLAUDE.md. 85K lines, zero sorry. Maybe we don't need the complexity we're designing.

5. **CLAUDE.md as the control system.** Each revision addresses a specific failure. 8 revisions over the project. The instructions ARE the automation, not the scripting around them.

6. **Build time as a first-class concern.** Session timeouts force decomposition. Heap caching speeds iteration. Build time tracking in every commit.

### Things we do better

1. **Library integration.** We use Mathlib's actual type classes and definitions. They created a parallel universe that doesn't interoperate.

2. **Structured verification.** Our CI pipeline, branch protection, and auto-merge give stronger guarantees than their `quick_and_dirty` mode during development.

3. **External proving.** Aristotle can solve problems that internal tactics can't, which Isabelle's sledgehammer can't always do either.

4. **Code quality.** Our `/critique`, `/simplify`, `/golf` commands produce cleaner, more maintainable code. They acknowledged no optimization pass.

### The big question for our design

Their system succeeded with **17% human intervention and zero inter-session state.** Do we actually need the Planner/Worker/Evaluator/Consultant architecture we've been designing? Or would a simpler system — a Python loop that re-fires a well-crafted prompt, with a good CLAUDE.md and occasional human check-ins via Telegram — be sufficient?

The answer probably depends on:
- **Math difficulty**: Topology is more combinatorial; algebraic geometry / sheaf cohomology may require more strategic planning
- **Target intervention rate**: If we want <5% human intervention, we need the evaluator and consultant. If 15-20% is acceptable, the simple loop may suffice.
- **Session productivity**: Their short sessions (13 min median) work because sledgehammer batch-processes sorry's. If our sessions need to be longer (Aristotle jobs take hours), we need more state management.
