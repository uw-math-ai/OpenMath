# Autonomous Formalization Loop — Design Analysis

**Date**: 2026-04-07
**Status**: Brainstorming / pre-implementation

## Goal

Automate the human's role in the formalization pipeline. Analysis of the Grothendieck Vanishing project prompts (287 total) shows ~250 were mechanical ("keep going", "look at plan.md"), ~30 were substantive. The substantive ones fall into categories that can be automated:

- **Refusing learned helplessness** ("BUILD IT YOURSELF") → planner instructions + issue tracker
- **Strategy correction** ("decompose hard → easy") → planner reads failed attempts
- **Mathematical correction** (ACC/DCC confusion) → critique + informal consultant
- **Engineering constraints** (heartbeat discipline) → CLAUDE.md rules + mechanical gates

## Prior Art

### Numina Lean Agent ([GitHub](https://github.com/project-numina/numina-lean-agent))

Python harness spawning `claude -p` / `claude -c` sessions. Up to 20 rounds per task.

- **Stuck handling**: Session reset after 2 consecutive token-limit hits. No semantic stuck detection.
- **State**: Files on disk only. `StatementTracker` snapshots theorem signatures and restores mutations.
- **Escalation**: Prompt-level sub-agents in "hard mode" (Coordinator/Blueprint/Sketch/Proof). Mandatory Gemini checkpoints at attempts 0, 2, 4, 8, 16, 32.
- **Accept criterion**: `lake env lean` verification. Statement immutability enforced externally.
- **Key idea**: The `END_REASON` protocol — sole communication channel from agent to harness.

### Archon ([GitHub](https://github.com/frenzymath/Archon))

Bash orchestrator (824 lines) running Plan → Prover(s) → Review cycles, up to N iterations.

- **Stuck handling**: Plan agent reads prover result files, instructed to recognize failure patterns (missing Mathlib, wrong construction, early stopping). No mechanical detection.
- **State**: 7 structured files in `.archon/`: `PROGRESS.md`, `task_pending.md`, `task_done.md`, `task_results/<file>.md`, `USER_HINTS.md`, proof journal, `PROJECT_STATUS.md`.
- **Escalation**: `informal_agent.py` calls Gemini/GPT for proof sketches when stuck.
- **Multi-agent**: Separate Plan/Prover/Review Claude sessions. Up to 8 parallel provers.
- **Key idea**: Structured attempt tracking — each prover writes what it tried and why it failed, planner reads these to avoid re-exploring dead ends.

### M2F / Project Numina ([arXiv 2602.17016](https://arxiv.org/abs/2602.17016))

Two-stage pipeline: Statement Compilation → Proof Repair. Codex CLI with `model_reasoning_effort="high"`.

- **Stuck handling**: Pure budget caps — 10 retries per plan, 21 replans, then abandon. No heuristic stuck detection.
- **State**: Checkpoint JSON (resume cursor) + append-only JSONL history store. Optional history window in prompts.
- **Accept criterion**: **VeriRefine** — patches accepted if and only if sorry/error count strictly decreases. Monotone progress enforced mechanically.
- **Key idea**: Decouple proposal (LLM) from certification (Lean compiler). Strict monotonicity makes the pipeline correct regardless of LLM quality.

### Meta Textbook Formalization ([arXiv 2604.03071](https://arxiv.org/pdf/2604.03071v1))

Swarm of ~30K Claude 4.5 Opus agents formalizing a 500-page textbook. $100K, one week, 130K LOC.

- **Stuck handling**: Provers that can't prove something **file an issue** describing the blocker. Maintainer agents pick up issues and do broader refactoring. Hard timeouts (128-512 turns, 10 PR revision cycles).
- **State**: Git repo IS the state. Issue tracker = directory of plain text files. Each agent reads repo fresh. No persistent memory.
- **Escalation**: Prover → issue → Maintainer (can touch multiple files). Scan agents proactively find global problems.
- **Multi-agent**: 7 roles (Sketcher, Prover, Maintainer, Math Reviewer, Eng Reviewer, Triage, Scan, Progress). Trunk-based git with short-lived branches + PR merge queue.
- **Key idea**: Issue tracker as lightweight structured escalation. Agents self-organize through shared files. "Simulated annealing" — start loose, tighten as project nears completion.

## Comparison Table

| | **M2F** | **Meta Textbook** | **Archon** | **Numina Agent** | **Ours (current)** |
|---|---|---|---|---|---|
| Outer loop | Python pipeline | Orchestrator spawning agents | Bash, Plan→Prover→Review | Python, claude -p/-c | Cron → claude -p |
| Stuck handling | Budget caps + replan | Issue tracker + maintainer agents | Plan agent recognizes patterns | Session reset after 2 LIMITs | Human |
| State passing | Checkpoint + history JSONL | Git repo + issue files | 7 structured files | Files on disk only | plan.md + critique.md |
| Accept criterion | Strict monotone (VeriRefine) | CI + reviewer agents | CI | Statement tracker + verify | CI only |
| Failed attempt memory | Optional history window | None (stateless agents) | `task_results/<file>.md` | None | None |
| Escalation | Replan (same LLM) | Issue → maintainer agent | Informal agent (Gemini/GPT) | Gemini checkpoints | Human |
| Multi-agent | No | 7 roles, ~30K agents | Plan/Prover/Review | Optional sub-agents | Single agent |

## Key Design Decisions for Our System

### Problem 1: Context Accumulation

**Problem**: `/loop 10m /babysit` runs in one session. By cycle 15, the 200K context window is saturated with stale proof states. The agent gets dumber over time.

**Solution**: Python outer loop launches fresh `claude -p --no-session-persistence` sessions. State persists through files on disk, not conversation history. Every cycle gets the full context budget.

All four systems above use this pattern (fresh sessions, file-based state).

### Problem 2: Lost Context Between Fresh Sessions

**Problem**: Fresh sessions don't know what was already tried. The next session will re-explore dead ends (try `exact Sheaf.hom_ext` when it already failed due to universe mismatch, re-discover that Čech cohomology is a dead end, etc.).

**Options considered**:
1. `attempts.md` — Worker self-reports. Problem: relies on faithful self-reporting, grows unboundedly.
2. Git log as memory — Free, but only captures successes (failed attempts don't get committed).
3. Evaluator extracts important bits from worker's full stdout into structured memory.
4. Two-file approach: `attempts.md` (append-only) + `strategy.md` (overwritten each cycle).
5. Archon-style `task_results/<cycle>.md` — each worker writes structured results, planner reads them.
6. Meta-style issue tracker — workers write issues when blocked, maintainer agents resolve them.

**Preferred**: Combination of (5) and (6). Worker writes `task_results/<cycle>.md` with what it tried and why it failed. When genuinely blocked (not just "hard"), it writes an issue file. The planner reads both.

### Problem 3: Getting Unstuck

**Problem**: The agent says "mathlib gap" or "blocked" and spins. Prompts saying "don't do that" are insufficient because the agent genuinely doesn't know what to do.

**Insight**: Stuck detection should NOT be heuristic-based (sorry count, line diff). If a reliable progress heuristic existed, mathematics would be reduced to minimizing it. Progress assessment must be LLM-based.

**Multi-layered approach**:
1. **Worker self-reports** via structured task results + issue files (Meta pattern)
2. **Evaluator** (cheap LLM) reads git diff + task results + history, judges progress, writes strategy for next cycle
3. **Informal consultant** (strong reasoning model via Codex MCP or Gemini) provides mathematical insight when the evaluator judges stuck for N cycles
4. **Mechanical gates** as hard floor: VeriRefine (sorry count can't increase), build must pass, hard budget cap per sorry

### Problem 4: Progress Measurement

**Rejected**: Heuristic metrics (sorry count, lines changed, git diff size). These are too coarse — decomposing 1 sorry into 5 sub-lemmas is progress but sorry count goes up.

**Chosen**: LLM-based evaluation. A cheap model (Haiku) reads the cycle's git diff, task results, and recent history, then judges:
- `progress_score` (-2 to +2)
- `summary` (what happened)
- `stuck_on` (current blocker)
- `strategy_for_next_cycle` (concrete instructions)

The evaluator replaces the human's role of reading session output and saying "you're spinning" or "good, keep going."

## Proposed Architecture

```
autonomous_loop.py (Python, runs via cron or tmux --loop)
│
├── 1. git pull (pick up other agents' work)
│
├── 2. PLANNER (fresh claude -p session)
│   ├── reads: issues/, task_results/, attempts.md, plan.md, critique.md
│   ├── writes: strategy.md (what to work on + how), updated plan.md
│   └── decides: assignments, approach, when to escalate
│
├── 3. WORKER (fresh claude -p session, runs /babysit steps)
│   ├── reads: strategy.md
│   ├── on success: writes task_results/<cycle>.md, commits + pushes
│   ├── on stuck: writes issues/<sorry_name>.md explaining WHY blocked
│   └── on finish: always writes structured results regardless of outcome
│
├── 4. EVALUATOR (haiku, cheap, no tools)
│   ├── reads: git diff, task_results/<cycle>.md, recent history
│   ├── judges: progress score, whether stuck
│   ├── writes: updated attempts.md (compacted memory), progress log
│   └── output: structured JSON for the loop to act on
│
├── 5. ESCALATION (triggered by evaluator judging stuck for N cycles)
│   └── INFORMAL CONSULTANT (codex/gemini, strong reasoning model)
│       ├── reads: stuck sorry context, issue files, attempts history
│       ├── provides: informal mathematical insight, alternative strategies
│       └── writes: issues/<name>_advice.md (consumed by next planner cycle)
│
└── 6. MECHANICAL GATES (enforced by Python, can't be bypassed)
    ├── VeriRefine: sorry count must not increase (auto-revert if regression)
    ├── Build gate: `lake env lean` must pass on all modified files
    └── Budget cap: same sorry stuck for N cycles → force strategy change
```

### File Structure

```
.prover-state/
├── cycle                    # current cycle number
├── history.jsonl            # one JSON record per cycle (evaluator output)
├── strategy.md              # planner's instructions for current cycle
├── attempts.md              # compacted memory of failed approaches
├── run.lock                 # flock to prevent concurrent runs
│
├── task_results/            # per-cycle structured results from worker
│   ├── cycle_001.md
│   ├── cycle_002.md
│   └── ...
│
└── issues/                  # blocker descriptions (Meta pattern)
    ├── isFlasque_filtered_colimit.md
    ├── isFlasque_filtered_colimit_advice.md  # from consultant
    └── ...
```

### Cycle Duration

Don't use fixed-interval cron. Use `--loop` mode where the next cycle starts only after the previous finishes, with a short cooldown (2-5 min). Run in tmux/screen. The lock file prevents concurrent runs regardless.

### Open Questions

- Should the planner and worker be the same Claude session or separate? Separate is cleaner (different responsibilities) but adds latency and cost. Archon separates them; Meta separates them; M2F doesn't.
- How aggressively should VeriRefine revert? Strict monotonicity prevents regression but also prevents speculative refactoring (temporary sorry increase during restructuring). Maybe allow temporary regression if the worker explicitly flags it as "restructuring in progress."
- Should the evaluator be Haiku (cheap, fast) or something stronger? It needs to understand Lean proof structure well enough to judge whether decomposition is progress.
- How to compact `attempts.md` when it gets too long? Periodic summarization by the evaluator? Hard truncation? Sliding window?
- Codex MCP vs Gemini MCP for informal consultation — need to test which gives better mathematical reasoning for algebraic geometry / sheaf cohomology.
