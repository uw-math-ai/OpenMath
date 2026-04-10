# OpenMath Autonomous Formalization Agent — Design Document

**Date**: 2026-04-10
**Target**: 99% automation (human intervention ≤ 1% of prompts)
**Project**: Semi-autonomous formalization of *A First Course in the Numerical Analysis of Differential Equations* in Lean 4 / Mathlib

---

## 1. Background

### What we've built before

**Clawristotle** semi-autonomously formalized two theorems:

| | VML Steady-State | Grothendieck Vanishing |
|---|---|---|
| Lines of code | 10,445 | ~5,800 |
| Duration | 10 days | 8 days |
| Sorry's | 0 | 0 |
| Human prompts | 836 | 287 |
| Substantive human prompts | ~50 (6%) | ~30 (10%) |
| Mechanical human prompts | ~786 (94%) | ~257 (90%) |
| Cost | ~$6,300 | Unknown |
| Architecture | Claude Code + /babysit loop + Aristotle | Same |

In both projects, ~90% of human prompts were mechanical ("keep going", "look at plan.md"). The substantive 10% fell into categories:

1. **Refusing learned helplessness** — "If mathlib is missing something, BUILD IT YOURSELF" (automatable via instructions)
2. **Strategy correction** — "Decompose hard → easy pieces" (automatable via planner)
3. **Mathematical correction** — "The informal proof confuses ACC and DCC" (needs external reasoning)
4. **Engineering constraints** — "Decompose proofs, don't increase heartbeats" (automatable via instructions)
5. **Redirecting from easy goals** — "Stop cherry-picking low-hanging fruit" (automatable via planner)

### Prior art we studied

| System | Key idea we take from it |
|---|---|
| **Archon** | Structured attempt tracking (`task_results/`), Plan/Prover/Review separation, informal agent for mathematical consultation |
| **M2F (Numina)** | VeriRefine — strict monotonicity gate (sorry/error count can't increase). Budget caps per sorry. |
| **Meta Textbook** | Issue tracker as escalation protocol. Prover vs Maintainer roles. Git as state. |
| **Munkres/Isabelle** | Simple architecture works. Short sessions. CLAUDE.md as the control system. Sorry-first workflow. |

See `autonomous_loop_design.md` and `munkres_autoformalization_analysis.md` for full analysis.

---

## 2. Design Principles

### P1: Start simple, add complexity only when the simple thing fails

The Munkres/Isabelle project achieved 83% automation with just a tmux loop and CLAUDE.md. Our Clawristotle achieved ~90% with /babysit + cron. To get to 99%, we add components incrementally — each one justified by a specific failure mode the simpler system can't handle.

### P2: State lives in files, not in the agent's head

Every Claude session starts fresh. Context accumulation is solved by architecture, not by tricks. The agent reads state from disk, works, writes results to disk, and exits. The outer loop manages lifecycle.

### P3: Progress assessment must be LLM-based

Heuristic metrics (sorry count, line diff) are unreliable. Decomposing 1 sorry into 5 sub-lemmas is progress but sorry count goes up. Building Mathlib infrastructure is progress but sorry count doesn't move. Only an LLM can judge whether real progress was made.

### P4: The agent must not be trusted to self-assess stuckness

An agent that's stuck will say "I'm making progress" or "it's a mathlib gap." External evaluation is necessary. The evaluator reads the diff and task results, not the agent's self-report.

### P5: Escalation is structural, not motivational

"Try harder" doesn't work. When the agent is stuck, it needs *different information* (mathematical insight from an external model) or *different scope* (a maintainer that can refactor across files, not just prove within one). Prompt-level admonishments are not escalation.

---

## 3. Architecture

```
┌─────────────────────────────────────────────────────────┐
│                   autonomous_loop.py                     │
│              (Python, runs in tmux/screen)                │
│                                                          │
│  ┌──────────┐   ┌──────────┐   ┌───────────┐            │
│  │ PLANNER  │──▶│  WORKER  │──▶│ EVALUATOR │            │
│  │ (claude) │   │ (claude) │   │  (haiku)  │            │
│  └──────────┘   └──────────┘   └───────────┘            │
│       │              │              │                    │
│       ▼              ▼              ▼                    │
│  strategy.md   task_results/   attempts.md               │
│  plan.md       issues/         history.jsonl             │
│                commits                                   │
│                                                          │
│  ┌─────────────┐   ┌──────────────────────┐             │
│  │ CONSULTANT  │   │   MECHANICAL GATES   │             │
│  │(codex/gemini│   │ • VeriRefine         │             │
│  │ on stuck)   │   │ • build gate         │             │
│  └─────────────┘   │ • budget cap/sorry   │             │
│                     └──────────────────────┘             │
│                                                          │
│  ┌─────────────────────────────────────────┐            │
│  │           TELEGRAM ALERTS               │            │
│  │  progress, stuck warnings, completions  │            │
│  └─────────────────────────────────────────┘            │
└─────────────────────────────────────────────────────────┘
```

### 3.1 The Outer Loop (`autonomous_loop.py`)

A Python script that manages the full lifecycle. NOT a cron job — runs continuously in tmux with a cooldown between cycles. This avoids wasted cron invocations bouncing off the lock and gives natural back-pressure (next cycle starts only when previous finishes).

```
while True:
    git_pull()
    planner_session()       # fresh claude -p
    worker_session()        # fresh claude -p
    evaluator_session()     # fresh claude -p --model haiku
    if stuck:
        consultant_session()  # codex/gemini
    mechanical_gates()
    sleep(cooldown)
```

Each component is a fresh Claude Code session (`claude -p --no-session-persistence`). No context accumulates.

**File lock** prevents concurrent runs (flock). Safe to also have a cron job as a watchdog that restarts the loop if it dies.

### 3.2 The Planner

**Input**: `plan.md`, `critique.md`, `attempts.md`, `issues/`, `task_results/` from last cycle, current sorry list.

**Output**: `strategy.md` — concrete instructions for the worker. What sorry to work on, what approach to use, what NOT to try (based on attempt history).

**Prompt structure**:
```
You are the planner for an autonomous Lean 4 formalization project.

## Current state
[sorry list, recent git log, current strategy.md]

## What was tried recently (DO NOT repeat these)
[contents of attempts.md — compacted failed approaches]

## Open issues (blockers reported by previous workers)
[contents of issues/]

## Task results from last cycle
[contents of task_results/<latest>.md]

## Your job
Write strategy.md with:
1. Which sorry to work on (highest priority, not cherry-picking easy ones)
2. What approach to use (specific, not "try harder")
3. What NOT to try (explicitly list failed approaches from attempts.md)
4. If an issue reports a blocker, assign infrastructure work before proof work
```

**Why a separate planner?** The worker should not decide what to work on. Left to its own devices, it cherry-picks easy goals (observed in both Clawristotle and Munkres). The planner reads the full project state and assigns hard goals first. This replaces the human's role of saying "stop jumping around."

### 3.3 The Worker

**Input**: `strategy.md` from the planner.

**Output**: Code changes (committed + pushed), `task_results/<cycle>.md`, optionally `issues/<blocker>.md`.

Runs the `/babysit` protocol or a subset: `/critique` → `/prove` → `/submit-aristotle` → `/check-aristotle` → `/commit` → `/alert`.

**Critical rules** (encoded in CLAUDE.md and the worker prompt):
- Follow the strategy. Don't freelance.
- If stuck on a sorry, write a structured issue file explaining WHY (not just "it's hard").
- If Mathlib is missing something, build it. "Mathlib gap" is never acceptable as a final answer.
- Never increase maxHeartbeats. Decompose instead.
- Write `task_results/<cycle>.md` before finishing, even if you made no progress. Document what you tried and why it failed.

**Task results format**:
```markdown
# Cycle 47 Results

## Worked on
isFlasque_filtered_colimit (FiniteGeneratorReduction.lean:247)

## Approach
Tried proving via isFlasque_of_injective + filtered colimit preservation.

## Result
FAILED — Gabriel's theorem (filtered colimits of injectives are injective)
is not in Mathlib. Attempted to build it but estimated 500+ LOC.

## Dead ends
- isFlasque_of_injective requires Injective, not just flasque
- CategoryTheory.Limits.colim_map exists but needs HasColimitsOfShape instance

## Discovery
We don't actually need injectivity — only vanishing H^n(colim). Since
injective ⟹ flasque and flasque sheaves have vanishing cohomology,
we might be able to prove flasque-ness of the colimit directly.

## Suggested next approach
Try proving isFlasque_filtered_colimit directly without going through
injectivity. Key lemma needed: filtered colimit of flasque presheaves
is flasque.
```

### 3.4 The Evaluator

**Input**: Git diff, `task_results/<cycle>.md`, `attempts.md`, last N cycle evaluations, worker stdout (truncated).

**Output**: Structured JSON (progress score, summary, stuck assessment, compacted attempt memory).

Runs as a cheap, fast, no-tools session: `claude -p --model haiku --bare --tools "" --json-schema ...`

**What it judges**:
- `progress_score` (-2 to +2): regression / stall / minor / solid / breakthrough
- `summary`: one sentence
- `stuck_on`: what's blocking, or empty
- `strategy_recommendation`: what the planner should consider next cycle
- `attempts_update`: new entries for attempts.md (compacted from task_results)

**What counts as progress**:
- Closing a sorry = +1 or +2
- Decomposing into well-chosen sub-lemmas = +1
- Building needed infrastructure = +1
- Meaningful refactoring = +1
- Submitting to Aristotle without other work = 0
- Changing comments/docs without proof progress = 0
- Repeating a failed approach = -1
- Breaking the build = -2
- Zero git diff = 0

**Why Haiku?** The evaluator doesn't need to understand Lean syntax deeply. It reads natural-language task results and git diffs. Fast and cheap. If evaluation quality proves insufficient, upgrade to Sonnet.

### 3.5 The Consultant (Escalation)

**Triggered when**: The evaluator judges stuck (progress_score ≤ 0) for N consecutive cycles (default: 4).

**Input**: The stuck sorry's Lean context, issue files describing the blocker, attempt history.

**Model**: Codex CLI (`mcp__codex-cli__codex`) or Gemini (`mcp__gemini-cli__ask-gemini`) — whichever is available and provides the strongest reasoning for the mathematical domain. Use the latest model version (do not hardcode — query available models at runtime or use defaults).

**Prompt**: Ask for *informal mathematical reasoning*, not Lean code:
```
I'm formalizing [theorem] in Lean 4 / Mathlib and I'm stuck on [sorry].

Here is the relevant context: [Lean code around the sorry]
Here is what has been tried and failed: [from attempts.md]
Here is the blocker: [from issues/]

Please suggest:
1. The mathematical argument that should work here
2. Relevant Mathlib theories or lemmas
3. An alternative proof strategy if the current approach is wrong
```

**Output**: Written to `issues/<sorry_name>_advice.md`. The planner reads this next cycle and incorporates it into the strategy.

**Why external consultation?** Claude Code may be stuck because it lacks the mathematical insight to find the right approach. A different model (especially one with stronger reasoning or different training data) can provide a fresh perspective. This replaces the human's role of consulting Gemini DeepThink (as was done during VML) or catching mathematical errors (ACC/DCC correction during GV).

### 3.6 Mechanical Gates

These are enforced by the Python loop, not by the agent. They cannot be bypassed.

**VeriRefine gate**: After the worker finishes, the loop checks:
- `lake env lean <file>` passes on all modified files
- Sorry count did not increase (compared to pre-cycle snapshot)

If either check fails, the cycle's changes are reverted (`git checkout -- .`) and the task result is flagged as regression. The evaluator sees this.

**Exception**: The worker can declare `RESTRUCTURING_IN_PROGRESS` in task_results, which temporarily allows sorry count to increase for up to 2 consecutive cycles (for decomposition/refactoring). If sorry count hasn't decreased by the 3rd cycle, revert to the pre-restructuring state.

**Budget cap**: If the evaluator judges the same sorry stuck for N cycles (default: 8, separate from the consultant trigger at 4), the planner is instructed to abandon that sorry temporarily, work on something else, and return to it later with a fresh approach.

**Build gate**: `lake env lean <modified files>` must succeed. Worker must verify this before committing (already part of `/commit`).

### 3.7 Telegram Alerts

Every cycle sends a Telegram notification:
```
🟢 Cycle 47 (sorry: 12→11)
Closed euler_error_step3_bound. Next: working on convergence_rate.

⚠️ Cycle 52 (sorry: 8→8) — stuck 3 cycles
Worker tried direct proof of ode_existence_local, failed (missing Picard iteration in Mathlib). Issue filed.

🔴 Cycle 55 (sorry: 8→9) — REVERTED
Restructuring exceeded 2-cycle budget. Changes rolled back.
```

The human reads these asynchronously. Intervention is only needed if:
- Stuck alerts persist beyond consultant escalation (>8 cycles)
- Repeated reverts suggest a systemic problem
- The project is complete (0 sorry) and the human wants to start the next chapter

---

## 4. File Structure

```
.prover-state/                     # gitignored, managed by the loop
├── cycle                          # current cycle number (int)
├── history.jsonl                  # one JSON record per cycle
├── strategy.md                    # planner output (read by worker)
├── attempts.md                    # compacted memory of failed approaches
├── run.lock                       # flock for concurrency safety
├── task_results/                  # per-cycle structured results
│   ├── cycle_001.md
│   ├── cycle_002.md
│   └── ...
└── issues/                        # blocker descriptions
    ├── ode_existence_local.md     # "missing Picard iteration in Mathlib"
    ├── ode_existence_local_advice.md  # from consultant
    └── ...

OpenMath/                          # the actual formalization
├── Basic.lean                     # current: Theorem 212A (Euler error bound)
├── ...                            # future: one file per section/theorem group

plan.md                            # high-level work plan
critique.md                        # adversarial review
LOG.md                             # chronological progress log
CLAUDE.md                          # instructions for the agent
```

---

## 5. CLAUDE.md Design

The CLAUDE.md is the most important artifact. Following the Munkres lesson, it should evolve iteratively based on observed failures. Initial version:

### Core workflow

1. **Read `strategy.md`** for what to work on this cycle.
2. **Sorry-first**: When formalizing new content, write the full proof structure with `sorry` at every step. Verify it compiles (`lake env lean <file>`). Then close sorry's one by one.
3. **Prove**: Use Lean LSP tools (`lean_goal`, `lean_multi_attempt`, search tools). Decompose hard sorry's into sub-lemmas. Submit truly hard lemmas to Aristotle.
4. **Write results**: Before finishing, write `task_results/<cycle>.md` documenting what you tried, what worked, what failed, and suggested next steps. If blocked, write an issue file.
5. **Commit**: Verify all modified files compile, then commit and push.

### Rules

- Follow the strategy. Do not cherry-pick easy goals.
- If Mathlib is missing something, build it yourself as a helper lemma.
- Never increase `maxHeartbeats` above 200000. Decompose the proof instead.
- Do not poll Aristotle repeatedly. Submit jobs, then work on proofs yourself.
- A cycle with zero changes is unacceptable. At minimum, decompose a sorry or write an issue.

### Build commands

```bash
lake env lean OpenMath/Foo.lean    # verify single file (preferred)
lake build                          # full build (uses cached .olean)
```

### What to formalize

Follow the textbook chapter by chapter. The current target is in `plan.md`. Each theorem should be:
- Stated as closely to the textbook as possible
- Proved in full (no sorry's in committed code, unless mid-restructuring)
- Documented with a reference to the textbook section

---

## 6. Lifecycle of a Formalization Project

### Phase 0: Setup (human, ~30 minutes)

1. Create `plan.md` with the target chapter/section and theorems to formalize.
2. Write (or have the agent write) the Lean file skeleton with theorem statements and `sorry` proofs.
3. Provide the textbook PDF in `context/` for the agent to reference.
4. Start the loop: `python scripts/autonomous_loop.py --loop --interval 120`

### Phase 1: Bulk formalization (mostly automated)

The agent works through the plan, formalizing definitions and theorem statements, then proving them. The planner prioritizes. The evaluator tracks progress. The consultant helps when stuck.

Human role: read Telegram alerts. Intervene only if stuck alerts persist beyond consultant escalation.

### Phase 2: Sorry elimination (fully automated)

The agent systematically closes remaining sorry's. Aristotle handles hard lemmas. The consultant provides mathematical insight for the toughest cases.

Human role: none, unless the project is truly stuck (0 sorry progress for 20+ cycles despite consultation).

### Phase 3: Cleanup (automated)

Once at 0 sorry, the agent runs `/critique` → `/simplify` → `/golf` cycles to improve code quality, reduce heartbeats, and prepare for potential Mathlib upstreaming.

Human role: review final code if desired. Start Phase 0 for the next chapter.

---

## 7. Getting to 99%

The 1% human intervention budget (~1 prompt per 100 cycles) covers:

| Situation | Frequency | What the human does |
|---|---|---|
| Start next chapter | Once per chapter (~100 cycles) | Write plan.md, provide PDF |
| Persistent stuck (>20 cycles) | Rare | Read issue files, provide insight or change approach |
| Systemic failure (build broken, wrong branch) | Very rare | Fix infrastructure |

Everything else is handled by the four-component system:

| Component | Replaces this human behavior |
|---|---|
| **Planner** | "Work on the hard stuff, stop cherry-picking" |
| **Evaluator** | "You're spinning" / "Good progress, keep going" |
| **Consultant** | "The proof strategy is wrong, try X instead" / consulting Gemini |
| **Mechanical gates** | "Don't break the build" / "Don't increase heartbeats" |

### What could prevent 99%

1. **Mathematical novelty**: If the textbook uses techniques not in Mathlib and not discoverable by the consultant. Mitigation: numerical analysis is well-established; most techniques have Mathlib analogues.

2. **Mathlib API changes**: Version bumps breaking existing code. Mitigation: pin Mathlib version per chapter.

3. **Agent capability ceiling**: Some proofs may be genuinely beyond current LLM capability. Mitigation: Aristotle external prover, decomposition into smaller pieces, consultant for alternative strategies.

4. **Coordination bugs**: The loop script itself has bugs. Mitigation: extensive logging, Telegram alerts on exceptions, watchdog cron job.

---

## 8. Implementation Plan

### Phase 1: Core loop (build first, iterate)

1. Write `autonomous_loop.py` with Worker only (no Planner/Evaluator/Consultant). This is the Munkres-equivalent baseline: loop re-fires a babysit prompt, each session is fresh.
2. Add `task_results/` writing to the worker prompt and CLAUDE.md.
3. Test on the next theorem (Theorem 213A: convergence of Euler method). Measure: how many cycles? How many human interventions?

### Phase 2: Add Evaluator

4. Add the Haiku evaluator. Write `attempts.md` compaction.
5. Add `history.jsonl` tracking and stuck detection.
6. Add Telegram alerts with progress scores.
7. Test on another theorem. Measure improvement.

### Phase 3: Add Planner

8. Separate the planning step from the worker.
9. Add issue-file reading and strategy generation.
10. Add cherry-picking prevention (planner prioritizes by difficulty).
11. Test on a chapter-scale target (multiple theorems).

### Phase 4: Add Consultant + Gates

12. Integrate Codex/Gemini MCP for mathematical consultation.
13. Add VeriRefine gate (sorry count monotonicity).
14. Add budget caps per sorry.
15. Test on a hard section. Measure stuck resolution rate.

### Phase 5: Scale

16. Run on full chapters. Tune parameters (cooldown, stuck thresholds, budget caps).
17. Measure automation rate. Target: <1 human intervention per 100 cycles.
18. Write a technical report comparing to Clawristotle results.

---

## 9. Open Questions

1. **Planner model**: Should the planner be Haiku (cheap) or Sonnet/Opus (better judgment)? The planner's job is strategic, not syntactic — it may need a stronger model.

2. **Consultant trigger threshold**: 4 consecutive stuck cycles before consulting? Could be too aggressive (wastes consultant calls on temporary stalls) or too passive (lets the agent spin). Needs tuning.

3. **VeriRefine strictness**: Strict monotonicity prevents regression but also prevents speculative refactoring. The 2-cycle restructuring exception is a pragmatic compromise — is it enough?

4. **attempts.md compaction**: How to keep it from growing unboundedly? Options: sliding window (last 20 entries), periodic LLM summarization, hard truncation. Needs experimentation.

5. **Parallel workers**: Archon and Meta both run multiple provers in parallel. We don't need this for a single-theorem project, but for chapter-scale targets, parallel workers (one per file) could dramatically speed things up. Deferred to Phase 5.

6. **Sorry-first enforcement**: The Munkres project found this critical. In Lean 4, the equivalent is: write `have h := by sorry` for every step, verify the structure compiles, then close sorry's. Should we enforce this mechanically (reject commits that add non-sorry tactic blocks) or via CLAUDE.md instructions?

---

## 10. References

- [Clawristotle VML Technical Report](https://github.com/Vilin97/Clawristotle) — 10-day VML formalization, same tooling
- [Clawristotle GV Technical Report](https://github.com/Vilin97/Clawristotle) — 8-day Grothendieck Vanishing, same tooling
- [Numina Lean Agent](https://github.com/project-numina/numina-lean-agent) — Python harness, session management, statement guard
- [Archon](https://github.com/frenzymath/Archon) — Plan/Prover/Review, attempt tracking, informal agent
- [M2F (arXiv 2602.17016)](https://arxiv.org/abs/2602.17016) — VeriRefine, budget caps, strict monotonicity
- [Meta Textbook (arXiv 2604.03071)](https://arxiv.org/abs/2604.03071) — 30K agent swarm, issue tracker, 7 roles
- [Munkres/Isabelle (arXiv 2604.07455)](https://arxiv.org/abs/2604.07455) — Simple loop, evolving CLAUDE.md, sorry-first, 83% automation
