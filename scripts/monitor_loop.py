#!/usr/bin/env python3
"""
Persistent monitoring for the OpenMath autonomous formalization loop.

Checks infrastructure health, detects stalls, takes corrective action,
and sends Telegram alerts. Designed to run as a cron job every 12 hours.

Usage:
    python3 scripts/monitor_loop.py          # run once (cron mode)
    crontab: 7 */12 * * * python3 /mmfs1/gscratch/stf/mathai/OpenMath/scripts/monitor_loop.py
"""

import fcntl
import json
import os
import re
import signal
import subprocess
import sys
import time
import urllib.request
import urllib.error
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional

# ─── Paths ────────────────────────────────────────────────────────────────────

ROOT = Path(__file__).resolve().parent.parent
STATE = ROOT / ".prover-state"
HISTORY_FILE = STATE / "history.jsonl"
CYCLE_FILE = STATE / "cycle"
STRATEGY_FILE = STATE / "strategy.md"
ATTEMPTS_FILE = STATE / "attempts.md"
ISSUES = STATE / "issues"
TASK_RESULTS = STATE / "task_results"
LOOP_LOCK = STATE / "run.lock"
MONITOR_LOCK = STATE / "monitor.lock"
MONITOR_LOG = STATE / "monitor.log"
ENV_FILE = ROOT / ".env"

# Infrastructure paths
NVME_TOOLCHAIN = Path("/tmp/lean4-toolchain/bin")
LAKE_WRAPPER = Path("/tmp/lake-bin/lake")
LAKE_SYMLINK = ROOT / ".lake"
LAKE_TARGET = Path("/tmp/OpenMath-lake")
CURL_SYMLINK = Path.home() / ".cache/mathlib/curl-7.88.1"
CONDA_CURL = Path("/gscratch/amath/vilin/conda/envs/curl-env/bin/curl")

PACKAGES = ["aesop", "batteries", "Cli", "importGraph",
            "LeanSearchClient", "plausible", "proofwidgets", "Qq"]

# ─── Config ───────────────────────────────────────────────────────────────────

BUDGET_CAP = 8
STALL_WINDOW = 3
STUCK_WINDOW = 3
CYCLE_HANG_HOURS = 5  # if a single cycle runs longer than this, it's hung (worker timeout is 2h)

# ─── Environment ──────────────────────────────────────────────────────────────

def load_env():
    if ENV_FILE.exists():
        for line in ENV_FILE.read_text().splitlines():
            line = line.strip()
            if line and not line.startswith("#") and "=" in line:
                key, _, value = line.partition("=")
                os.environ.setdefault(key.strip(), value.strip())

load_env()
TELEGRAM_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN", "")
TELEGRAM_CHAT_ID = os.environ.get("TELEGRAM_CHAT_ID", "")

# ─── Logging ──────────────────────────────────────────────────────────────────

_log_file = None

def log(msg):
    global _log_file
    ts = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
    line = "[{ts}] {msg}".format(ts=ts, msg=msg)
    print(line, flush=True)
    if _log_file:
        _log_file.write(line + "\n")
        _log_file.flush()

def telegram_send(message):
    if not TELEGRAM_TOKEN or not TELEGRAM_CHAT_ID:
        log("Telegram not configured, skipping")
        return
    try:
        url = "https://api.telegram.org/bot{token}/sendMessage".format(token=TELEGRAM_TOKEN)
        payload = json.dumps({
            "chat_id": TELEGRAM_CHAT_ID,
            "text": message,
            "parse_mode": "Markdown",
        }).encode()
        req = urllib.request.Request(url, data=payload,
                                     headers={"Content-Type": "application/json"},
                                     method="POST")
        with urllib.request.urlopen(req, timeout=10) as resp:
            resp.read()
    except Exception as e:
        log("Telegram send failed: {e}".format(e=e))

# ─── File helpers ─────────────────────────────────────────────────────────────

def read_history():
    if not HISTORY_FILE.exists():
        return []
    records = []
    for line in HISTORY_FILE.read_text().strip().splitlines():
        try:
            records.append(json.loads(line))
        except (json.JSONDecodeError, ValueError):
            continue
    return records

def get_cycle():
    if CYCLE_FILE.exists():
        return int(CYCLE_FILE.read_text().strip())
    return 0

def get_tracked_lean_files():
    try:
        r = subprocess.run(
            ["git", "ls-files", "OpenMath"],
            cwd=ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            universal_newlines=True,
            timeout=30,
        )
        if r.returncode == 0:
            files = []
            for rel in r.stdout.strip().splitlines():
                if rel.endswith(".lean"):
                    path = ROOT / rel
                    if path.exists():
                        files.append(path)
            if files:
                return files
    except Exception:
        pass

    lean_dir = ROOT / "OpenMath"
    if not lean_dir.exists():
        return []
    return sorted(lean_dir.rglob("*.lean"))

def _strip_lean_comments(text):
    result = []
    i = 0
    depth = 0
    while i < len(text):
        if text[i:i+2] == '/-':
            depth += 1
            i += 2
        elif text[i:i+2] == '-/' and depth > 0:
            depth -= 1
            i += 2
        elif depth == 0:
            result.append(text[i])
            i += 1
        else:
            i += 1
    text = ''.join(result)
    lines = text.splitlines()
    stripped = []
    for line in lines:
        idx = line.find('--')
        stripped.append(line[:idx] if idx >= 0 else line)
    return '\n'.join(stripped)

def count_sorries():
    count = 0
    for f in get_tracked_lean_files():
        count += len(re.findall(r'\bsorry\b', _strip_lean_comments(f.read_text())))
    return count

# ─── Phase 1: Infrastructure Health ──────────────────────────────────────────

def check_infra():
    """Returns dict of {component: 'ok' | 'missing' | 'error' | 'repaired'}."""
    results = {}

    # 1a: NVMe lean toolchain
    lean_bin = NVME_TOOLCHAIN / "lean"
    lake_bin = NVME_TOOLCHAIN / "lake"
    if lean_bin.exists() and lake_bin.exists():
        try:
            r = subprocess.run([str(lean_bin), "--version"],
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               timeout=10)
            results["toolchain"] = "ok" if r.returncode == 0 else "error"
        except Exception:
            results["toolchain"] = "error"
    else:
        results["toolchain"] = "missing"

    # 1b: Lake wrapper
    if LAKE_WRAPPER.exists() and os.access(str(LAKE_WRAPPER), os.X_OK):
        results["lake_wrapper"] = "ok"
    else:
        try:
            LAKE_WRAPPER.parent.mkdir(parents=True, exist_ok=True)
            LAKE_WRAPPER.write_text(
                '#!/bin/bash\n'
                'for arg in "$@"; do\n'
                '    if [[ "$arg" == "proofwidgets:release" ]]; then\n'
                '        exit 0\n'
                '    fi\n'
                'done\n'
                'exec /tmp/lean4-toolchain/bin/lake "$@"\n'
            )
            os.chmod(str(LAKE_WRAPPER), 0o755)
            results["lake_wrapper"] = "repaired"
            log("Repaired lake wrapper")
        except Exception as e:
            results["lake_wrapper"] = "error"
            log("Failed to repair lake wrapper: {e}".format(e=e))

    # 1c: .lake symlink
    if LAKE_SYMLINK.is_symlink() and LAKE_TARGET.exists():
        mathlib_oleans = LAKE_TARGET / "packages/mathlib/.lake/build/lib/lean/Mathlib"
        if mathlib_oleans.exists():
            results["lake_symlink"] = "ok"
        else:
            results["lake_symlink"] = "error"
            log("Mathlib oleans missing from NVMe")
    else:
        results["lake_symlink"] = "missing"

    # 1d: Curl symlink
    if CURL_SYMLINK.is_symlink() and CONDA_CURL.exists():
        results["curl_symlink"] = "ok"
    else:
        try:
            if CURL_SYMLINK.exists() or CURL_SYMLINK.is_symlink():
                CURL_SYMLINK.unlink()
            CURL_SYMLINK.symlink_to(CONDA_CURL)
            results["curl_symlink"] = "repaired"
            log("Repaired curl symlink")
        except Exception as e:
            results["curl_symlink"] = "error"
            log("Failed to repair curl symlink: {e}".format(e=e))

    # 1e: Package build symlinks
    missing_pkgs = []
    for pkg in PACKAGES:
        lib_dir = LAKE_TARGET / "packages" / pkg / ".lake/build/lib"
        if not lib_dir.exists():
            missing_pkgs.append(pkg)
    results["package_symlinks"] = "ok" if not missing_pkgs else "missing: " + ",".join(missing_pkgs)

    return results


def infra_is_critical(results):
    """Returns True if infrastructure is too broken to run the loop."""
    return results.get("toolchain") in ("missing", "error") or \
           results.get("lake_symlink") in ("missing", "error")


# ─── Phase 2: Process Liveness ────────────────────────────────────────────────

def find_loop_process():
    """Find the autonomous loop process. Returns dict with pid, elapsed, cmdline or None."""
    try:
        r = subprocess.run(["pgrep", "-f", "autonomous_loop.py"],
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                           universal_newlines=True, timeout=10)
        pids = [int(p) for p in r.stdout.strip().splitlines() if p.strip()]
    except Exception:
        return None

    for pid in pids:
        try:
            # Read cmdline
            cmdline_path = "/proc/{pid}/cmdline".format(pid=pid)
            with open(cmdline_path, "r") as f:
                cmdline = f.read().replace("\x00", " ").strip()

            # Read status
            status_path = "/proc/{pid}/status".format(pid=pid)
            with open(status_path, "r") as f:
                status_text = f.read()

            state = "unknown"
            for line in status_text.splitlines():
                if line.startswith("State:"):
                    state = line.split()[1]
                    break

            # Get elapsed time
            stat_path = "/proc/{pid}/stat".format(pid=pid)
            with open(stat_path, "r") as f:
                stat_fields = f.read().split()
            start_ticks = int(stat_fields[21])
            with open("/proc/uptime", "r") as f:
                uptime_sec = float(f.read().split()[0])
            hz = os.sysconf("SC_CLK_TCK")
            elapsed_sec = uptime_sec - (start_ticks / hz)

            if state in ("Z", "T"):
                continue  # skip zombies/stopped

            skip_planner = "--skip-planner" in cmdline

            return {
                "pid": pid,
                "elapsed_sec": elapsed_sec,
                "state": state,
                "cmdline": cmdline,
                "skip_planner": skip_planner,
            }
        except (IOError, OSError, IndexError, ValueError):
            continue

    return None


def restart_loop(skip_planner=False):
    """Restart the autonomous loop. Returns new PID or None."""
    # Clean up lock file
    if LOOP_LOCK.exists():
        try:
            LOOP_LOCK.unlink()
        except Exception:
            pass

    cmd = ["python3", str(ROOT / "scripts/autonomous_loop.py"), "--loop"]
    if skip_planner:
        cmd.append("--skip-planner")

    log("Restarting loop with: {cmd}".format(cmd=" ".join(cmd)))

    try:
        proc = subprocess.Popen(
            cmd,
            cwd=str(ROOT),
            stdout=open("/tmp/autonomous_loop.log", "a"),
            stderr=subprocess.STDOUT,
            preexec_fn=os.setpgrp,
        )
        time.sleep(5)
        if proc.poll() is None:
            log("Loop restarted with PID {pid}".format(pid=proc.pid))
            return proc.pid
        else:
            log("Loop exited immediately with code {rc}".format(rc=proc.returncode))
            return None
    except Exception as e:
        log("Failed to restart loop: {e}".format(e=e))
        return None


def kill_loop(pid):
    """Kill the loop process and its children."""
    log("Killing loop process {pid}".format(pid=pid))
    try:
        # Try SIGTERM to process group
        pgid = os.getpgid(pid)
        os.killpg(pgid, signal.SIGTERM)
    except (ProcessLookupError, PermissionError, OSError):
        try:
            os.kill(pid, signal.SIGTERM)
        except Exception:
            pass

    # Wait up to 30 seconds
    for _ in range(30):
        try:
            os.kill(pid, 0)
            time.sleep(1)
        except ProcessLookupError:
            log("Process {pid} terminated".format(pid=pid))
            return True

    # Force kill
    try:
        os.kill(pid, signal.SIGKILL)
        log("Sent SIGKILL to {pid}".format(pid=pid))
    except Exception:
        pass
    return True


# ─── Phase 3: Stuck Detection ────────────────────────────────────────────────

def normalize_topic(s):
    """Normalize a stuck_on string for comparison."""
    if not s:
        return ""
    return re.sub(r'[^a-z0-9 ]', '', s.lower()).strip()


def detect_stuck(history):
    """Analyze history for stuck indicators. Returns dict with level and details."""
    result = {
        "level": 0,
        "indicators": [],
        "stuck_on": "",
        "detail": "",
    }

    if len(history) < STALL_WINDOW:
        return result

    recent = history[-STALL_WINDOW:]

    # STALL_SCORE: last N cycles all have score <= 0
    scores = [h.get("progress_score", 1) for h in recent]
    if all(s <= 0 for s in scores):
        result["indicators"].append("STALL_SCORE")
        result["level"] = max(result["level"], 1)

    # STALL_SORRY: sorry count unchanged across last N cycles
    sorry_counts = [(h.get("pre_sorry_count", -1), h.get("post_sorry_count", -1))
                    for h in recent]
    if len(set(sorry_counts)) == 1 and sorry_counts[0][0] >= 0:
        result["indicators"].append("STALL_SORRY")
        result["level"] = max(result["level"], 1)

    # SAME_STUCK_ON: same non-empty stuck_on topic
    stuck_topics = [normalize_topic(h.get("stuck_on", "")) for h in recent]
    stuck_topics = [t for t in stuck_topics if t]
    if len(stuck_topics) >= STUCK_WINDOW:
        # Check if all recent topics are similar (share long common substring)
        if len(set(stuck_topics)) <= 2:
            result["indicators"].append("SAME_STUCK_ON")
            result["stuck_on"] = recent[-1].get("stuck_on", "")
            result["level"] = max(result["level"], 2)

    # BUDGET_CAP_HIT: stuck on same topic for BUDGET_CAP cycles
    if len(history) >= BUDGET_CAP:
        long_recent = history[-BUDGET_CAP:]
        long_topics = [normalize_topic(h.get("stuck_on", "")) for h in long_recent]
        long_topics = [t for t in long_topics if t]
        if len(long_topics) >= BUDGET_CAP and len(set(long_topics)) <= 2:
            result["indicators"].append("BUDGET_CAP_HIT")
            result["stuck_on"] = long_recent[-1].get("stuck_on", "")
            result["level"] = max(result["level"], 3)

    # NEGATIVE_TREND: last N cycles all negative
    if all(s < 0 for s in scores):
        result["indicators"].append("NEGATIVE_TREND")
        result["level"] = max(result["level"], 4)

    if result["indicators"]:
        result["detail"] = "Indicators: {ind}".format(ind=", ".join(result["indicators"]))
        if result["stuck_on"]:
            result["detail"] += " on '{topic}'".format(topic=result["stuck_on"])

    return result


def detect_patterns(history):
    """Detect repeating patterns in recent history. Returns list of pattern descriptions."""
    patterns = []
    if len(history) < 3:
        return patterns

    recent = history[-12:]  # look at last 12 cycles

    # Pattern: high timeout rate
    timeout_count = sum(
        1 for h in recent
        if "timed out" in h.get("summary", "").lower()
        or "timeout" in h.get("summary", "").lower()
        or h.get("progress_score", 0) == -1
        and "zero code changes" in h.get("summary", "").lower()
    )
    if timeout_count >= len(recent) * 0.4:
        patterns.append(
            "HIGH_TIMEOUT_RATE: {n}/{total} recent cycles timed out or produced nothing"
            .format(n=timeout_count, total=len(recent)))

    # Pattern: strategy deviation (producing work but ignoring assigned targets)
    deviation_count = sum(
        1 for h in recent
        if h.get("strategy_deviation")
        or "deviat" in h.get("summary", "").lower()
        or "off-strategy" in h.get("summary", "").lower()
        or "ignoring" in h.get("summary", "").lower()
    )
    if deviation_count >= 3:
        patterns.append(
            "STRATEGY_DEVIATION: {n} recent cycles deviated from strategy"
            .format(n=deviation_count))

    # Pattern: CLAUDE.md violations (no task result written)
    violation_count = sum(
        1 for h in recent
        if "violation" in h.get("summary", "").lower()
        or "did not write" in h.get("summary", "").lower()
        or "no task result" in h.get("summary", "").lower()
    )
    if violation_count >= 3:
        patterns.append(
            "DOCUMENTATION_VIOLATIONS: {n} recent cycles failed to write task results"
            .format(n=violation_count))

    # Pattern: sorry regressions (VeriRefine reverts)
    revert_count = sum(
        1 for h in recent
        if "REVERTED" in h.get("summary", "")
    )
    if revert_count >= 3:
        patterns.append(
            "FREQUENT_REVERTS: {n} recent cycles had sorry regressions and were reverted"
            .format(n=revert_count))

    # Pattern: same engine failing
    for engine in ("claude", "codex"):
        engine_cycles = [h for h in recent if h.get("engine") == engine]
        if len(engine_cycles) >= 3:
            engine_fails = sum(
                1 for h in engine_cycles
                if h.get("progress_score", 0) <= 0
            )
            if engine_fails == len(engine_cycles):
                patterns.append(
                    "ENGINE_FAILING: all {n} recent {engine} cycles scored <= 0"
                    .format(n=len(engine_cycles), engine=engine))

    return patterns


def run_diagnostic_agent(history, stuck_info, patterns, infra):
    """Run a Claude session to investigate issues and produce fixes.

    The agent can modify strategy.md, write issue files, and adjust
    the autonomous_loop.py configuration. Returns a summary of actions taken.
    """
    recent = history[-15:]
    history_text = "\n".join(
        "Cycle {c} [{eng}] score={s}: {summary}{stuck}".format(
            c=h.get("cycle", "?"),
            eng=h.get("engine", "?"),
            s=h.get("progress_score", "?"),
            summary=h.get("summary", "N/A"),
            stuck=" | stuck_on: " + h["stuck_on"] if h.get("stuck_on") else ""
        )
        for h in recent
    )

    pattern_text = "\n".join("- " + p for p in patterns) if patterns else "None detected."
    stuck_text = (
        "Level {lvl}: {detail}".format(lvl=stuck_info["level"], detail=stuck_info["detail"])
        if stuck_info["level"] > 0 else "Not stuck."
    )
    infra_text = "\n".join(
        "  {k}: {v}".format(k=k, v=v) for k, v in infra.items()
    )

    # Read current strategy and attempts for context
    strategy = ""
    if STRATEGY_FILE.exists():
        strategy = STRATEGY_FILE.read_text()
    attempts = ""
    if ATTEMPTS_FILE.exists():
        attempts = ATTEMPTS_FILE.read_text()[-5000:]  # last 5KB

    prompt = """You are the diagnostic agent for an autonomous Lean 4 formalization system.
The system runs in a loop: Planner → Worker → Evaluator. You are called by the 12-hour
monitor when repeating issues are detected.

Your job: investigate the patterns below, determine root causes, and TAKE ACTION to fix them.

## Recent cycle history (last 15 cycles)
{history}

## Detected patterns
{patterns}

## Stuck status
{stuck}

## Infrastructure
{infra}

## Current strategy.md
{strategy}

## Recent attempts (last 5KB)
{attempts}

## Actions you can take
1. **Write a new strategy.md** — to redirect the worker to productive work
2. **Write an issue file** in `.prover-state/issues/` — to document blockers
3. **Read and modify `scripts/autonomous_loop.py`** — to fix configuration issues
   (e.g., adjust timeouts, fix engine selection, modify worker prompts)
4. **Read any project file** to investigate (e.g., Lean files with sorrys, task results)

## Rules
- DO NOT just report findings. Take concrete action to fix the problems.
- If workers are ignoring strategy, make the strategy more forceful and specific.
- If an engine (claude/codex) consistently fails, investigate why (read logs, check config).
- If timeouts are frequent, check if the worker prompt is too broad or if lake build is hanging.
- Write a brief summary of what you investigated and what you changed to stdout.
- Be surgical — make the minimum changes needed to unblock progress.
""".format(
        history=history_text,
        patterns=pattern_text,
        stuck=stuck_text,
        infra=infra_text,
        strategy=strategy or "(no strategy file)",
        attempts=attempts or "(no attempts file)",
    )

    log("Running diagnostic agent...")
    try:
        cmd = ["claude", "-p", prompt, "--allowedTools",
               "Read,Edit,Write,Bash,Grep,Glob"]
        r = subprocess.run(
            cmd, cwd=str(ROOT),
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            universal_newlines=True, timeout=3600,
        )
        output = r.stdout.strip()
        log("Diagnostic agent done. Output length: {n}".format(n=len(output)))
        if output:
            log("Diagnostic summary: {s}".format(s=output[:1000]))
        return output[:2000] if output else "Agent produced no output"
    except subprocess.TimeoutExpired:
        log("Diagnostic agent timed out (3600s)")
        return "Diagnostic agent timed out"
    except Exception as e:
        log("Diagnostic agent failed: {e}".format(e=e))
        return "Diagnostic agent error: {e}".format(e=e)


def take_corrective_action(stuck_info, process_info, history, infra):
    """Take corrective action based on stuck level and detected patterns.

    Uses an LLM diagnostic agent for investigation when patterns are detected.
    Returns description of action taken.
    """
    level = stuck_info["level"]
    actions = []

    if level == 0:
        # Even at level 0, check for patterns that need attention
        patterns = detect_patterns(history)
        if not patterns:
            return "none"
        # Fall through to diagnostic agent below

    patterns = detect_patterns(history) if level == 0 else detect_patterns(history)

    # Level 1+: basic corrective actions (fast, no LLM)
    if level >= 1:
        if STRATEGY_FILE.exists():
            STRATEGY_FILE.unlink()
            actions.append("strategy reset")
            log("Deleted strategy.md (stall level {level})".format(level=level))

    if level >= 2:
        if process_info and process_info.get("skip_planner"):
            kill_loop(process_info["pid"])
            time.sleep(5)
            new_pid = restart_loop(skip_planner=False)
            if new_pid:
                actions.append("escalated to full mode (PID {pid})".format(pid=new_pid))
            else:
                actions.append("escalation restart FAILED")

    if level >= 4:
        try:
            subprocess.run(["git", "checkout", "--", "."], cwd=str(ROOT),
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30)
            actions.append("reverted uncommitted changes")
            log("Reverted uncommitted changes (negative regression)")
        except Exception as e:
            log("Failed to revert: {e}".format(e=e))

    # Run diagnostic agent when patterns are detected or stuck level >= 2
    if patterns or level >= 2:
        log("Patterns detected: {p}".format(p=patterns))
        log("Launching diagnostic agent for investigation and fixes...")
        diag_summary = run_diagnostic_agent(history, stuck_info, patterns, infra)
        actions.append("diagnostic agent: " + diag_summary[:500])

    return "; ".join(actions) if actions else "none"


# ─── Phase 4: Summary ────────────────────────────────────────────────────────

def compose_summary(infra, process_info, stuck_info, action_taken,
                    cycle_num, sorry_count, recent_scores):
    lines = []
    lines.append("*[MONITOR]* {ts}".format(
        ts=datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M UTC")))

    # Infrastructure
    infra_issues = [k for k, v in infra.items() if v not in ("ok", "repaired")]
    if not infra_issues:
        repaired = [k for k, v in infra.items() if v == "repaired"]
        if repaired:
            lines.append("Infra: OK (repaired: {r})".format(r=", ".join(repaired)))
        else:
            lines.append("Infra: OK")
    elif infra_is_critical(infra):
        lines.append("Infra: DEAD ({issues})".format(issues=", ".join(infra_issues)))
    else:
        lines.append("Infra: DEGRADED ({issues})".format(issues=", ".join(infra_issues)))

    # Process
    if process_info:
        elapsed_h = process_info["elapsed_sec"] / 3600
        lines.append("Process: alive (PID {pid}, {h:.1f}h)".format(
            pid=process_info["pid"], h=elapsed_h))
    else:
        lines.append("Process: DEAD (restart attempted)")

    # Cycle and sorry
    lines.append("Cycle: {c} | Sorries: {s}".format(c=cycle_num, s=sorry_count))

    # Scores
    if recent_scores:
        score_str = ", ".join("{s:+d}".format(s=s) for s in recent_scores[-5:])
        lines.append("Recent scores: [{scores}]".format(scores=score_str))

    # Stuck
    if stuck_info["level"] == 0:
        lines.append("Stuck: NO")
    else:
        lines.append("Stuck: YES (level {lvl}) {detail}".format(
            lvl=stuck_info["level"], detail=stuck_info["detail"]))

    # Action
    if action_taken and action_taken != "none":
        lines.append("Action: {action}".format(action=action_taken))

    return "\n".join(lines)


# ─── Main ─────────────────────────────────────────────────────────────────────

def main():
    global _log_file

    STATE.mkdir(parents=True, exist_ok=True)
    ISSUES.mkdir(parents=True, exist_ok=True)

    # Acquire monitor lock
    lock_fd = open(str(MONITOR_LOCK), "w")
    try:
        fcntl.flock(lock_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        print("Another monitor instance is running. Exiting.")
        sys.exit(0)

    _log_file = open(str(MONITOR_LOG), "a")
    log("=" * 60)
    log("Monitor run starting")

    try:
        # Phase 1: Infrastructure
        log("Phase 1: Infrastructure checks")
        infra = check_infra()
        for component, status in infra.items():
            log("  {c}: {s}".format(c=component, s=status))

        if infra_is_critical(infra):
            msg = ("*[MONITOR] CRITICAL*\n"
                   "Infrastructure is broken. The autonomous loop cannot run.\n"
                   "Missing: {issues}\n\n"
                   "Manual intervention required:\n"
                   "1. Check if /tmp was wiped (node reboot?)\n"
                   "2. Re-copy lean toolchain to /tmp/lean4-toolchain\n"
                   "3. Re-run lake exe cache get\n"
                   "4. Re-create package symlinks"
                   ).format(issues=", ".join(
                       k for k, v in infra.items() if v in ("missing", "error")))
            telegram_send(msg)
            log("CRITICAL infrastructure failure — aborting")
            return

        # Phase 2: Process liveness
        log("Phase 2: Process liveness check")
        process_info = find_loop_process()
        restarted = False

        if process_info:
            log("  Loop alive: PID {pid}, state={state}, elapsed={h:.1f}h".format(
                pid=process_info["pid"],
                state=process_info["state"],
                h=process_info["elapsed_sec"] / 3600))

            # Check for hung cycle
            cycle_file_mtime = CYCLE_FILE.stat().st_mtime if CYCLE_FILE.exists() else 0
            hours_since_cycle = (time.time() - cycle_file_mtime) / 3600 if cycle_file_mtime else 999
            if hours_since_cycle > CYCLE_HANG_HOURS:
                log("  WARNING: No cycle completion in {h:.1f}h — possible hang".format(
                    h=hours_since_cycle))
                kill_loop(process_info["pid"])
                time.sleep(5)
                process_info = None  # will be restarted below
        else:
            log("  Loop process NOT found")

        if not process_info:
            log("  Attempting restart...")
            # Determine flags based on stuck detection (we'll refine after Phase 3)
            new_pid = restart_loop(skip_planner=False)
            if new_pid:
                restarted = True
                process_info = {"pid": new_pid, "elapsed_sec": 0,
                                "state": "S", "cmdline": "", "skip_planner": False}
            else:
                log("  Restart FAILED")

        # Phase 3: Stuck detection
        log("Phase 3: Stuck detection")
        history = read_history()
        stuck_info = detect_stuck(history)
        log("  Stuck level: {lvl}, indicators: {ind}".format(
            lvl=stuck_info["level"],
            ind=stuck_info["indicators"] or "none"))

        action_taken = "none"
        patterns = detect_patterns(history)
        if patterns:
            log("  Patterns detected: {p}".format(p=patterns))

        if (stuck_info["level"] > 0 or patterns) and not restarted:
            log("  Taking corrective action...")
            action_taken = take_corrective_action(
                stuck_info, process_info, history, infra)
            log("  Actions: {a}".format(a=action_taken))
            # Re-find process after possible restart
            process_info = find_loop_process()

        # Phase 4: Summary
        log("Phase 4: Composing summary")
        cycle_num = get_cycle()
        sorry_count = count_sorries()
        recent_scores = [h.get("progress_score", 0) for h in history[-5:]]

        summary = compose_summary(infra, process_info, stuck_info,
                                  action_taken, cycle_num, sorry_count,
                                  recent_scores)
        log("Summary:\n" + summary)
        telegram_send(summary)

    except Exception as e:
        log("Monitor failed with exception: {e}".format(e=e))
        import traceback
        traceback.print_exc()
        telegram_send("*[MONITOR] ERROR*\n`{e}`".format(e=str(e)[:200]))
    finally:
        log("Monitor run complete")
        log("=" * 60 + "\n")
        if _log_file:
            _log_file.close()
        fcntl.flock(lock_fd, fcntl.LOCK_UN)
        lock_fd.close()


if __name__ == "__main__":
    main()
