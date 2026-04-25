#!/usr/bin/env python3
"""
Autonomous formalization loop for OpenMath.

Manages the Planner → Worker → Evaluator → Consultant pipeline.
Each component is a fresh Claude Code session. State lives in files.

Usage:
    python scripts/autonomous_loop.py --loop           # run continuously
    python scripts/autonomous_loop.py --once           # run one cycle
    python scripts/autonomous_loop.py --worker-only    # Phase 1: worker only
    python scripts/autonomous_loop.py --watchdog       # monitor & restart loop
"""

import argparse
import fcntl
import json
import os
import re
import shutil
import subprocess
import sys
import time
import urllib.request
import urllib.error
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Dict, List, Optional, Tuple

# ─── Paths ────────────────────────────────────────────────────────────────────

ROOT = Path(__file__).resolve().parent.parent
STATE = ROOT / ".prover-state"
TASK_RESULTS = STATE / "task_results"
ISSUES = STATE / "issues"
CYCLE_FILE = STATE / "cycle"
HISTORY_FILE = STATE / "history.jsonl"
STRATEGY_FILE = STATE / "strategy.md"
ATTEMPTS_FILE = STATE / "attempts.md"
LOCK_FILE = STATE / "run.lock"
HEARTBEAT_FILE = STATE / "heartbeat.json"
WATCHDOG_LOG = STATE / "watchdog.log"
ARISTOTLE_INPUTS_DIR = STATE / "aristotle_inputs"
SWEEP_STAMP_FILE = STATE / "last_cleanup_sweep.txt"
SWEEP_REPORTS_DIR = STATE / "cleanup_sweeps"
PLAN_FILE = ROOT / "plan.md"
CLAUDE_FILE = ROOT / "CLAUDE.md"
ENV_FILE = ROOT / ".env"

# ─── Config ───────────────────────────────────────────────────────────────────

DEFAULT_COOLDOWN = 300  # seconds between cycles (5 min, enough for CI to finish)
STUCK_THRESHOLD = 4     # consecutive stalls before consultant
BUDGET_CAP = 8          # consecutive stalls on same sorry before abandoning
RESTRUCTURING_BUDGET = 2  # max cycles with increasing sorry count

# File-size caps for OpenMath/*.lean files. Large monolithic files hurt
# compile time, editor responsiveness, and (empirically) encourage the worker
# to keep accreting seam-style helpers instead of closing sorry's. When a
# file is over the warn line, the planner prompt surfaces it. Over the hard
# cap, the planner MUST schedule a split before new content is added, and
# the evaluator penalizes commits that add lines to such files.
FILE_SIZE_WARN = 3000   # surface in planner prompt as a caution
FILE_SIZE_CAP = 6000    # split before adding more; evaluator penalty on growth

# Cleanup sweep: runs inline at the end of run_cycle() when the last sweep was
# >= SWEEP_INTERVAL_HOURS ago. Purely mechanical: prunes issue files whose
# referenced theorem/file is already sorry-free, deletes old scaffolding
# directories under .prover-state/aristotle_inputs/, and writes a markdown
# report with oversized files and persistent sorry's. Never touches live
# proof code (OpenMath/*.lean).
SWEEP_INTERVAL_HOURS = 48
ARISTOTLE_INPUTS_RETAIN = 30   # keep last N cycles of scaffolding
PERSISTENT_SORRY_DAYS = 14     # flag sorry's whose blame is >= N days old

# NVMe toolchain paths — GPFS lean toolchain is extremely slow on this cluster
NVME_LEAN_TOOLCHAIN = "/tmp/lean4-toolchain/bin"
LAKE_WRAPPER_DIR = "/tmp/lake-bin"

# ─── Environment ──────────────────────────────────────────────────────────────

def load_env():
    """Load .env file into os.environ."""
    if ENV_FILE.exists():
        for line in ENV_FILE.read_text().splitlines():
            line = line.strip()
            if line and not line.startswith("#") and "=" in line:
                key, _, value = line.partition("=")
                os.environ[key.strip()] = value.strip()

load_env()


def setup_nvme_toolchain():
    """Ensure NVMe lean toolchain is first in PATH.

    The GPFS lean toolchain causes multi-minute hangs due to slow I/O.
    The NVMe copy at /tmp/lean4-toolchain is orders of magnitude faster.
    A lake wrapper at /tmp/lake-bin/lake handles the proofwidgets check.
    """
    current_path = os.environ.get("PATH", "")
    if NVME_LEAN_TOOLCHAIN not in current_path:
        os.environ["PATH"] = LAKE_WRAPPER_DIR + ":" + NVME_LEAN_TOOLCHAIN + ":" + current_path

    # Ensure the lake wrapper exists
    lake_wrapper = os.path.join(LAKE_WRAPPER_DIR, "lake")
    if not os.path.exists(lake_wrapper):
        os.makedirs(LAKE_WRAPPER_DIR, exist_ok=True)
        with open(lake_wrapper, "w") as f:
            f.write('#!/bin/bash\n'
                    '# Bypass proofwidgets check (already built)\n'
                    'for arg in "$@"; do\n'
                    '    if [[ "$arg" == "proofwidgets:release" ]]; then\n'
                    '        exit 0\n'
                    '    fi\n'
                    'done\n'
                    'exec {toolchain}/lake "$@"\n'.format(toolchain=NVME_LEAN_TOOLCHAIN))
        os.chmod(lake_wrapper, 0o755)


setup_nvme_toolchain()

TELEGRAM_TOKEN = os.environ.get("TELEGRAM_BOT_TOKEN", "")
TELEGRAM_CHAT_ID = os.environ.get("TELEGRAM_CHAT_ID", "")

# ─── Telegram ─────────────────────────────────────────────────────────────────

def telegram_discover_chat_id():
    """Try to discover chat_id from recent bot updates."""
    global TELEGRAM_CHAT_ID
    if TELEGRAM_CHAT_ID or not TELEGRAM_TOKEN:
        return
    try:
        url = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/getUpdates"
        req = urllib.request.Request(url, method="GET")
        with urllib.request.urlopen(req, timeout=10) as resp:
            data = json.loads(resp.read())
        if data.get("ok") and data.get("result"):
            for update in reversed(data["result"]):
                msg = update.get("message", {})
                chat = msg.get("chat", {})
                if chat.get("id"):
                    TELEGRAM_CHAT_ID = str(chat["id"])
                    # Persist it
                    env_text = ENV_FILE.read_text() if ENV_FILE.exists() else ""
                    if "TELEGRAM_CHAT_ID" not in env_text:
                        with open(ENV_FILE, "a") as f:
                            f.write(f"\nTELEGRAM_CHAT_ID={TELEGRAM_CHAT_ID}\n")
                    log(f"Discovered Telegram chat_id: {TELEGRAM_CHAT_ID}")
                    return
    except Exception as e:
        log(f"Telegram discovery failed: {e}")


def telegram_send(message: str):
    """Send a message via Telegram bot."""
    if not TELEGRAM_TOKEN or not TELEGRAM_CHAT_ID:
        log("Telegram not configured, skipping alert")
        return
    try:
        url = f"https://api.telegram.org/bot{TELEGRAM_TOKEN}/sendMessage"
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
        log(f"Telegram send failed (Markdown): {e}")
        # Retry without Markdown parse_mode (special chars may break it)
        try:
            payload = json.dumps({
                "chat_id": TELEGRAM_CHAT_ID,
                "text": message,
            }).encode()
            req = urllib.request.Request(url, data=payload,
                                         headers={"Content-Type": "application/json"},
                                         method="POST")
            with urllib.request.urlopen(req, timeout=10) as resp:
                resp.read()
        except Exception as e2:
            log(f"Telegram send failed (plain): {e2}")


# ─── Logging ──────────────────────────────────────────────────────────────────

def log(msg: str):
    ts = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
    print(f"[{ts}] {msg}", flush=True)


# ─── Heartbeat ───────────────────────────────────────────────────────────────

def write_heartbeat(cycle: int, phase: str):
    """Write heartbeat file so the watchdog can monitor liveness."""
    now = datetime.now(timezone.utc)
    data = {
        "pid": os.getpid(),
        "cycle": cycle,
        "phase": phase,
        "timestamp": now.isoformat(),
        "epoch": now.timestamp(),
    }
    tmp = HEARTBEAT_FILE.with_suffix(".tmp")
    tmp.write_text(json.dumps(data))
    tmp.rename(HEARTBEAT_FILE)


def read_heartbeat() -> Optional[dict]:
    """Read heartbeat file. Returns None if missing or corrupt."""
    try:
        if HEARTBEAT_FILE.exists():
            return json.loads(HEARTBEAT_FILE.read_text())
    except (json.JSONDecodeError, OSError):
        pass
    return None


def _pid_alive(pid: int) -> bool:
    """Check if a process is running."""
    try:
        os.kill(pid, 0)
        return True
    except OSError:
        return False


def watchdog_log(msg: str):
    """Append a line to the watchdog log."""
    ts = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")
    line = f"[{ts}] {msg}\n"
    with open(WATCHDOG_LOG, "a") as f:
        f.write(line)
    print(line, end="", flush=True)


def run_watchdog(interval: int = 300, max_restarts: int = 10):
    """Monitor the autonomous loop and restart it if it dies.

    Checks heartbeat every `interval` seconds. If the orchestrator PID is dead,
    attempts to restart up to `max_restarts` times. Sends Telegram alerts on
    failure and when max restarts are exhausted.
    """
    watchdog_log("Watchdog starting")
    telegram_discover_chat_id()
    restart_count = 0
    loop_proc = None  # subprocess.Popen if we started the loop ourselves

    while True:
        hb = read_heartbeat()
        if hb is None:
            watchdog_log("Watchdog: no heartbeat file found, waiting...")
            time.sleep(interval)
            continue

        pid = hb.get("pid", 0)
        cycle = hb.get("cycle", "?")
        phase = hb.get("phase", "?")
        epoch = hb.get("epoch", 0)
        age = time.time() - epoch if epoch else float("inf")

        alive = _pid_alive(pid) if pid else False

        if alive:
            watchdog_log(f"Watchdog: healthy (cycle {cycle}, phase={phase}, age={int(age)}s)")
            restart_count = 0  # reset on healthy check
            time.sleep(interval)
            continue

        # Orchestrator is dead
        watchdog_log(f"Watchdog: UNHEALTHY — orchestrator pid {pid} is dead")

        if restart_count >= max_restarts:
            msg = (f"🚨 *Watchdog: max restarts ({max_restarts}) exhausted*\n"
                   f"Loop is dead (last cycle {cycle}, phase {phase}).\n"
                   f"Manual intervention required.")
            watchdog_log(f"Watchdog: max restarts ({max_restarts}) reached, alerting and exiting")
            telegram_send(msg)
            sys.exit(1)

        restart_count += 1
        watchdog_log(f"Watchdog: restarting loop (attempt {restart_count}/{max_restarts})")

        # Remove stale lock file so the new process can acquire it
        if LOCK_FILE.exists():
            try:
                LOCK_FILE.unlink()
                watchdog_log("Watchdog: removed stale lock file")
            except OSError as e:
                watchdog_log(f"Watchdog: failed to remove lock file: {e}")

        # Start a new loop process
        try:
            loop_proc = subprocess.Popen(
                [sys.executable, str(ROOT / "scripts" / "autonomous_loop.py"), "--loop"],
                cwd=ROOT,
                stdout=open("/tmp/autonomous_loop.log", "a"),
                stderr=subprocess.STDOUT,
            )
            watchdog_log(f"Watchdog: started new loop (PID {loop_proc.pid})")
            telegram_send(f"🔄 *Watchdog: restarted loop* (attempt {restart_count}/{max_restarts}, PID {loop_proc.pid})")
        except Exception as e:
            watchdog_log(f"Watchdog: failed to start loop: {e}")
            telegram_send(f"🚨 *Watchdog: restart failed*\n`{str(e)[:200]}`")

        time.sleep(interval)


# ─── File helpers ─────────────────────────────────────────────────────────────

def read_file(path: Path, default: str = "") -> str:
    if path.exists():
        return path.read_text()
    return default


def read_recent_text(path: Path, max_chars: int, default: str = "") -> str:
    """Read the tail of a text file, preserving the most recent context."""
    text = read_file(path, default)
    if len(text) <= max_chars:
        return text
    return text[-max_chars:]


def get_cycle() -> int:
    return int(read_file(CYCLE_FILE, "0").strip())


def set_cycle(n: int):
    CYCLE_FILE.write_text(str(n))


def append_history(record: dict):
    with open(HISTORY_FILE, "a") as f:
        f.write(json.dumps(record) + "\n")


def get_recent_history(n: int = 10) -> list:
    if not HISTORY_FILE.exists():
        return []
    lines = HISTORY_FILE.read_text().strip().splitlines()
    return [json.loads(l) for l in lines[-n:]]


def get_tracked_lean_files() -> List[Path]:
    """Return git-tracked Lean files under OpenMath/.

    This excludes untracked scratch files such as unfinished helper modules that
    are not part of the live build or the committed formalization state.
    """
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


# ─── Sorry counting ──────────────────────────────────────────────────────────

def _strip_lean_comments(text: str) -> str:
    """Strip block comments (/- ... -/) and line comments (-- ...) from Lean source."""
    # Remove nested block comments
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
    # Remove single-line comments
    lines = text.splitlines()
    stripped = []
    for line in lines:
        idx = line.find('--')
        stripped.append(line[:idx] if idx >= 0 else line)
    return '\n'.join(stripped)


def count_sorries() -> int:
    """Count sorry's in tracked Lean files under OpenMath/ (excluding comments)."""
    count = 0
    for f in get_tracked_lean_files():
        text = f.read_text()
        code = _strip_lean_comments(text)
        count += len(re.findall(r'\bsorry\b', code))
    return count


def get_sorry_locations() -> str:
    """Get tracked sorry locations for context (excluding comments)."""
    locations = []
    tracked_files = get_tracked_lean_files()
    if not tracked_files:
        return "No sorry's found."
    for f in tracked_files:
        text = f.read_text()
        lines = text.splitlines()
        # Track block comment depth
        depth = 0
        for i, line in enumerate(lines, 1):
            # Update block comment depth
            j = 0
            line_depth_start = depth
            while j < len(line):
                if line[j:j+2] == '/-':
                    depth += 1
                    j += 2
                elif line[j:j+2] == '-/' and depth > 0:
                    depth -= 1
                    j += 2
                else:
                    j += 1
            # Skip lines entirely inside block comments
            if line_depth_start > 0:
                continue
            # Strip line comment portion
            comment_idx = line.find('--')
            code_part = line[:comment_idx] if comment_idx >= 0 else line
            if re.search(r'\bsorry\b', code_part):
                rel = f.relative_to(ROOT)
                locations.append(f"  {rel}:{i}: {line.strip()}")
    if not locations:
        return "No sorry's found."
    return "\n".join(locations)


# ─── File-size tracking ──────────────────────────────────────────────────────

def get_file_sizes() -> List[Tuple[str, int]]:
    """Return [(relative_path, line_count)] for every OpenMath/*.lean file,
    sorted descending by line count."""
    entries: List[Tuple[str, int]] = []
    for f in get_tracked_lean_files():
        try:
            n = sum(1 for _ in f.read_text().splitlines())
        except Exception:
            continue
        entries.append((str(f.relative_to(ROOT)), n))
    entries.sort(key=lambda kv: kv[1], reverse=True)
    return entries


def get_files_over_cap() -> List[Tuple[str, int]]:
    """Return files currently over the hard size cap."""
    return [(p, n) for p, n in get_file_sizes() if n >= FILE_SIZE_CAP]


def get_file_size_report() -> str:
    """Planner/worker-facing report of OpenMath/*.lean files that are near or
    over size thresholds. Returns a short message when everything is fine."""
    entries = get_file_sizes()
    over_cap = [(p, n) for p, n in entries if n >= FILE_SIZE_CAP]
    near_cap = [(p, n) for p, n in entries if FILE_SIZE_WARN <= n < FILE_SIZE_CAP]
    if not over_cap and not near_cap:
        return (f"All OpenMath/*.lean files under {FILE_SIZE_WARN} lines. "
                "No action required.")
    lines: List[str] = []
    if over_cap:
        lines.append(
            f"HARD CAP EXCEEDED (>= {FILE_SIZE_CAP} lines). These files "
            "MUST be split before new content is added. A split cycle is a "
            "legitimate use of a full cycle — extract a cohesive sub-theory "
            "into a new `OpenMath/<sub>.lean` module and update imports:"
        )
        for p, n in over_cap:
            lines.append(f"  - {p} ({n} lines)")
    if near_cap:
        lines.append(
            f"APPROACHING CAP (>= {FILE_SIZE_WARN} lines). Prefer extracting "
            "helpers into a new module over adding more to these files:"
        )
        for p, n in near_cap:
            lines.append(f"  - {p} ({n} lines)")
    return "\n".join(lines)


def file_size_growth_report(base_rev: str = "") -> str:
    """Post-cycle: list OpenMath/*.lean files that are over the hard cap AND
    grew this cycle (i.e. commits added more lines than they removed).
    Used by the evaluator to flag accretion onto already-too-large files."""
    if not base_rev:
        return ""
    over_cap = {p for p, _ in get_files_over_cap()}
    if not over_cap:
        return ""
    try:
        r = subprocess.run(
            ["git", "diff", "--numstat", base_rev, "HEAD"],
            cwd=ROOT, capture_output=True, text=True, timeout=30,
        )
    except Exception:
        return ""
    if r.returncode != 0:
        return ""
    offenders: List[str] = []
    for line in r.stdout.splitlines():
        parts = line.split("\t")
        if len(parts) != 3:
            continue
        added_s, removed_s, path = parts
        if path not in over_cap:
            continue
        try:
            added, removed = int(added_s), int(removed_s)
        except ValueError:
            continue
        net = added - removed
        if net > 0:
            offenders.append(f"  - {path}: +{added}/-{removed} (net +{net})")
    if not offenders:
        return ""
    return (
        "FILE-SIZE ACCRETION: the worker added net lines to files already over "
        f"the {FILE_SIZE_CAP}-line hard cap. Treat this as at most 0 progress "
        "(score ≤ 0) unless the task result explicitly declares a split or "
        "refactor is in progress (SPLITTING_IN_PROGRESS or REFACTOR_COMMIT):\n"
        + "\n".join(offenders)
    )


# ─── Cleanup sweep (runs inline at end of run_cycle every SWEEP_INTERVAL_HOURS)

_ISSUE_CYCLE_RE = re.compile(r"^cycle_(\d+)_.+\.md$")
_LEAN_PATH_RE = re.compile(r"OpenMath/[A-Za-z0-9_/]+\.lean")


def _files_with_live_sorries() -> set:
    """Return {relative_path_str, ...} of tracked OpenMath/*.lean files that
    still contain a live (non-commented) sorry."""
    live = set()
    for f in get_tracked_lean_files():
        try:
            text = f.read_text()
        except Exception:
            continue
        if re.search(r"\bsorry\b", _strip_lean_comments(text)):
            live.add(str(f.relative_to(ROOT)))
    return live


def sweep_stale_issues(current_cycle: int, live_sorry_files: set) -> List[Tuple[str, str]]:
    """Delete `cycle_<N>_*.md` issue files where:
      1. N is at least 30 cycles old (N <= current_cycle - ARISTOTLE_INPUTS_RETAIN), and
      2. The issue mentions at least one `OpenMath/*.lean` path, and
      3. None of the mentioned paths still has a live sorry.

    Consultant advice files (`consultant_advice_cycle_*.md`) are skipped — they
    are advice logs, not blockers.

    Returns list of (relative_path, reason) for removed files."""
    if not ISSUES.exists():
        return []
    removed: List[Tuple[str, str]] = []
    cutoff = current_cycle - ARISTOTLE_INPUTS_RETAIN
    for path in sorted(ISSUES.iterdir()):
        if not path.is_file() or path.suffix != ".md":
            continue
        name = path.name
        if name.startswith("consultant_advice_"):
            continue
        m = _ISSUE_CYCLE_RE.match(name)
        if not m:
            continue
        try:
            n = int(m.group(1))
        except ValueError:
            continue
        if n > cutoff:
            continue
        try:
            text = path.read_text()
        except Exception:
            continue
        mentioned = set(_LEAN_PATH_RE.findall(text))
        if not mentioned:
            continue
        still_blocking = mentioned & live_sorry_files
        if still_blocking:
            continue
        try:
            path.unlink()
        except Exception as e:
            log(f"sweep: failed to remove {name}: {e}")
            continue
        rel = str(path.relative_to(ROOT))
        reason = f"cycle {n} <= {cutoff}; mentioned files sorry-free: {', '.join(sorted(mentioned))}"
        removed.append((rel, reason))
    return removed


def sweep_old_aristotle_inputs(current_cycle: int) -> List[str]:
    """Delete `.prover-state/aristotle_inputs/cycle_<N>/` directories where
    N <= current_cycle - ARISTOTLE_INPUTS_RETAIN. Returns list of removed
    relative paths."""
    if not ARISTOTLE_INPUTS_DIR.exists():
        return []
    removed: List[str] = []
    cutoff = current_cycle - ARISTOTLE_INPUTS_RETAIN
    for path in sorted(ARISTOTLE_INPUTS_DIR.iterdir()):
        if not path.is_dir():
            continue
        name = path.name
        if not name.startswith("cycle_"):
            continue
        try:
            n = int(name[len("cycle_"):])
        except ValueError:
            continue
        if n > cutoff:
            continue
        try:
            shutil.rmtree(path)
        except Exception as e:
            log(f"sweep: failed to remove {name}: {e}")
            continue
        removed.append(str(path.relative_to(ROOT)))
    return removed


def _blame_line_age_days(file_rel: str, line_no: int) -> Optional[int]:
    """Return age in days of the commit that last touched file_rel:line_no,
    or None on failure."""
    try:
        r = subprocess.run(
            ["git", "log", "-1", "--format=%ct", "-L",
             f"{line_no},{line_no}:{file_rel}"],
            cwd=ROOT, capture_output=True, text=True, timeout=30,
        )
    except Exception:
        return None
    if r.returncode != 0:
        return None
    first = r.stdout.splitlines()[0].strip() if r.stdout.strip() else ""
    if not first.isdigit():
        return None
    commit_ts = int(first)
    now_ts = int(datetime.now(tz=timezone.utc).timestamp())
    return max(0, (now_ts - commit_ts) // 86400)


def persistent_sorry_report() -> List[Tuple[str, int, int]]:
    """Return [(relative_path, line_no, age_days)] for every live sorry in
    OpenMath/*.lean whose last-touching commit is >= PERSISTENT_SORRY_DAYS old."""
    entries: List[Tuple[str, int, int]] = []
    for f in get_tracked_lean_files():
        try:
            text = f.read_text()
        except Exception:
            continue
        rel = str(f.relative_to(ROOT))
        lines = text.splitlines()
        depth = 0
        for i, line in enumerate(lines, 1):
            j = 0
            line_depth_start = depth
            while j < len(line):
                if line[j:j+2] == "/-":
                    depth += 1
                    j += 2
                elif line[j:j+2] == "-/" and depth > 0:
                    depth -= 1
                    j += 2
                else:
                    j += 1
            if line_depth_start > 0:
                continue
            idx = line.find("--")
            code = line[:idx] if idx >= 0 else line
            if not re.search(r"\bsorry\b", code):
                continue
            age = _blame_line_age_days(rel, i)
            if age is None or age < PERSISTENT_SORRY_DAYS:
                continue
            entries.append((rel, i, age))
    entries.sort(key=lambda x: (-x[2], x[0], x[1]))
    return entries


def oversized_files_report() -> List[Tuple[str, int]]:
    """Return [(relative_path, line_count)] for files over FILE_SIZE_CAP,
    sorted by size descending."""
    return sorted(get_files_over_cap(), key=lambda x: -x[1])


def format_cleanup_report(
    date_str: str,
    current_cycle: int,
    removed_issues: List[Tuple[str, str]],
    removed_aristotle: List[str],
    oversized: List[Tuple[str, int]],
    persistent: List[Tuple[str, int, int]],
) -> str:
    """Render the cleanup-sweep markdown report."""
    lines = [f"# Cleanup sweep — {date_str} (cycle {current_cycle})", ""]

    lines.append("## Removed stale issues")
    if removed_issues:
        for path, reason in removed_issues:
            lines.append(f"- `{path}` — {reason}")
    else:
        lines.append("- (none)")
    lines.append("")

    lines.append(f"## Removed aristotle_inputs (> {ARISTOTLE_INPUTS_RETAIN} cycles old)")
    if removed_aristotle:
        for path in removed_aristotle:
            lines.append(f"- `{path}`")
    else:
        lines.append("- (none)")
    lines.append("")

    lines.append(f"## Oversized files (>= {FILE_SIZE_CAP} lines)")
    if oversized:
        for path, n in oversized:
            lines.append(f"- `{path}` — {n} lines (recommend split)")
    else:
        lines.append("- (none)")
    lines.append("")

    lines.append(f"## Persistent sorry's (untouched >= {PERSISTENT_SORRY_DAYS} days)")
    if persistent:
        for path, line_no, age in persistent:
            lines.append(f"- `{path}:{line_no}` — {age} days old")
    else:
        lines.append("- (none)")
    lines.append("")

    return "\n".join(lines)


def _sweep_should_run() -> bool:
    """True iff the last sweep was >= SWEEP_INTERVAL_HOURS ago (or never).

    Stamp file holds epoch seconds (float) for Python 3.6 compatibility —
    `datetime.fromisoformat` is 3.7+ and the orchestrator runs under 3.6.8."""
    if not SWEEP_STAMP_FILE.exists():
        return True
    raw = SWEEP_STAMP_FILE.read_text().strip()
    try:
        last_epoch = float(raw)
    except ValueError:
        try:
            last_epoch = datetime.strptime(
                raw[:26], "%Y-%m-%dT%H:%M:%S.%f"
            ).replace(tzinfo=timezone.utc).timestamp()
        except Exception:
            return True
    age_hours = (time.time() - last_epoch) / 3600.0
    return age_hours >= SWEEP_INTERVAL_HOURS


def _sweep_commit_and_push(report_rel: str):
    """Stage any touched .prover-state/{issues,aristotle_inputs,cleanup_sweeps}
    paths, commit if there's a diff, and push. Never touches OpenMath/."""
    try:
        subprocess.run(
            ["git", "add", "-A", "--",
             ".prover-state/issues",
             ".prover-state/aristotle_inputs",
             ".prover-state/cleanup_sweeps",
             ".prover-state/last_cleanup_sweep.txt"],
            cwd=ROOT, check=False, timeout=60,
        )
        diff = subprocess.run(
            ["git", "diff", "--cached", "--quiet"],
            cwd=ROOT, timeout=30,
        )
        if diff.returncode == 0:
            return
        subprocess.run(
            ["git", "commit", "-m",
             f"chore: 48h cleanup sweep\n\nReport: {report_rel}"],
            cwd=ROOT, check=False, timeout=60,
        )
        subprocess.run(
            ["git", "push"],
            cwd=ROOT, check=False, timeout=120,
        )
    except Exception as e:
        log(f"sweep: commit/push failed: {e}")


def maybe_run_cleanup_sweep(current_cycle: int) -> bool:
    """If >= SWEEP_INTERVAL_HOURS has passed since the last sweep, run the
    sweep and commit the results. Returns True iff the sweep actually ran."""
    if not _sweep_should_run():
        return False
    log(f"── Cleanup sweep (every {SWEEP_INTERVAL_HOURS}h) ──")
    SWEEP_REPORTS_DIR.mkdir(parents=True, exist_ok=True)
    try:
        live = _files_with_live_sorries()
        removed_issues = sweep_stale_issues(current_cycle, live)
        removed_aristotle = sweep_old_aristotle_inputs(current_cycle)
        oversized = oversized_files_report()
        persistent = persistent_sorry_report()
        now = datetime.now(tz=timezone.utc)
        date_tag = now.strftime("%Y-%m-%dT%H-%M-%SZ")
        report = format_cleanup_report(
            now.strftime("%Y-%m-%d %H:%M UTC"),
            current_cycle, removed_issues, removed_aristotle,
            oversized, persistent,
        )
        report_path = SWEEP_REPORTS_DIR / f"{date_tag}.md"
        report_path.write_text(report)
        log(f"sweep: wrote {report_path.relative_to(ROOT)}; "
            f"removed {len(removed_issues)} issue(s), "
            f"{len(removed_aristotle)} aristotle dir(s); "
            f"{len(oversized)} oversized, {len(persistent)} persistent sorry(s)")
        SWEEP_STAMP_FILE.write_text(f"{now.timestamp():.6f}")
        _sweep_commit_and_push(str(report_path.relative_to(ROOT)))
    except Exception as e:
        log(f"sweep: unexpected failure: {e}")
        return False
    return True


# ─── Git helpers ──────────────────────────────────────────────────────────────

def git_pull():
    """Pull latest changes."""
    try:
        subprocess.run(["git", "pull", "--rebase"], cwd=ROOT,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60)
    except Exception as e:
        log(f"git pull failed: {e}")


def check_ci_status() -> dict:
    """Check the CI status of the latest commit on main.

    Returns dict with 'status' ('success', 'failure', 'pending', 'unknown')
    and 'details' (error messages if failed).
    """
    try:
        r = subprocess.run(
            ["gh", "run", "list", "--branch", "main", "--limit", "1",
             "--json", "conclusion,status,name,headSha,databaseId"],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            universal_newlines=True, timeout=30)
        if r.returncode != 0:
            return {"status": "unknown", "details": f"gh failed: {r.stderr[:200]}"}

        runs = json.loads(r.stdout)
        if not runs:
            return {"status": "unknown", "details": "No CI runs found"}

        run = runs[0]
        if run.get("status") != "completed":
            return {"status": "pending", "details": f"CI run {run.get('databaseId')} in progress"}

        conclusion = run.get("conclusion", "unknown")
        if conclusion == "success":
            return {"status": "success", "details": ""}

        # Get failure details
        run_id = run.get("databaseId")
        details = f"CI run {run_id} failed"
        try:
            r2 = subprocess.run(
                ["gh", "run", "view", str(run_id), "--log-failed"],
                cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                universal_newlines=True, timeout=30)
            # Extract error lines
            errors = [
                line.split("\t")[-1].strip()
                for line in r2.stdout.splitlines()
                if "error:" in line.lower()
                and "exited" not in line.lower()
                and "failed" not in line.lower()
            ]
            if errors:
                details += ":\n" + "\n".join(errors[:20])
        except Exception:
            pass

        return {"status": "failure", "details": details}

    except Exception as e:
        return {"status": "unknown", "details": str(e)}


def git_diff_stat() -> str:
    """Get git diff --stat for current uncommitted changes."""
    try:
        r = subprocess.run(["git", "diff", "--stat"], cwd=ROOT,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True, timeout=30)
        return r.stdout.strip()
    except Exception:
        return ""


def git_head() -> str:
    """Return the current HEAD SHA, or empty string on failure."""
    try:
        r = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            universal_newlines=True,
            timeout=30,
        )
        if r.returncode == 0:
            return r.stdout.strip()
    except Exception:
        pass
    return ""


def git_status_short() -> str:
    """Return `git status --short`, including untracked files."""
    try:
        r = subprocess.run(
            ["git", "status", "--short"],
            cwd=ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            universal_newlines=True,
            timeout=30,
        )
        return r.stdout.strip()
    except Exception:
        return ""


def git_push() -> bool:
    """Push the current branch. Returns True on success."""
    try:
        r = subprocess.run(
            ["git", "push"],
            cwd=ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            universal_newlines=True,
            timeout=120,
        )
        if r.returncode == 0:
            return True
        log(f"git push failed: {r.stderr[:500]}")
    except Exception as e:
        log(f"git push error: {e}")
    return False


def git_diff(base_rev: str = "") -> str:
    """Get git diff information for this cycle.

    If `base_rev` is provided, include committed changes from `base_rev..HEAD`
    so evaluator/planner logic still sees real work after the worker commits.
    """
    try:
        sections = []

        current_head = git_head()
        if base_rev and current_head and base_rev != current_head:
            committed_stat = subprocess.run(
                ["git", "diff", "--stat", f"{base_rev}..HEAD"],
                cwd=ROOT,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                universal_newlines=True,
                timeout=30,
            )
            committed_full = subprocess.run(
                ["git", "diff", f"{base_rev}..HEAD"],
                cwd=ROOT,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                universal_newlines=True,
                timeout=30,
            )
            committed_text = (committed_stat.stdout + "\n" + committed_full.stdout).strip()
            if committed_text:
                sections.append(
                    "## Committed changes since cycle start\n"
                    f"base={base_rev}\nhead={current_head}\n\n{committed_text}"
                )

        stat = subprocess.run(["git", "diff", "--stat"], cwd=ROOT,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              universal_newlines=True, timeout=30)
        full = subprocess.run(["git", "diff"], cwd=ROOT,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              universal_newlines=True, timeout=30)
        worktree_text = (stat.stdout + "\n" + full.stdout).strip()
        if worktree_text:
            sections.append("## Uncommitted worktree changes\n" + worktree_text)

        status = git_status_short()
        if status:
            sections.append("## Git status\n" + status)

        return "\n\n".join(s for s in sections if s)[:200000]
    except Exception:
        return ""


def git_changed_files(base_rev: str = "") -> set:
    """Return files changed this cycle, including committed and uncommitted work."""
    changed = set()
    commands = []
    if base_rev:
        commands.append(["git", "diff", "--name-only", f"{base_rev}..HEAD"])
    commands.extend([
        ["git", "diff", "--name-only"],
        ["git", "diff", "--cached", "--name-only"],
    ])

    try:
        for cmd in commands:
            r = subprocess.run(
                cmd,
                cwd=ROOT,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                universal_newlines=True,
                timeout=30,
            )
            changed.update(line.strip() for line in r.stdout.splitlines() if line.strip())

        status = git_status_short()
        for line in status.splitlines():
            if not line:
                continue
            # Porcelain format: XY path, or "?? path" for untracked files.
            path = line[3:] if len(line) > 3 else ""
            if path:
                changed.add(path)
    except Exception:
        pass

    return changed


def git_revert_cycle_commits(base_rev: str, cycle: int) -> bool:
    """Revert any committed changes made since `base_rev`.

    This is used when a worker committed a regression before the mechanical
    gates ran. We prefer `git revert` over history-rewriting commands so the
    rollback is explicit and non-destructive.
    """
    current_head = git_head()
    if not base_rev or not current_head or base_rev == current_head:
        return False

    try:
        revs = subprocess.run(
            ["git", "rev-list", "--reverse", f"{base_rev}..{current_head}"],
            cwd=ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            universal_newlines=True,
            timeout=30,
        )
        commits = [line.strip() for line in revs.stdout.splitlines() if line.strip()]
        if not commits:
            return False

        r = subprocess.run(
            ["git", "revert", "--no-edit", *commits],
            cwd=ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            universal_newlines=True,
            timeout=600,
        )
        if r.returncode != 0:
            log(f"git revert failed for cycle {cycle}: {r.stderr[:500]}")
            return False

        log(f"Reverted {len(commits)} committed change(s) from cycle {cycle}")
        git_push()
        return True
    except Exception as e:
        log(f"git revert error for cycle {cycle}: {e}")
        return False


def git_log_recent(n: int = 5) -> str:
    try:
        r = subprocess.run(["git", "log", f"-{n}", "--oneline"], cwd=ROOT,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True, timeout=30)
        return r.stdout.strip()
    except Exception:
        return ""


def git_revert_changes():
    """Revert all uncommitted changes."""
    try:
        subprocess.run(["git", "checkout", "--", "."], cwd=ROOT,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30)
        log("Reverted uncommitted changes")
    except Exception as e:
        log(f"git revert failed: {e}")


# ─── Build gate ───────────────────────────────────────────────────────────────

def get_modified_lean_files() -> list:
    """Get list of modified Lean files."""
    try:
        r = subprocess.run(["git", "diff", "--name-only"], cwd=ROOT,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True, timeout=30)
        staged = subprocess.run(["git", "diff", "--cached", "--name-only"], cwd=ROOT,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True, timeout=30)
        files = set(r.stdout.strip().splitlines() + staged.stdout.strip().splitlines())
        return [f for f in files if f.endswith(".lean")]
    except Exception:
        return []


def check_build(files: list = None) -> bool:
    """Run lake env lean on modified files. Returns True if build passes."""
    if not files:
        files = get_modified_lean_files()
    if not files:
        # No modified files, check all
        lean_dir = ROOT / "OpenMath"
        files = [str(f.relative_to(ROOT)) for f in lean_dir.rglob("*.lean")] if lean_dir.exists() else []
    for f in files:
        try:
            r = subprocess.run(["lake", "env", "lean", f], cwd=ROOT,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True, timeout=600)
            if r.returncode != 0:
                log(f"Build failed for {f}: {r.stderr[:500]}")
                return False
        except subprocess.TimeoutExpired:
            log(f"Build timed out for {f}")
            return False
        except Exception as e:
            log(f"Build check error for {f}: {e}")
            return False
    return True


# ─── Agent sessions ──────────────────────────────────────────────────────────

# Path to Aristotle CLI (installed via uv)
ARISTOTLE_BIN = str(ROOT / ".uv-tools" / "aristotle-mcp" / "bin" / "aristotle")
ARISTOTLE_RESULTS_DIR = STATE / "aristotle_results"

# Path to codex binary (installed in conda env)
CODEX_BIN = "/gscratch/amath/vilin/conda/envs/codex/bin/codex"

# ─── Aristotle ────────────────────────────────────────────────────────────────

def aristotle_check_completed() -> List[Dict]:
    """Check for completed Aristotle jobs. Returns list of completed projects."""
    api_key = os.environ.get("ARISTOTLE_API_KEY", "")
    if not api_key:
        log("Aristotle: no API key configured, skipping check")
        return []

    completed = []
    for status in ["COMPLETE", "COMPLETE_WITH_ERRORS"]:
        try:
            r = subprocess.run(
                [ARISTOTLE_BIN, "list", "--api-key", api_key,
                 "--status", status, "--limit", "20"],
                cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                universal_newlines=True, timeout=30)
            if r.returncode != 0:
                log(f"Aristotle list ({status}) failed: {r.stderr[:200]}")
                continue
            # Parse output — aristotle list prints project info
            output = r.stdout.strip()
            if output:
                # Extract project IDs (UUIDs) from output
                ids = re.findall(r'[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}', output)
                for pid in ids:
                    completed.append({"project_id": pid, "status": status})
        except subprocess.TimeoutExpired:
            log(f"Aristotle list ({status}) timed out")
        except Exception as e:
            log(f"Aristotle list ({status}) error: {e}")

    return completed


def aristotle_download_result(project_id: str) -> Optional[str]:
    """Download result for a completed Aristotle project. Returns destination path or None."""
    api_key = os.environ.get("ARISTOTLE_API_KEY", "")
    if not api_key:
        return None

    dest_dir = ARISTOTLE_RESULTS_DIR / project_id
    # If a previous run left a flat file (not a dir) at this path, remove it
    if dest_dir.exists() and not dest_dir.is_dir():
        dest_dir.unlink()
    dest_dir.mkdir(parents=True, exist_ok=True)
    # CLI --destination expects a file path (writes tar.gz), not a directory
    dest_file = dest_dir / "result.tar.gz"

    try:
        r = subprocess.run(
            [ARISTOTLE_BIN, "result", project_id,
             "--api-key", api_key, "--destination", str(dest_file)],
            cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            universal_newlines=True, timeout=60)
        if r.returncode != 0:
            log(f"Aristotle result {project_id[:8]} failed: {r.stderr[:200]}")
            return None
        # Extract the tar.gz
        import tarfile
        if dest_file.exists() and tarfile.is_tarfile(str(dest_file)):
            with tarfile.open(str(dest_file), "r:gz") as tf:
                tf.extractall(path=str(dest_dir))
            log(f"Aristotle result {project_id[:8]} extracted to {dest_dir}")
        else:
            log(f"Aristotle result {project_id[:8]} downloaded to {dest_dir}")
        return str(dest_dir)
    except Exception as e:
        log(f"Aristotle result {project_id[:8]} error: {e}")
        return None


def aristotle_harvest() -> str:
    """Check for and download all completed Aristotle results.

    Returns a summary string for the worker to use.
    """
    completed = aristotle_check_completed()
    if not completed:
        log("Aristotle: no completed jobs found")
        return ""

    log(f"Aristotle: found {len(completed)} completed job(s)")
    summaries = []

    # Track which projects we've already harvested
    harvested_file = STATE / "aristotle_harvested.txt"
    already_harvested = set()
    if harvested_file.exists():
        already_harvested = set(harvested_file.read_text().strip().splitlines())

    new_results = []
    for job in completed:
        pid = job["project_id"]
        if pid in already_harvested:
            continue

        dest = aristotle_download_result(pid)
        if dest:
            # List files in the result directory
            result_files = list(Path(dest).rglob("*.lean"))
            file_list = ", ".join(f.name for f in result_files[:10])
            summaries.append(
                f"- Project {pid[:8]}… ({job['status']}): "
                f"{len(result_files)} Lean file(s) [{file_list}] → {dest}"
            )
            new_results.append(pid)
        else:
            summaries.append(f"- Project {pid[:8]}… ({job['status']}): download failed")

    # Mark as harvested
    if new_results:
        with open(harvested_file, "a") as f:
            for pid in new_results:
                f.write(pid + "\n")

    if summaries:
        summary = "## Aristotle results ready for incorporation\n" + "\n".join(summaries)
        log(f"Aristotle harvest: {len(new_results)} new result(s)")
        return summary
    return ""


def run_claude(prompt: str, model: str = None, timeout: int = 1800,
               json_output: bool = False) -> str:
    """Run a fresh Claude Code session with the given prompt.

    Returns stdout as a string.
    """
    cmd = ["claude", "-p", "--dangerously-skip-permissions"]
    if not json_output:
        cmd.append("--verbose")
    if model:
        cmd.extend(["--model", model])
    if json_output:
        cmd.append("--output-format=json")

    log(f"Running claude session (model={model or 'default'}, timeout={timeout}s)")
    log(f"Prompt preview: {prompt[:200]}...")

    try:
        r = subprocess.run(
            cmd,
            input=prompt,
            cwd=ROOT,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            universal_newlines=True,
            timeout=timeout,
            env={k: v for k, v in os.environ.items() if k != "CLAUDECODE"},
        )
        output = r.stdout
        fallback_reason = None
        if r.returncode != 0:
            log(f"Claude session exited with code {r.returncode}")
            if r.stderr:
                log(f"stderr: {r.stderr[:500]}")
            fallback_reason = f"exit code {r.returncode}"

        if json_output and output.strip():
            try:
                parsed = json.loads(output.strip())
                if isinstance(parsed, dict) and parsed.get("type") == "result" and parsed.get("is_error"):
                    fallback_reason = parsed.get("result", "Claude CLI returned an error")
            except json.JSONDecodeError:
                # Leave malformed output to the caller's parser.
                pass

        if not fallback_reason and output:
            if "You've hit your limit" in output or "rate limit" in output.lower():
                fallback_reason = "Claude usage unavailable"

        if fallback_reason:
            log(f"Claude unavailable, falling back to Codex: {fallback_reason}")
            return run_codex(prompt, timeout=timeout)

        return output
    except subprocess.TimeoutExpired:
        log(f"Claude session timed out after {timeout}s")
        log("Claude timed out, falling back to Codex")
        return run_codex(prompt, timeout=timeout)
    except Exception as e:
        log(f"Claude session failed: {e}")
        log("Claude failed, falling back to Codex")
        return run_codex(prompt, timeout=timeout)


CODEX_CONDA_ENV = "/gscratch/amath/vilin/conda/envs/codex"


def parse_evaluator_output(output: str) -> dict:
    """Parse evaluator output from raw JSON or the Claude CLI JSON envelope."""
    parsed = json.loads(output.strip())

    if isinstance(parsed, dict) and parsed.get("type") == "result":
        if parsed.get("is_error"):
            raise ValueError(parsed.get("result", "Claude CLI returned an error"))
        result = parsed.get("result")
        if isinstance(result, dict):
            return result
        if isinstance(result, str):
            return json.loads(result.strip())
        raise ValueError("Claude CLI JSON output did not contain a JSON result payload")

    if isinstance(parsed, dict):
        return parsed

    raise ValueError("Evaluator output was not a JSON object")

def run_codex(prompt: str, timeout: int = 1800) -> str:
    """Run a fresh Codex CLI session with the given prompt.

    Returns stdout as a string.
    """
    cmd = [
        CODEX_BIN, "exec",
        "--dangerously-bypass-approvals-and-sandbox",
    ]

    # Codex is a Node.js app — node must be on PATH.
    # Prepend the conda env's bin dir so node (and other deps) are found.
    env = os.environ.copy()
    conda_bin = os.path.join(CODEX_CONDA_ENV, "bin")
    env["PATH"] = conda_bin + ":" + env.get("PATH", "")

    log(f"Running codex session (timeout={timeout}s)")
    log(f"Prompt preview: {prompt[:200]}...")

    try:
        r = subprocess.run(
            cmd,
            input=prompt,
            cwd=ROOT,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            universal_newlines=True,
            timeout=timeout,
            env=env,
        )
        output = r.stdout
        if r.returncode != 0:
            log(f"Codex session exited with code {r.returncode}")
            if r.stderr:
                log(f"stderr: {r.stderr[:500]}")
        return output
    except subprocess.TimeoutExpired:
        log(f"Codex session timed out after {timeout}s")
        return "[TIMEOUT]"
    except Exception as e:
        log(f"Codex session failed: {e}")
        return f"[ERROR: {e}]"


def get_worker_engine(cycle: int) -> str:
    """Determine which engine to use for this cycle's worker.

    Even cycles → claude, odd cycles → codex.
    """
    return "codex" if cycle % 2 == 1 else "claude"


def extract_markdown_section(text: str, header: str) -> str:
    """Extract a top-level markdown section beginning with `header`."""
    lines = text.splitlines()
    start = None
    for i, line in enumerate(lines):
        if line.strip() == header:
            start = i
            break
    if start is None:
        return ""

    end = len(lines)
    for i in range(start + 1, len(lines)):
        if lines[i].startswith("## "):
            end = i
            break
    return "\n".join(lines[start:end]).strip()


def extract_target_files(text: str) -> List[str]:
    """Extract `OpenMath/Foo.lean` references from free-form text."""
    return sorted(set(re.findall(r'(OpenMath/\w+\.lean)', text)))


def get_recent_issue_text(limit: int = 12, preferred_files: Optional[List[str]] = None) -> str:
    """Read the most recent non-consultant issue files."""
    if not ISSUES.exists():
        return "No open issues."

    issue_files = [
        p for p in ISSUES.glob("*.md")
        if not p.stem.startswith("consultant_advice")
    ]
    preferred_names = set()
    for path in preferred_files or []:
        preferred_names.add(path)
        preferred_names.add(Path(path).name)

    def priority(p: Path):
        try:
            text = p.read_text()
        except Exception:
            text = ""
        matches_target = any(name in text for name in preferred_names) if preferred_names else False
        return (0 if matches_target else 1, -p.stat().st_mtime)

    issue_files.sort(key=priority)
    issue_files = issue_files[:limit]

    if not issue_files:
        return "No open issues."

    chunks = []
    for issue_file in issue_files:
        chunks.append(f"\n### {issue_file.stem}\n{issue_file.read_text()}\n")
    return "".join(chunks)


# ─── Components ───────────────────────────────────────────────────────────────

def run_planner(cycle: int, aristotle_summary: str = "") -> str:
    """Run the planner to generate strategy.md."""
    sorry_locations = get_sorry_locations()
    plan = read_file(PLAN_FILE, "No plan.md found.")
    plan_focus = extract_markdown_section(plan, "## Current Target")
    plan_target_files = extract_target_files(plan_focus or plan)
    attempts = read_recent_text(ATTEMPTS_FILE, 20000, "No previous attempts.")
    recent_history = get_recent_history(5)
    history_summary = "\n".join(
        f"  Cycle {h.get('cycle', '?')}: score={h.get('progress_score', '?')}, "
        f"summary={h.get('summary', 'N/A')}"
        for h in recent_history
    ) or "No history yet."

    # Read latest task result
    latest_task_result = ""
    if cycle > 1:
        prev = TASK_RESULTS / f"cycle_{cycle-1:03d}.md"
        latest_task_result = read_file(prev, "No task result from previous cycle.")

    issues_text = get_recent_issue_text(limit=12, preferred_files=plan_target_files)

    latest_alignment = "No explicit target-file alignment check available."
    if plan_target_files and latest_task_result:
        target_mentions = []
        for path in plan_target_files:
            target_mentions.extend([path, Path(path).name])
        if any(name in latest_task_result for name in target_mentions):
            latest_alignment = (
                "The previous cycle output mentions the current plan target files."
            )
        else:
            latest_alignment = (
                "The previous cycle output does not mention the current plan target files "
                f"({', '.join(Path(p).name for p in plan_target_files)}); treat it as a side "
                "investigation unless a blocker issue proves it is a prerequisite."
            )

    git_recent = git_log_recent(10)
    budget_stuck = check_budget_cap()
    stall_note = (
        f"The project has hit the budget cap on: {budget_stuck}. The next strategy must pivot away "
        "from that blocker or attack a smaller prerequisite seam beneath it."
        if budget_stuck else
        "No active budget-cap blocker."
    )

    prompt = f"""You are the planner for an autonomous Lean 4 formalization project.
Your job: write strategy.md with concrete instructions for the worker.

This repository's textbook on `main` is Arieh Iserles, *A First Course in the Numerical Analysis
of Differential Equations*. The old `extraction/` pipeline was for a different book and has been
removed from `main`; do not assume `extraction/` exists, and do not plan work around Butcher-only
metadata.

## Current plan
{plan}

## Current plan focus
{plan_focus or "No explicit Current Target section found in plan.md."}

## Current target files
{", ".join(plan_target_files) if plan_target_files else "No explicit target files extracted from the plan."}

## Sorry locations
{sorry_locations}

## File size status
{get_file_size_report()}

## Recent git history
{git_recent}

## Recent cycle history
{history_summary}

## What was tried recently (DO NOT repeat these)
{attempts}

## Open issues (blockers reported by previous workers)
{issues_text}

## Stall status
{stall_note}

## Task results from last cycle
{latest_task_result}

## Latest-cycle alignment check
{latest_alignment}

## Completed Aristotle results (ready for incorporation)
{aristotle_summary or "No pending Aristotle results."}

## Your job
Write `.prover-state/strategy.md` with:
1. If Aristotle results are available, prioritize incorporating them first
2. Which sorry/theorem to work on (highest priority, not cherry-picking easy ones)
3. What approach to use (specific, not "try harder")
4. What NOT to try (explicitly list failed approaches from attempts)
5. If an issue reports a blocker, assign infrastructure work before proof work
6. If there are no sorry's and no theorems in progress, pick the next theorem from plan.md
7. If recent history shows repeated low-value cycles on the same blocker, pivot to a smaller
   prerequisite seam or to the next unfinished target instead of reissuing the same plan
8. Base the strategy on the live Lean files, `plan.md`, recent task results, and recent issues only
9. Treat `plan.md`'s Current Target as the highest-priority source of truth; do not pivot to a
   different theorem family unless an issue or task result shows it is an explicit prerequisite
10. Do not promote a failed or off-target side investigation into the next main target by default
11. Do not assign tracked scratch work in a new `OpenMath/*.lean` file unless it is clearly part
    of the planned theorem path and intended to remain in the repo
12. If any file is over the hard size cap (see "File size status"), the highest-priority work is
    a split of that file. Extract a cohesive sub-theory into a new module (e.g. split
    `OpenMath/Foo.lean` into `OpenMath/Foo/Core.lean` + `OpenMath/Foo/Extras.lean`). Only skip
    the split if the current Target theorem is one-to-two cycles away AND would be strictly
    blocked by the split — state that tradeoff explicitly in strategy.md.

Be concrete and actionable. The worker will follow your instructions literally.
Write the file now using the Write tool.
"""
    output = run_claude(prompt, timeout=1800)
    log(f"Planner done. Output length: {len(output)}")
    return output


def run_worker(cycle: int, aristotle_summary: str = "") -> str:
    """Run the worker to make progress on the formalization."""
    engine = get_worker_engine(cycle)
    strategy = read_file(STRATEGY_FILE, "No strategy file. Work on the next theorem in plan.md.")
    sorry_locations = get_sorry_locations()

    aristotle_section = ""
    if aristotle_summary:
        aristotle_section = f"""
## Aristotle results from previous cycles (INCORPORATE THESE FIRST)
{aristotle_summary}

**IMPORTANT**: Before starting new work, check these Aristotle results. Read the Lean files
in the result directories, and incorporate any successful proofs into the codebase. Fix partial
proofs if they need minor edits. This is free work — do not ignore it.
"""

    prompt = f"""You are the worker for cycle {cycle} of an autonomous Lean 4 formalization project.

## Project ground truth
- The live textbook on `main` is Arieh Iserles, *A First Course in the Numerical Analysis of Differential Equations*.
- The old `extraction/` pipeline is gone from `main`; do not rely on `extraction/...` paths or Butcher-only metadata.
- Treat `plan.md`, the live Lean files, recent task results, and recent issue files as the source of truth.

## Your strategy (from the planner — FOLLOW THIS)
{strategy}
{aristotle_section}
## Current sorry locations
{sorry_locations}

## File size status
{get_file_size_report()}

## Instructions
1. Follow the strategy above. Do not freelance or cherry-pick easy goals.
2. Use sorry-first workflow: write proof structure with sorry, verify it compiles, then close sorry's.
3. **Aristotle-first workflow (MANDATORY)**: Aristotle is FREE compute — use it aggressively.
   a. After setting up the sorry-first structure, identify ~5 sorry's or sub-lemmas suitable for Aristotle.
   b. Submit ALL of them to Aristotle in batch (use submit_file tool for each).
   c. Sleep for 30 minutes (`sleep 1800`) to let Aristotle work.
   d. Check all Aristotle results.
   e. Incorporate whatever Aristotle proved.
   f. Fix partial proofs from Aristotle if they need minor edits.
   g. Only manually prove what Aristotle completely failed on.
4. Use lean LSP tools (lean_goal, lean_multi_attempt, lean_leansearch, lean_loogle) to find lemmas and prove goals that Aristotle didn't solve.
5. Verify your changes compile: run `lake env lean <file>` before committing.
6. Write `.prover-state/task_results/cycle_{cycle:03d}.md` documenting what you did (include Aristotle job results).
7. If blocked, write an issue file in `.prover-state/issues/`.
8. Commit and push your changes with a descriptive message.
9. A cycle with zero changes is unacceptable. At minimum, decompose a sorry or write an issue.
10. Do not commit a new tracked `OpenMath/*.lean` file with live `sorry`s unless the strategy
    explicitly requires that file and the proof path is part of the current plan target.
11. If you need scratch Lean code or Aristotle scaffolding, keep it under `.prover-state/`,
    not under `OpenMath/`.
12. Do not leave tracked orphan helper modules on `main`.
13. Respect the file size cap. If any existing file is already over the hard cap ({FILE_SIZE_CAP}
    lines, see "File size status"), do NOT add lines to it — instead, extract cohesive helpers
    into a new sub-module and update imports. If the strategy does not already schedule a split,
    treat the split as this cycle's work. If you are mid-refactor and legitimately need a
    temporary net increase, record `SPLITTING_IN_PROGRESS` or `REFACTOR_COMMIT` in the task
    result so the evaluator knows to allow it.

Work autonomously. Do not ask questions. Make progress.
"""
    log(f"Worker engine: {engine}")
    if engine == "codex":
        output = run_codex(prompt, timeout=7200)
    else:
        output = run_claude(prompt, timeout=7200)
    log(f"Worker done ({engine}). Output length: {len(output)}")
    return output


def run_evaluator(cycle: int, pre_sorry_count: int, post_sorry_count: int,
                  worker_output: str, base_rev: str = "") -> dict:
    """Run the evaluator to assess progress. Returns structured evaluation."""
    task_result_file = TASK_RESULTS / f"cycle_{cycle:03d}.md"
    task_result = read_file(task_result_file, "Worker did not write a task result file.")
    attempts = read_recent_text(ATTEMPTS_FILE, 20000, "No previous attempts.")
    diff = git_diff(base_rev=base_rev)
    recent_history = get_recent_history(5)
    history_summary = "\n".join(
        f"  Cycle {h.get('cycle', '?')}: score={h.get('progress_score', '?')}, "
        f"stuck_on={h.get('stuck_on', 'N/A')}"
        for h in recent_history
    ) or "No history yet."

    size_growth = file_size_growth_report(base_rev=base_rev)
    size_growth_section = (
        f"\n## File-size accretion warning\n{size_growth}\n"
        if size_growth else ""
    )

    prompt = f"""You are the evaluator for an autonomous Lean 4 formalization project.
Assess the worker's progress in cycle {cycle}.

## Sorry count change
Before: {pre_sorry_count} → After: {post_sorry_count}

## Git diff
{diff}

## Task result written by worker
{task_result}

## Previous attempt history
{attempts}

## Recent evaluation history
{history_summary}

## Worker output
{worker_output[:50000]}

## Important bookkeeping note
The orchestrator appends the current cycle to `history.jsonl` and advances
`.prover-state/cycle` only after evaluation. Do NOT penalize the worker merely
because those current-cycle bookkeeping updates are absent from the diff.
{size_growth_section}
## Your job
Output a JSON object with these fields:
- "progress_score": integer from -2 to +2
  - -2: regression (build broken, sorry count increased without justification)
  - -1: stall with wasted effort (repeated failed approach, OR net-adding lines to
        a file already over the {FILE_SIZE_CAP}-line hard cap without a declared
        split/refactor)
  - 0: stall but reasonable (exploration, infrastructure)
  - +1: minor progress (decomposition, infrastructure, partial proof)
  - +2: solid progress (sorry closed, significant advancement)
- "summary": one sentence describing what happened
- "stuck_on": what's blocking progress (empty string if not stuck)
- "strategy_recommendation": what the planner should consider next cycle
- "attempts_update": new entry for attempts.md (compact description of what was tried and failed, empty if nothing new to record)

Respond with ONLY the JSON object, no other text.
"""
    output = run_claude(prompt, model="sonnet", timeout=1800, json_output=True)

    # Parse JSON from output
    try:
        result = parse_evaluator_output(output)
    except (json.JSONDecodeError, AttributeError, ValueError) as e:
        log(f"Failed to parse evaluator output as JSON: {e}")
        log(f"Failed to parse evaluator output as JSON: {output[:500]}")
        result = {
            "progress_score": 0,
            "summary": "Evaluator output could not be parsed",
            "stuck_on": "",
            "strategy_recommendation": "Continue with current strategy",
            "attempts_update": "",
        }

    result["cycle"] = cycle
    result["engine"] = get_worker_engine(cycle)
    result["pre_sorry_count"] = pre_sorry_count
    result["post_sorry_count"] = post_sorry_count
    result["timestamp"] = datetime.now(timezone.utc).isoformat()

    log(f"Evaluator: score={result.get('progress_score')}, "
        f"engine={result.get('engine')}, summary={result.get('summary', 'N/A')}")
    return result


def run_consultant(cycle: int) -> str:
    """Run the consultant for mathematical advice when stuck."""
    sorry_locations = get_sorry_locations()
    attempts = read_recent_text(ATTEMPTS_FILE, 20000, "No previous attempts.")

    issues_text = get_recent_issue_text(limit=12)

    recent_history = get_recent_history(10)
    stuck_on = ""
    for h in reversed(recent_history):
        if h.get("stuck_on"):
            stuck_on = h["stuck_on"]
            break

    prompt = f"""I'm formalizing a numerical analysis textbook in Lean 4 / Mathlib and I'm stuck.

## What I'm stuck on
{stuck_on}

## Current sorry locations
{sorry_locations}

## What has been tried and failed
{attempts}

## Open issues / blockers
{issues_text}

Please suggest:
1. The mathematical argument that should work here
2. Relevant Mathlib theories or lemmas (search for them using lean_leansearch or lean_loogle)
3. An alternative proof strategy if the current approach is wrong
4. Concrete Lean 4 tactic suggestions

Write your advice to `.prover-state/issues/consultant_advice_cycle_{cycle:03d}.md`.
"""
    output = run_claude(prompt, timeout=3600)
    log(f"Consultant done. Output length: {len(output)}")
    return output


# ─── Mechanical gates ─────────────────────────────────────────────────────────

def verirefine_gate(pre_count: int, post_count: int, cycle: int) -> bool:
    """Check VeriRefine: sorry count should not increase.

    Returns True if the gate passes (ok to proceed).
    """
    if post_count <= pre_count:
        return True

    # Check for restructuring declaration
    task_result_file = TASK_RESULTS / f"cycle_{cycle:03d}.md"
    task_result = read_file(task_result_file, "")
    if "RESTRUCTURING_IN_PROGRESS" in task_result:
        # Allow temporary increase for up to RESTRUCTURING_BUDGET cycles
        recent = get_recent_history(RESTRUCTURING_BUDGET)
        restructuring_cycles = sum(
            1 for h in recent
            if h.get("post_sorry_count", 0) > h.get("pre_sorry_count", 0)
        )
        if restructuring_cycles < RESTRUCTURING_BUDGET:
            log(f"VeriRefine: sorry count increased ({pre_count}→{post_count}) "
                f"but RESTRUCTURING_IN_PROGRESS declared "
                f"({restructuring_cycles+1}/{RESTRUCTURING_BUDGET} budget)")
            return True
        else:
            log(f"VeriRefine: restructuring budget exhausted")

    log(f"VeriRefine FAILED: sorry count increased {pre_count}→{post_count}")
    return False


def check_budget_cap() -> Optional[str]:
    """Check if any sorry has been stuck for too long. Returns the sorry if so."""
    recent = get_recent_history(BUDGET_CAP)
    if len(recent) < BUDGET_CAP:
        return None

    # Check if all recent cycles are stuck on the same thing
    stuck_topics = [h.get("stuck_on", "") for h in recent]
    stuck_topics = [t for t in stuck_topics if t]

    if len(stuck_topics) >= BUDGET_CAP:
        # Check if they're all about the same thing (rough check)
        if len(set(stuck_topics)) <= 2:  # same 1-2 topics
            return stuck_topics[-1]
    return None


def check_strategy_compliance(cycle: int, base_rev: str = "") -> Optional[str]:
    """Check if the worker touched files mentioned in strategy.md.

    Returns a warning string if the worker deviated, None if compliant.
    """
    strategy = read_file(STRATEGY_FILE, "")
    if not strategy:
        return None

    # Extract file paths mentioned in strategy (OpenMath/Foo.lean patterns)
    target_files = set(re.findall(r'(OpenMath/\w+\.lean)', strategy))
    if not target_files:
        return None

    changed_files = git_changed_files(base_rev=base_rev)

    touched_targets = target_files & changed_files
    if not touched_targets and target_files:
        return (
            f"STRATEGY DEVIATION: Strategy mentioned {target_files} "
            f"but worker only touched {changed_files or 'nothing'}. "
            f"Worker may be freelancing instead of following the plan."
        )
    return None


# ─── Main cycle ───────────────────────────────────────────────────────────────

def run_cycle(cycle: int, worker_only: bool = False, skip_planner: bool = False):
    """Run one full cycle of the autonomous loop."""
    log(f"═══ Starting cycle {cycle} ═══")
    set_cycle(cycle)
    write_heartbeat(cycle, "starting")

    # Discover Telegram chat_id if needed
    telegram_discover_chat_id()

    # Pull latest
    git_pull()

    # ── CI Check ──
    ci = check_ci_status()
    log(f"CI status: {ci['status']}")
    ci_failing = ci["status"] == "failure"
    if ci_failing:
        log(f"CI FAILING: {ci['details'][:500]}")

    # ── Aristotle Harvest ──
    log("── Checking Aristotle results ──")
    aristotle_summary = aristotle_harvest()

    # Pre-cycle state
    pre_sorry_count = count_sorries()
    log(f"Pre-cycle sorry count: {pre_sorry_count}")

    # If CI is failing, override strategy to fix it first
    if ci_failing:
        ci_strategy = (
            "# Strategy — CI FIX REQUIRED\n\n"
            "**The CI build is broken.** This is the top priority. "
            "Fix the build errors before doing ANY other work.\n\n"
            "## CI errors\n"
            f"```\n{ci['details']}\n```\n\n"
            "## Instructions\n"
            "1. Read the failing files and fix the errors\n"
            "2. Verify each fix compiles: `lake env lean OpenMath/Foo.lean`\n"
            "3. Commit and push the fix\n"
            "4. Only after CI is fixed, proceed with normal strategy\n"
        )
        STRATEGY_FILE.write_text(ci_strategy)
        log("Wrote CI-fix strategy override")

    # ── Planner ──
    elif not worker_only and not skip_planner:
        log("── Running Planner ──")
        write_heartbeat(cycle, "planner")
        run_planner(cycle, aristotle_summary=aristotle_summary)
    elif not STRATEGY_FILE.exists():
        # Write a default strategy if none exists
        STRATEGY_FILE.write_text(
            "# Strategy\n\nWork on the next theorem in plan.md. "
            "Follow the sorry-first workflow.\n"
        )

    cycle_base_rev = git_head()

    # ── Worker ──
    log("── Running Worker ──")
    write_heartbeat(cycle, "worker")
    worker_output = run_worker(cycle, aristotle_summary=aristotle_summary)

    # Post-cycle state
    post_sorry_count = count_sorries()
    log(f"Post-cycle sorry count: {post_sorry_count} (delta: {post_sorry_count - pre_sorry_count:+d})")

    engine = get_worker_engine(cycle)

    if worker_only:
        # Phase 1: minimal evaluation
        evaluation = {
            "cycle": cycle,
            "engine": engine,
            "pre_sorry_count": pre_sorry_count,
            "post_sorry_count": post_sorry_count,
            "progress_score": 1 if post_sorry_count < pre_sorry_count else 0,
            "summary": f"Sorry count: {pre_sorry_count}→{post_sorry_count}",
            "stuck_on": "",
            "strategy_recommendation": "",
            "attempts_update": "",
            "timestamp": datetime.now(timezone.utc).isoformat(),
        }
    else:
        # ── Evaluator ──
        log("── Running Evaluator ──")
        write_heartbeat(cycle, "evaluator")
        evaluation = run_evaluator(cycle, pre_sorry_count, post_sorry_count,
                                   worker_output, base_rev=cycle_base_rev)

        # ── Mechanical Gates ──
        log("── Checking Mechanical Gates ──")

        # VeriRefine
        if not verirefine_gate(pre_sorry_count, post_sorry_count, cycle):
            log("VeriRefine gate failed — reverting changes")
            raw_post_sorry_count = post_sorry_count
            reverted = git_revert_cycle_commits(cycle_base_rev, cycle)
            if not reverted:
                git_revert_changes()
            post_sorry_count = count_sorries()
            evaluation["progress_score"] = -2
            evaluation["summary"] = (
                f"REVERTED: sorry count increased {pre_sorry_count}→{raw_post_sorry_count}"
            )
            evaluation["post_sorry_count"] = post_sorry_count

        # Budget cap
        budget_stuck = check_budget_cap()
        if budget_stuck:
            log(f"Budget cap hit: stuck on '{budget_stuck}' for {BUDGET_CAP} cycles")
            evaluation["strategy_recommendation"] = (
                f"BUDGET CAP: Abandon '{budget_stuck}' temporarily. "
                f"Work on something else and return later."
            )

        # Strategy compliance
        deviation = check_strategy_compliance(cycle, base_rev=cycle_base_rev)
        if deviation:
            log(f"Strategy compliance: {deviation}")
            evaluation["strategy_deviation"] = deviation
            # Cap score at 0 if worker ignored strategy — good work doesn't
            # count if it's not what was asked for.
            if evaluation.get("progress_score", 0) > 0:
                log("Capping score to 0 due to strategy deviation")
                evaluation["progress_score"] = 0
                evaluation["summary"] = (
                    f"OFF-STRATEGY: {evaluation.get('summary', '')} "
                    f"[Worker ignored assigned files]"
                )

        # ── Consultant ──
        consecutive_stalls = 0
        for h in reversed(get_recent_history(STUCK_THRESHOLD)):
            if h.get("progress_score", 1) <= 0:
                consecutive_stalls += 1
            else:
                break

        if consecutive_stalls >= STUCK_THRESHOLD:
            log(f"── Running Consultant (stuck for {consecutive_stalls} cycles) ──")
            write_heartbeat(cycle, "consultant")
            run_consultant(cycle)

        # Update attempts.md only after mechanical gates settle the final state.
        new_attempt = evaluation.get("attempts_update", "")
        if new_attempt:
            with open(ATTEMPTS_FILE, "a") as f:
                f.write(f"\n### Cycle {cycle}\n{new_attempt}\n")

    # ── Record history ──
    append_history(evaluation)
    set_cycle(cycle)

    # ── Telegram alert ──
    delta = post_sorry_count - pre_sorry_count
    score = evaluation.get("progress_score", 0)
    summary = evaluation.get("summary", "N/A")

    if score >= 1:
        emoji = "🟢"
    elif score == 0:
        emoji = "🟡"
    elif score == -1:
        emoji = "🟠"
    else:
        emoji = "🔴"

    stuck_info = ""
    if evaluation.get("stuck_on"):
        consecutive = 0
        for h in reversed(get_recent_history(20)):
            if h.get("progress_score", 1) <= 0:
                consecutive += 1
            else:
                break
        if consecutive > 1:
            stuck_info = f" — stuck {consecutive} cycles"

    engine_tag = f" [{engine}]"
    alert = (
        f"{emoji} *Cycle {cycle}*{engine_tag} (sorry: {pre_sorry_count}→{post_sorry_count})"
        f"{stuck_info}\n{summary}"
    )
    telegram_send(alert)

    # Cleanup sweep — runs at most once per SWEEP_INTERVAL_HOURS, from inside
    # the pipeline so state access and logging stay local. Touches only
    # `.prover-state/` subdirectories; never the OpenMath/ source tree.
    try:
        maybe_run_cleanup_sweep(cycle)
    except Exception as e:
        log(f"sweep: top-level failure: {e}")

    log(f"═══ Cycle {cycle} complete ═══\n")
    return evaluation


# ─── Main ─────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(description="OpenMath autonomous formalization loop")
    parser.add_argument("--loop", action="store_true", help="Run continuously")
    parser.add_argument("--once", action="store_true", help="Run one cycle")
    parser.add_argument("--worker-only", action="store_true",
                        help="Phase 1: worker only (no planner/evaluator/consultant)")
    parser.add_argument("--interval", type=int, default=DEFAULT_COOLDOWN,
                        help=f"Cooldown between cycles in seconds (default: {DEFAULT_COOLDOWN})")
    parser.add_argument("--skip-planner", action="store_true",
                        help="Skip planner (use existing strategy.md)")
    parser.add_argument("--watchdog", action="store_true",
                        help="Run as watchdog: monitor loop health and restart if dead")
    parser.add_argument("--watchdog-interval", type=int, default=300,
                        help="Watchdog check interval in seconds (default: 300)")
    parser.add_argument("--watchdog-max-restarts", type=int, default=10,
                        help="Max consecutive restart attempts before giving up (default: 10)")
    args = parser.parse_args()

    if args.watchdog:
        run_watchdog(interval=args.watchdog_interval,
                     max_restarts=args.watchdog_max_restarts)
        return

    if not args.loop and not args.once:
        parser.print_help()
        sys.exit(1)

    # Ensure state directories exist
    TASK_RESULTS.mkdir(parents=True, exist_ok=True)
    ISSUES.mkdir(parents=True, exist_ok=True)
    ARISTOTLE_RESULTS_DIR.mkdir(parents=True, exist_ok=True)

    # File lock
    lock_fd = open(LOCK_FILE, "w")
    try:
        fcntl.flock(lock_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        log("Another instance is running (lock file held). Exiting.")
        sys.exit(1)

    log("OpenMath autonomous formalization loop starting")
    log(f"Mode: {'loop' if args.loop else 'once'}, "
        f"worker_only={args.worker_only}, interval={args.interval}s")

    telegram_discover_chat_id()
    telegram_send("🚀 *OpenMath autonomous loop started*\n"
                  f"Mode: {'continuous' if args.loop else 'single cycle'}")

    try:
        if args.once:
            cycle = get_cycle() + 1
            run_cycle(cycle, worker_only=args.worker_only,
                      skip_planner=args.skip_planner)
        elif args.loop:
            while True:
                cycle = get_cycle() + 1
                try:
                    run_cycle(cycle, worker_only=args.worker_only,
                              skip_planner=args.skip_planner)
                except KeyboardInterrupt:
                    raise
                except Exception as e:
                    log(f"Cycle {cycle} failed with exception: {e}")
                    telegram_send(f"💥 *Cycle {cycle} EXCEPTION*\n`{str(e)[:200]}`")
                    import traceback
                    traceback.print_exc()

                log(f"Cooling down for {args.interval}s...")
                write_heartbeat(cycle, "cooldown")
                time.sleep(args.interval)
    except KeyboardInterrupt:
        log("Interrupted by user")
        telegram_send("⏹️ *OpenMath autonomous loop stopped* (user interrupt)")
    finally:
        fcntl.flock(lock_fd, fcntl.LOCK_UN)
        lock_fd.close()


if __name__ == "__main__":
    main()
