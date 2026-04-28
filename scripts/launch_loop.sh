#!/bin/bash
# Launch the OpenMath autonomous formalization loop.
#
# Per-node bootstrap (NVMe toolchain, lake wrapper, mathlib cache dir) is
# idempotent — re-runnable inside the same allocation without harm.
#
# Usage:
#   scripts/launch_loop.sh                    # default: --loop foreground
#   scripts/launch_loop.sh --once             # one cycle
#   scripts/launch_loop.sh --watchdog         # monitor + restart
#   scripts/launch_loop.sh --loop -b          # background + nohup, log to /tmp
#   scripts/launch_loop.sh --once --clean     # wipe working tree + .prover-state first
#
# Cross-cutting flags:
#   -b, --background   detach via nohup, log to /tmp/autonomous_loop.log
#   --clean            reset working tree and .prover-state before launch
#   -h, --help         show this and exit

set -euo pipefail

MODE="--loop"
CLEAN=0
BACKGROUND=0
for arg in "$@"; do
    case "$arg" in
        --once|--loop|--watchdog) MODE="$arg" ;;
        --clean) CLEAN=1 ;;
        -b|--background) BACKGROUND=1 ;;
        -h|--help) sed -n '2,18p' "$0"; exit 0 ;;
        *) echo "unknown arg: $arg" >&2; exit 1 ;;
    esac
done

PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$PROJECT_ROOT"

ELAN_SRC="/gscratch/amath/vilin/.elan/toolchains/leanprover--lean4---v4.28.0"
CONDA_CURL="/gscratch/amath/vilin/conda/envs/curl-env/bin/curl"
NVME_TOOLCHAIN="/tmp/lean4-toolchain"
LAKE_BIN_DIR="/tmp/lake-bin"
MATHLIB_CACHE="/tmp/mathlib-cache"
LOG_FILE="/tmp/autonomous_loop.log"
PID_FILE="/tmp/autonomous_loop.pid"

step() { printf '\n[%s] %s\n' "$1" "$2"; }
ok()   { printf '  ✓ %s\n' "$1"; }
warn() { printf '  ! %s\n' "$1"; }
fail() { printf '  x %s\n' "$1"; exit 1; }

# ── 1. conda env ─────────────────────────────────────────────────────────────
step 1/6 "Activate conda env (openmath-tools)"
if [ "${CONDA_DEFAULT_ENV:-}" = "openmath-tools" ]; then
    ok "already active"
else
    command -v module >/dev/null 2>&1 || fail "'module' not found — not on a Hyak node?"
    module load conda
    # shellcheck disable=SC1091
    source "$(conda info --base)/etc/profile.d/conda.sh"
    conda activate openmath-tools
    ok "activated: $CONDA_DEFAULT_ENV"
fi

# ── 2. NVMe lean toolchain ───────────────────────────────────────────────────
step 2/6 "NVMe Lean toolchain"
if [ -x "$NVME_TOOLCHAIN/bin/lean" ] && "$NVME_TOOLCHAIN/bin/lean" --version >/dev/null 2>&1; then
    ok "already at $NVME_TOOLCHAIN ($("$NVME_TOOLCHAIN/bin/lean" --version 2>&1 | head -1))"
else
    [ -d "$ELAN_SRC" ] || fail "source toolchain missing: $ELAN_SRC"
    echo "  copying ~3.7G from $ELAN_SRC ..."
    rm -rf "$NVME_TOOLCHAIN"
    cp -a "$ELAN_SRC" "$NVME_TOOLCHAIN"
    ok "copied ($(du -sh "$NVME_TOOLCHAIN" | cut -f1))"
fi

# ── 3. lake wrapper ──────────────────────────────────────────────────────────
step 3/6 "Lake wrapper"
mkdir -p "$LAKE_BIN_DIR"
cat > "$LAKE_BIN_DIR/lake" << 'WRAPPER'
#!/bin/bash
# Skip the proofwidgets:release fetch step (already built); pass everything else through.
for arg in "$@"; do
    if [[ "$arg" == "proofwidgets:release" ]]; then exit 0; fi
done
exec /tmp/lean4-toolchain/bin/lake "$@"
WRAPPER
chmod +x "$LAKE_BIN_DIR/lake"
ok "$LAKE_BIN_DIR/lake"
# ensure the loop subprocess sees these on PATH (autonomous_loop.py also prepends them)
export PATH="$LAKE_BIN_DIR:$NVME_TOOLCHAIN/bin:$PATH"

# ── 4. mathlib cache ─────────────────────────────────────────────────────────
step 4/6 "Mathlib cache (NVMe-backed via symlink in \$HOME)"
mkdir -p "$MATHLIB_CACHE"
# curl wrapper that mathlib's cache fetcher invokes
if [ ! -e "$MATHLIB_CACHE/curl-7.88.1" ]; then
    [ -e "$CONDA_CURL" ] || fail "curl helper source missing: $CONDA_CURL"
    ln -sfn "$CONDA_CURL" "$MATHLIB_CACHE/curl-7.88.1"
fi
# user-side symlink so ~/.cache/mathlib -> /tmp/mathlib-cache
mkdir -p "$HOME/.cache"
if [ ! -L "$HOME/.cache/mathlib" ]; then
    if [ -e "$HOME/.cache/mathlib" ]; then
        warn "~/.cache/mathlib is a real dir; leaving it alone"
    else
        ln -sfn "$MATHLIB_CACHE" "$HOME/.cache/mathlib"
        ok "created symlink ~/.cache/mathlib -> $MATHLIB_CACHE"
    fi
else
    target="$(readlink "$HOME/.cache/mathlib")"
    [ "$target" = "$MATHLIB_CACHE" ] && ok "~/.cache/mathlib -> $target" \
        || warn "~/.cache/mathlib -> $target (not $MATHLIB_CACHE)"
fi
ltar_count=$(ls "$MATHLIB_CACHE"/*.ltar 2>/dev/null | wc -l)
echo "  cached .ltar files: $ltar_count (will fetch missing on first build)"

# ── 5. sanity checks ─────────────────────────────────────────────────────────
step 5/6 "Sanity checks"
problems=0
for b in claude aristotle-mcp uvx gh python3; do
    if command -v "$b" >/dev/null 2>&1; then ok "$b on PATH"
    else warn "$b NOT on PATH"; problems=$((problems+1)); fi
done
if gh auth status >/dev/null 2>&1; then ok "gh authenticated"
else warn "gh not authenticated (CI gate will be inert) — gh auth login"; fi
if [ -f .env ] && grep -q '^TELEGRAM_BOT_TOKEN=' .env; then ok ".env has Telegram token"
else warn ".env missing TELEGRAM_BOT_TOKEN (alerts skipped)"; fi
if [ -f .env ] && grep -q '^ARISTOTLE_API_KEY=' .env; then ok ".env has Aristotle key"
else warn ".env missing ARISTOTLE_API_KEY (Aristotle harvest skipped)"; problems=$((problems+1)); fi
[ "$problems" -gt 0 ] && fail "$problems blocking issue(s) above"

# ── optional clean ───────────────────────────────────────────────────────────
if [ "$CLEAN" -eq 1 ]; then
    echo
    echo "[clean] resetting working tree and .prover-state ..."
    git clean -fd OpenMath/ 2>/dev/null || true
    git checkout -- OpenMath.lean 2>/dev/null || true
    rm -rf .prover-state
    ok "cleaned"
fi

# ── 6. launch ────────────────────────────────────────────────────────────────
step 6/6 "Launch loop (mode=$MODE)"
if [ -f "$PID_FILE" ]; then
    OLD_PID="$(cat "$PID_FILE")"
    if ps -p "$OLD_PID" >/dev/null 2>&1; then
        fail "another loop is already running (PID $OLD_PID). Stop with: kill -TERM -$OLD_PID"
    fi
    rm -f "$PID_FILE"
fi
rm -f .prover-state/run.lock 2>/dev/null || true

if [ "$BACKGROUND" -eq 1 ]; then
    nohup python scripts/autonomous_loop.py "$MODE" > "$LOG_FILE" 2>&1 &
    echo $! > "$PID_FILE"
    ok "launched in background (PID $(cat "$PID_FILE"))"
    echo "  log:   tail -f $LOG_FILE"
    echo "  stop:  kill -TERM -\$(cat $PID_FILE)"
else
    echo "  foreground; Ctrl+C to stop"
    exec python scripts/autonomous_loop.py "$MODE"
fi
