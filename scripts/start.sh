#!/bin/bash
# Start the OpenMath autonomous formalization loop on Hyak.
#
# This script handles everything after getting a new interactive node:
#   1. Restores NVMe toolchain + Mathlib cache (if /tmp was wiped)
#   2. Sets up the crontab for the 12h monitor
#   3. Starts the autonomous loop in the background
#
# Usage:
#   bash scripts/start.sh           # full setup + start loop
#   bash scripts/start.sh --restore # only restore NVMe, don't start loop
#
# === FOR COLLABORATORS ===
# Before running this script, you need:
#   1. A .env file in the project root with:
#        ARISTOTLE_API_KEY=<your key>
#        TELEGRAM_BOT_TOKEN=<your bot token>    (optional)
#        TELEGRAM_CHAT_ID=<your chat id>        (optional)
#   2. Claude Code CLI installed (`claude` on PATH)
#   3. An elan toolchain — set ELAN_TOOLCHAIN below to your path
#   4. (Optional) Codex CLI in a conda env — set CODEX_CONDA_ENV below
#   5. (Optional) lean-lsp-mcp and aristotle-mcp for MCP tools
# ========================

set -euo pipefail

PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$PROJECT_ROOT"

# ─── User-configurable paths ────────────────────────────────────────────────
# Change these if you're not vilin or your paths differ.

# Where the lean toolchain lives on persistent storage (GPFS)
ELAN_TOOLCHAIN="${ELAN_TOOLCHAIN:-/gscratch/amath/vilin/.elan/toolchains/leanprover--lean4---v4.28.0}"

# Conda env with codex + node.js (set to "" to disable codex)
CODEX_CONDA_ENV="${CODEX_CONDA_ENV:-/gscratch/amath/vilin/conda/envs/codex}"

# Conda env with curl (for lake cache downloads)
CONDA_CURL="${CONDA_CURL:-/gscratch/amath/vilin/conda/envs/curl-env/bin/curl}"

# ─── NVMe paths (don't change unless you know what you're doing) ─────────
NVME_TOOLCHAIN="/tmp/lean4-toolchain"
LAKE_DIR="/tmp/OpenMath-lake"
LAKE_WRAPPER="/tmp/lake-bin/lake"
LOG_DIR="$PROJECT_ROOT/.prover-state"

# ─── Parse args ──────────────────────────────────────────────────────────────
RESTORE_ONLY=false
if [[ "${1:-}" == "--restore" ]]; then
    RESTORE_ONLY=true
fi

# ─── Step 1: Restore NVMe toolchain ─────────────────────────────────────────
echo "=== Step 1: NVMe Toolchain ==="

if [ -d "$NVME_TOOLCHAIN/bin" ] && "$NVME_TOOLCHAIN/bin/lean" --version &>/dev/null; then
    echo "  [OK] Lean toolchain at $NVME_TOOLCHAIN"
else
    if [ ! -d "$ELAN_TOOLCHAIN" ]; then
        echo "  [ERROR] Elan toolchain not found at $ELAN_TOOLCHAIN"
        echo "  Set ELAN_TOOLCHAIN env var to your lean toolchain path"
        exit 1
    fi
    echo "  Copying lean toolchain to NVMe..."
    rm -rf "$NVME_TOOLCHAIN"
    cp -a "$ELAN_TOOLCHAIN" "$NVME_TOOLCHAIN"
    echo "  [OK] Copied"
fi

# ─── Step 2: Lake wrapper ───────────────────────────────────────────────────
echo "=== Step 2: Lake Wrapper ==="
mkdir -p /tmp/lake-bin
cat > "$LAKE_WRAPPER" << 'WRAPPER'
#!/bin/bash
for arg in "$@"; do
    if [[ "$arg" == "proofwidgets:release" ]]; then
        exit 0
    fi
done
exec /tmp/lean4-toolchain/bin/lake "$@"
WRAPPER
chmod +x "$LAKE_WRAPPER"
echo "  [OK] Lake wrapper at $LAKE_WRAPPER"

# ─── Step 3: .lake symlink + Mathlib cache ──────────────────────────────────
echo "=== Step 3: Mathlib Cache ==="

# Ensure .lake points to NVMe
ln -sfn "$LAKE_DIR" "$PROJECT_ROOT/.lake"

if [ -d "$LAKE_DIR/packages/mathlib/.lake/build/lib/lean/Mathlib" ]; then
    echo "  [OK] Mathlib oleans present"
else
    mkdir -p "$LAKE_DIR"

    # Fix curl used by `lake exe cache get`.
    # The static curl-7.88.1 (OpenSSL 3.0.8) breaks on EL8 (GLIBC_2.28 / OpenSSL "unregistered scheme").
    # Replace it with the working conda curl at all possible HOME-resolved cache dirs.
    if [ -n "$CONDA_CURL" ] && [ -e "$CONDA_CURL" ]; then
        for cache_base in "$HOME/.cache/mathlib" "/gscratch/amath/vilin/.cache/mathlib"; do
            [ -z "$cache_base" ] && continue
            # Remove broken symlink at the directory path (e.g. from wiped /tmp)
            if [ -L "$cache_base" ] && [ ! -e "$cache_base" ]; then
                rm "$cache_base"
            fi
            mkdir -p "$cache_base" 2>/dev/null || true
            ln -sfn "$CONDA_CURL" "$cache_base/curl-7.88.1"
        done
    fi

    export PATH="/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH"
    # Use system gcc — the bundled clang requires GLIBC_2.29 but EL8 has 2.28
    # Also add toolchain lib to linker search path for libc++, libgmp, libuv
    export LEAN_CC=/usr/bin/gcc
    export LIBRARY_PATH="/tmp/lean4-toolchain/lib:${LIBRARY_PATH:-}"
    echo "  Fetching Mathlib cache (this takes a few minutes)..."
    lake exe cache get || true
    # Verify the cache actually has oleans despite possible non-zero exit
    if [ -d "$LAKE_DIR/packages/mathlib/.lake/build/lib/lean/Mathlib" ]; then
        echo "  [OK] Mathlib cache restored"
    else
        echo "  [ERROR] Mathlib oleans not found after cache get"
        exit 1
    fi
fi

# ─── Step 4: Verify ─────────────────────────────────────────────────────────
echo "=== Verification ==="
"$NVME_TOOLCHAIN/bin/lean" --version
OLEAN_COUNT=$(find "$LAKE_DIR/packages/mathlib/.lake/build/lib/lean/Mathlib" -name "*.olean" 2>/dev/null | wc -l)
echo "  Mathlib oleans: $OLEAN_COUNT files"
echo "  .lake -> $(readlink "$PROJECT_ROOT/.lake")"

if $RESTORE_ONLY; then
    echo ""
    echo "=== Restore complete (--restore mode) ==="
    exit 0
fi

# ─── Step 5: Crontab (12h monitor) ──────────────────────────────────────────
echo "=== Step 5: Crontab ==="
MONITOR_CMD="/usr/bin/python3 $PROJECT_ROOT/scripts/monitor_loop.py >> $LOG_DIR/monitor_cron.log 2>&1"

if crontab -l 2>/dev/null | grep -q "monitor_loop.py"; then
    echo "  [OK] Monitor cron job already installed"
else
    (crontab -l 2>/dev/null; echo "7 */12 * * * $MONITOR_CMD") | crontab -
    echo "  [OK] Installed 12h monitor cron job"
fi

# ─── Step 6: Start the loop ─────────────────────────────────────────────────
echo "=== Step 6: Starting Loop ==="

if pgrep -f "autonomous_loop.py" > /dev/null 2>&1; then
    echo "  [SKIP] Loop already running (PID $(pgrep -f autonomous_loop.py | head -1))"
else
    mkdir -p "$LOG_DIR/task_results" "$LOG_DIR/issues"
    nohup python3 "$PROJECT_ROOT/scripts/autonomous_loop.py" --loop \
        >> /tmp/autonomous_loop.log 2>&1 &
    LOOP_PID=$!
    sleep 2
    if kill -0 $LOOP_PID 2>/dev/null; then
        echo "  [OK] Loop started (PID $LOOP_PID)"
        echo "  Logs: /tmp/autonomous_loop.log"
    else
        echo "  [ERROR] Loop failed to start — check /tmp/autonomous_loop.log"
        exit 1
    fi
fi

echo ""
echo "=== All done ==="
echo "Monitor: cron every 12h"
echo "Loop: running (cooldown 5min between cycles)"
echo "Telegram alerts: $([ -f "$PROJECT_ROOT/.env" ] && grep -q TELEGRAM "$PROJECT_ROOT/.env" && echo 'configured' || echo 'not configured')"
