#!/bin/bash
# Restore NVMe toolchain and Mathlib cache after /tmp wipe (Hyak maintenance).
# Usage: bash scripts/restore_nvme.sh
set -euo pipefail

# Prefer /gscratch copy (more space, ~ may be cleaned)
if [ -d "/gscratch/amath/vilin/.elan/toolchains/leanprover--lean4---v4.28.0" ]; then
    ELAN_TOOLCHAIN="/gscratch/amath/vilin/.elan/toolchains/leanprover--lean4---v4.28.0"
else
    ELAN_TOOLCHAIN="$HOME/.elan/toolchains/leanprover--lean4---v4.28.0"
fi
NVME_TOOLCHAIN="/tmp/lean4-toolchain"
LAKE_DIR="/tmp/OpenMath-lake"
LAKE_WRAPPER="/tmp/lake-bin/lake"
PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"

echo "=== Restoring NVMe toolchain and cache ==="

# 1. Copy lean toolchain from GPFS to NVMe
if [ -d "$NVME_TOOLCHAIN/bin" ] && "$NVME_TOOLCHAIN/bin/lean" --version &>/dev/null; then
    echo "✓ Lean toolchain already at $NVME_TOOLCHAIN"
else
    echo "Copying lean toolchain to NVMe..."
    rm -rf "$NVME_TOOLCHAIN"
    cp -a "$ELAN_TOOLCHAIN" "$NVME_TOOLCHAIN"
    echo "✓ Lean toolchain copied"
fi

# 2. Create lake wrapper
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
echo "✓ Lake wrapper created"

# 3. Restore .lake directory and Mathlib cache
if [ -d "$LAKE_DIR/packages/mathlib/.lake/build/lib/lean/Mathlib" ]; then
    echo "✓ Mathlib oleans already present"
else
    echo "Restoring .lake directory..."
    mkdir -p "$LAKE_DIR"

    # Point .lake symlink
    ln -sfn "$LAKE_DIR" "$PROJECT_ROOT/.lake"

    # Fetch Mathlib cache
    cd "$PROJECT_ROOT"
    export PATH="/tmp/lake-bin:/tmp/lean4-toolchain/bin:$PATH"
    echo "Running lake exe cache get (this takes a few minutes)..."
    lake exe cache get
    echo "✓ Mathlib cache restored"
fi

# 4. Fix curl symlink if needed
CURL_SYMLINK="$HOME/.cache/mathlib/curl-7.88.1"
CONDA_CURL="/gscratch/amath/vilin/conda/envs/curl-env/bin/curl"
if [ -L "$CURL_SYMLINK" ] && [ -e "$CONDA_CURL" ]; then
    echo "✓ Curl symlink OK"
else
    mkdir -p "$(dirname "$CURL_SYMLINK")"
    ln -sfn "$CONDA_CURL" "$CURL_SYMLINK"
    echo "✓ Curl symlink fixed"
fi

# 5. Verify
echo ""
echo "=== Verification ==="
"$NVME_TOOLCHAIN/bin/lean" --version
echo "Lake wrapper: $(ls -la $LAKE_WRAPPER)"
echo ".lake symlink: $(readlink $PROJECT_ROOT/.lake)"
echo "Mathlib oleans: $(ls $LAKE_DIR/packages/mathlib/.lake/build/lib/lean/Mathlib/*.olean 2>/dev/null | wc -l) files"
echo ""
echo "=== Done. You can restart the loop: ==="
echo "  python3 scripts/autonomous_loop.py --loop &"
