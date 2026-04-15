#!/bin/bash
# WSL Python bridge for T32 MCP — launches python3 with TCP transport
# for cross-boundary communication (WSL cannot use UDP to Windows host).
set -euo pipefail

# --- Detect WSL ---
if [ ! -f /proc/version ]; then
    echo "ERROR: /proc/version not found — not running under Linux/WSL." >&2
    exit 1
fi
if ! grep -qiE 'Microsoft|WSL' /proc/version 2>/dev/null; then
    echo "ERROR: This script is intended for WSL environments only." >&2
    exit 1
fi

# --- Find python3 ---
PYTHON3="$(command -v python3 2>/dev/null || true)"
if [ -z "$PYTHON3" ]; then
    echo "ERROR: python3 not found on PATH. Install with: sudo apt install python3" >&2
    exit 1
fi

# --- Ensure lauterbach.trace32.rcl is available ---
if ! "$PYTHON3" -c "import lauterbach.trace32.rcl" 2>/dev/null; then
    echo "ERROR: Python package 'lauterbach.trace32.rcl' is not installed." >&2
    echo "       Install with: pip3 install lauterbach-trace32-rcl" >&2
    exit 1
fi

# --- Detect Windows host IP ---
T32_RCL_HOST="${T32_RCL_HOST:-}"
if [ -z "$T32_RCL_HOST" ]; then
    # Try /etc/resolv.conf nameserver (works on WSL2)
    T32_RCL_HOST="$(grep -m1 '^nameserver' /etc/resolv.conf 2>/dev/null | awk '{print $2}' || true)"
fi
if [ -z "$T32_RCL_HOST" ]; then
    # Fallback: default gateway from ip route
    T32_RCL_HOST="$(ip route show default 2>/dev/null | awk '{print $3; exit}' || true)"
fi
if [ -z "$T32_RCL_HOST" ]; then
    echo "ERROR: Cannot determine Windows host IP. Set T32_RCL_HOST manually." >&2
    exit 1
fi

# --- Set TCP protocol for cross-boundary RCL ---
export T32_RCL_PROTOCOL="NETTCP"
export T32_RCL_HOST

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BRIDGE_SCRIPT="${SCRIPT_DIR}/t32_python_bridge.py"

if [ ! -f "$BRIDGE_SCRIPT" ]; then
    echo "ERROR: Bridge script not found: $BRIDGE_SCRIPT" >&2
    exit 1
fi

exec "$PYTHON3" "$BRIDGE_SCRIPT" "$@"
