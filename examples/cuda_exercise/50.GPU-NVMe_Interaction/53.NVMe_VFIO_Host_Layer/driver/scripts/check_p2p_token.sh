#!/usr/bin/env bash
set -euo pipefail

# Compile and run a tiny CUDA probe that prints the P2P token and va_space.
# A zero token means the NVIDIA driver is not exposing peer tokens, so GPU
# P2P mappings (Modes 5/6) will fail even if the modules are loaded.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROBE_SRC="${SCRIPT_DIR}/p2p_token_probe.cu"

if [[ ! -f "${PROBE_SRC}" ]]; then
  echo "ERROR: Probe source not found: ${PROBE_SRC}"
  exit 1
fi

if ! command -v nvcc >/dev/null 2>&1; then
  echo "ERROR: nvcc not found in PATH. Run ./scripts/setup_env.sh or load CUDA."
  exit 1
fi

BUILD_DIR="$(mktemp -d)"
trap 'rm -rf "${BUILD_DIR}"' EXIT

PROBE_BIN="${BUILD_DIR}/p2p_token_probe"

nvcc -std=c++17 "${PROBE_SRC}" -o "${PROBE_BIN}" >/dev/null

set +e
"${PROBE_BIN}"
status=$?
set -e

if [[ ${status} -ne 0 ]]; then
  echo ""
  echo "P2P token probe failed (exit ${status}). True GPU P2P is not ready."
  echo "Troubleshooting tips:"
  echo "  - Rebuild and reload the dual P2P modules: sudo make -f Makefile.dual load"
  echo "  - Ensure the running NVIDIA driver matches the toolkit used to build modules"
  echo "  - Disable MIG/virtual GPU partitions; tokens are only exposed on bare metal"
  echo "  - Verify nvidia-peermem/nvidia_p2p symbols are available (dmesg | grep nvidia_p2p)"
  exit ${status}
fi

echo "P2P tokens look good (non-zero). GPU P2P mapping can proceed."
