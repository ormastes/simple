#!/usr/bin/env bash
set -euo pipefail

# Launch the host DBC daemon binary that mirrors shadow doorbells to MMIO.
# Usage: sudo SHADOW_HEX=0x7f... ./host_dbc_daemon_task.sh [standard|realtime] [device_path] [qid]

if [[ ${EUID:-$(id -u)} -ne 0 ]]; then
  echo "This helper must run with sudo. Example: sudo SHADOW_HEX=0x... $0"
  exit 1
fi

mode="${1:-standard}"
device_path="${2:-/dev/nvme0}"
queue_id="${3:-1}"

# Kill any pre-existing daemon processes to avoid conflicts
echo "[host_dbc_daemon_task] Cleaning up any pre-existing daemon processes..."
pkill -9 -f "host_dbc_daemon" 2>/dev/null || true
pkill -9 -f "host_dbc_daemon_realtime" 2>/dev/null || true
sleep 0.5  # Wait for processes to terminate

if [[ -z "${SHADOW_HEX:-}" ]]; then
  echo "Set SHADOW_HEX to the shadow doorbell buffer host pointer (hex) before running."
  exit 1
fi

binary="host_dbc_daemon"
[[ "${mode}" == "realtime" ]] && binary="host_dbc_daemon_realtime"

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="${script_dir%/50.GPU-NVMe_Interaction/*}"
candidate="${repo_root}/build/50.GPU-NVMe_Interaction/53.NVMe_VFIO_Host_Layer/daemon/${binary}"

if [[ ! -x "${candidate}" ]]; then
  echo "[host_dbc_daemon_task] Binary not found at ${candidate}"
  echo "Build it first (e.g., ninja -C build ${binary})"
  exit 1
fi

echo "[host_dbc_daemon_task] Starting ${binary} shadow=${SHADOW_HEX} device=${device_path} qid=${queue_id}"
exec "${candidate}" --device "${device_path}" --shadow "${SHADOW_HEX}" --qid "${queue_id}"
