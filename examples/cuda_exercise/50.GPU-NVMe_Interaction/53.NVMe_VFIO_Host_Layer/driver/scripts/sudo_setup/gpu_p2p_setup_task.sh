#!/usr/bin/env bash
set -euo pipefail

# Build and load the GPU P2P kernel modules so /dev/gpu_p2p_nvme is available.
# Also performs the platform checks that were previously in setup_p2p.sh.
# Usage: sudo ./gpu_p2p_setup_task.sh

if [[ ${EUID:-$(id -u)} -ne 0 ]]; then
  echo "This helper must run with sudo. Example: sudo $0"
  exit 1
fi

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
driver_dir="${script_dir}/../.."

echo "[gpu_p2p_setup_task] Checking IOMMU/ACS state..."
if dmesg | grep -qi "IOMMU disabled"; then
  echo "WARNING: IOMMU appears disabled; P2P/VFIO may fail."
fi
if lspci -vv | grep -q \"ACSCtl\"; then
  echo "NOTE: ACS present; ensure P2P path is allowed (pci=noacs or BIOS toggle)."
fi

echo "[gpu_p2p_setup_task] Building and loading dual-driver modules..."
pushd "${driver_dir}" >/dev/null
make -f Makefile.dual load
popd >/dev/null

echo "[gpu_p2p_setup_task] Verifying CUDA P2P tokens (Modes 5/6 require non-zero token)..."
if ! "${driver_dir}/scripts/check_p2p_token.sh"; then
  echo "[gpu_p2p_setup_task] ERROR: P2P token is 0. Driver is loaded but not exposing peer tokens."
  echo "  Fix by rebuilding against the running NVIDIA driver, reloading modules, or disabling MIG/VGPU."
  exit 1
fi

echo "[gpu_p2p_setup_task] Setting permissions on /dev/gpu_p2p_core for non-root access..."
if [[ -c /dev/gpu_p2p_core ]]; then
  chmod 666 /dev/gpu_p2p_core
  echo "[gpu_p2p_setup_task] /dev/gpu_p2p_core permissions set to 666"
else
  echo "[gpu_p2p_setup_task] WARNING: /dev/gpu_p2p_core not found"
fi

echo "[gpu_p2p_setup_task] Done. Verify with: ls -l /dev/gpu_p2p_nvme"
