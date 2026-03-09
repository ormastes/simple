#!/usr/bin/env bash
set -euo pipefail

# Bind NVMe to vfio-pci outside the test harness.
# Usage: sudo NVME_BDF=0000:41:00.0 ./vfio_binding_task.sh

if [[ ${EUID:-$(id -u)} -ne 0 ]]; then
  echo "This helper must run with sudo. Example: sudo NVME_BDF=0000:41:00.0 $0"
  exit 1
fi

if [[ -z "${NVME_BDF:-}" ]]; then
  echo "Set NVME_BDF (e.g., NVME_BDF=0000:41:00.0) before running."
  exit 1
fi

echo "[vfio_binding_task] Preparing to bind ${NVME_BDF} to vfio-pci"
modprobe vfio-pci

if command -v driverctl >/dev/null 2>&1; then
  echo "[vfio_binding_task] Using driverctl to set override"
  driverctl -v set-override "${NVME_BDF}" vfio-pci
else
  vendor_device=$(lspci -n -s "${NVME_BDF}" | awk '{print $3}')
  if [[ -z "${vendor_device}" ]]; then
    echo "Could not determine vendor/device for ${NVME_BDF}"
    exit 1
  fi
  vendor=${vendor_device%:*}
  device=${vendor_device#*:}
  echo "[vfio_binding_task] Unbinding and rebinding via sysfs (vendor=${vendor} device=${device})"
  if [[ -e "/sys/bus/pci/devices/${NVME_BDF}/driver/unbind" ]]; then
    echo "${NVME_BDF}" >"/sys/bus/pci/devices/${NVME_BDF}/driver/unbind"
  fi
  echo "${vendor} ${device}" >/sys/bus/pci/drivers/vfio-pci/new_id
  echo "${NVME_BDF}" >/sys/bus/pci/drivers/vfio-pci/bind
fi

echo "[vfio_binding_task] Done. Verify with: lspci -k -s ${NVME_BDF}"
