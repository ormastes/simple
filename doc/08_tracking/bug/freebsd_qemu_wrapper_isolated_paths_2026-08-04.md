# FreeBSD QEMU wrapper ignores isolated runtime artifact paths

- **ID:** freebsd_qemu_wrapper_isolated_paths_2026-08-04
- **Date:** 2026-08-04
- **Area:** FreeBSD QEMU bootstrap wrapper
- **Severity:** medium — concurrent or forensic runs can overwrite each other's
  overlay, serial, start, and PID artifacts despite separate base image and
  cloud-init paths.
- **Status:** FIXED IN SOURCE — live QEMU rerun intentionally deferred

## What happens

`scripts/check/check-freebsd-bootstrap-qemu.shs` accepts `QEMU_VM_PATH` and
`QEMU_CLOUDINIT_ISO`, but still derives `freebsd-run.overlay.qcow2`,
`qemu-serial.log`, `qemu-start.log`, and `qemu.pid` from the shared
`build/freebsd/vm` directory. An isolated run can therefore terminate or
overwrite evidence belonging to another run.

## Fix direction

Add explicit runtime-artifact path knobs, preserving the existing
`build/freebsd/vm` defaults. The wrapper must create the parent directories
for every selected artifact and a shell contract test must prove that all
mutable QEMU paths derive from the isolated configuration.

## Resolution

The wrapper now accepts `QEMU_RUNTIME_DIR`, with individually overrideable
`QEMU_OVERLAY_IMAGE`, `QEMU_PID_FILE`, `QEMU_SERIAL_LOG`, `QEMU_START_LOG`, and
`QEMU_CLOUDINIT_DIR` paths. Each defaults beneath `QEMU_RUNTIME_DIR`, which in
turn defaults to the historical `build/freebsd/vm` location. Parent directories
are created before use, so a caller can place every mutable artifact in an
isolated directory while retaining separately selected base-image and ISO paths.

Focused verification:

```text
sh -n scripts/check/check-freebsd-bootstrap-qemu.shs
sh test/02_integration/freebsd_bootstrap_qemu_isolation_contract_test.shs
freebsd_bootstrap_qemu_isolation_contract=true
```

The contract test is intentionally static: it validates isolation plumbing
without downloading an image or launching QEMU. A fresh live QEMU smoke remains
required as separate evidence.
