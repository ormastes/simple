# QEMU System Tests Guide

## Overview

System-level SSpec tests for SimpleOS boot and execution live in `test/03_system/os/qemu/`. Each test boots a real QEMU instance per architecture, executing full end-to-end scenarios. The helper contract is defined in `src/os/qemu_systest_contract.spl`.

## Running System Tests

Export the Simple compiler path, then invoke a specific test:

```bash
export SIMPLE_BOOTSTRAP_DRIVER=bin/release/x86_64-unknown-linux-gnu/simple_seed
bin/simple test test/03_system/os/qemu/sys_qemu_riscv64_fs_exec_spec.spl
```

The bootstrap driver is required because system-level tests execute compiled binaries, not interpreter mode.

## Direct Boot Fallback

While P1 system-test automation is open, use direct `qemu-system-*` commands for manual verification. This is the known-good riscv64 boot command:

```bash
qemu-system-riscv64 \
  -machine virt \
  -m 512M \
  -nographic \
  -bios default \
  -global virtio-mmio.force-legacy=false \
  -drive file=build/os/fat32-riscv64.img,if=none,id=rvdisk,format=raw \
  -device virtio-blk-device,drive=rvdisk \
  -kernel build/os/simpleos_riscv64_smf_fs.elf
```

## Pass Markers

Serial output must contain ALL of these to qualify as a pass:
- `SIMPLEOS_RISCV_SMF_FS_PASS`
- `TEST PASSED`
- `ELF_LOAD_OK`
- `SMF_CLI_LAUNCH_OK`

**Fail-closed rule:** Serial output containing either of these is NEVER a pass, even if other markers are present:
- `[launcher] fallback=resident-manifest`
- `[desktop-e2e] resident-fallback:active`

See `src/os/fs_exec_fallback_contract.spl` for the full fallback contract.

## Telnet-over-Serial Observation

A system test can observe the guest console over a telnet socket instead of
reading the serial file directly, exercising the same path a real board would
use. `scripts/qemu/check_simpleos_riscv_telnet_serial.shs` boots SimpleOS RV64
on `qemu-system-riscv64 -machine virt` (OpenSBI) with `-serial file:$rx`, then
the telnet-over-serial bridge (`std.nogc_sync_mut.io.telnet_serial_bridge`)
relays `$rx` to a TCP telnet port where a telnet client waits for a real kernel
marker (`SimpleOS RV64`). The QEMU `-serial file:` output *is* the bridge's
read path — no glue needed. This is the emulation counterpart of the physical
KV260 path in `doc/07_guide/hardware/fpga/kv260_rv64gc_fpga_boot.md` (Section 8);
point `QEMU_RX`/`SERIAL_PORT` at a real tty to validate silicon with the same
harness.

## Known Blockers

The `/bin/simple os` subcommands (e.g., `bin/simple os test`) are currently broken per `doc/08_tracking/bug/interp_simpleos_lane_contract_crash_2026-06-13.md`. System tests therefore boot `qemu-system-*` directly rather than through the compiler tool.

## Alpine-Class Hardening Specs (RED until build target exists)

Three new specs in `test/03_system/os/qemu/os/harden/` exercise the SimpleOS x86_64 hardening
probe. All classify MISSING-MEDIA (RED) until `build/os/simpleos_x86_64_harden_probe.elf` and
`build/os/fat32-x86_64-harden.img` are produced by the harden probe build target
(see `doc/08_tracking/bug/simpleos_harden_probe_build_target_2026-06-28.md`).

| Spec | AC | Markers |
|------|----|---------|
| `os/harden/cap_exec_gate_spec.spl` | AC-1 | `[exec] capability gate: ENFORCED`, `[exec] uncapable exec REJECTED` |
| `os/harden/hardened_malloc_spec.spl` | AC-2 | `[hmalloc] guard-page trap OK`, `[hmalloc] double-free TRAPPED` |
| `os/harden/pie_ssp_relro_preset_spec.spl` | AC-8/9/10 | `[hardening] PIE=1`, `[hardening] RELRO=1 BIND_NOW=1`, `[hardening] NX=1 SMEP=1 SMAP=1`, `[hardening] STACK_CANARY=1` |

Each spec follows the standard fail-closed contract: a media-check `it` (expects `rt_file_exists`
true for kernel + image) followed by a boot `it` (calls `run_qemu_systest`, expects `== SYSTEST_PASS`).
Missing media returns `missing-media:<path>` — never `skip()`.

## Storage Policy

FAT32 images (~4 MB each) and kernel ELFs are kept for reproducibility and regression testing. QMP logs and .ppm screendumps are stale debris.

Run the audit script to see per-category disk usage:

```bash
scripts/check/qemu-storage-audit.shs        # Dry run
scripts/check/qemu-storage-audit.shs --clean # Delete QMP logs and .ppm >7 days old
```

Serial logs and test output remain in `build/os/systest/` for diagnosis.
