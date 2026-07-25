# Bug: Missing Harden Probe Build Target

**Date:** 2026-06-28
**Category:** build / OS hardening
**Status:** OPEN

## Summary

The SimpleOS Alpine-class hardening system specs (AC-1, AC-2, AC-8/9/10) are permanently RED
because the two build artifacts they depend on do not exist yet:

- `build/os/simpleos_x86_64_harden_probe.elf` — hardening probe kernel ELF
- `build/os/fat32-x86_64-harden.img` — FAT32 disk image containing probe payloads

`run_qemu_systest` returns `missing-media:<path>` for absent artifacts, so the specs classify
RED rather than crash or skip.

## Specs blocked

| Spec | AC |
|------|----|
| `test/03_system/os/qemu/os/harden/cap_exec_gate_spec.spl` | AC-1 |
| `test/03_system/os/qemu/os/harden/hardened_malloc_spec.spl` | AC-2 |
| `test/03_system/os/qemu/os/harden/pie_ssp_relro_preset_spec.spl` | AC-8/9/10 |

## Acceptance criteria (what the probe must emit on serial)

**AC-1 — capability gate exec:**
- `[exec] capability gate: ENFORCED`
- `[exec] uncapable exec REJECTED`

**AC-2 — hardened malloc:**
- `[hmalloc] guard-page trap OK`
- `[hmalloc] double-free TRAPPED`

**AC-8/9/10 — PIE/RELRO/NX/SSP preset:**
- `[hardening] PIE=1`
- `[hardening] RELRO=1 BIND_NOW=1`
- `[hardening] NX=1 SMEP=1 SMAP=1`
- `[hardening] STACK_CANARY=1`

## Resolution path

Add a `build-harden-probe` target to the OS build system that:
1. Compiles `simpleos_x86_64_harden_probe.elf` with PIE, SSP, RELRO, NX/SMEP/SMAP enabled
   and inlines the capability-gate and hmalloc probe routines.
2. Packs `fat32-x86_64-harden.img` with the probe SMF payloads used by AC-1/AC-2.
3. Emits the serial markers listed above on the successful probe path.

Once both artifacts exist the three specs will turn GREEN automatically.
