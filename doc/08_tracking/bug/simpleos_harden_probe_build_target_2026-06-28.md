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

## Re-investigated 2026-08-10 — still OPEN, characterized precisely

Confirmed both artifacts are still genuinely absent and no build machinery for
them exists anywhere in the tree:

```
$ find . -iname '*harden_probe*'   # only this bug doc
$ grep -rl 'simpleos_x86_64_harden_probe|fat32-x86_64-harden' \
    --include='*.sh' --include='*.shs' --include='*.spl' --include='Makefile*' .
  src/os/qemu_systest_contract.spl                        (paths/args/markers only)
  test/03_system/os/qemu/os/harden/cap_exec_gate_spec.spl
  test/03_system/os/qemu/os/harden/hardened_malloc_spec.spl
  test/03_system/os/qemu/os/harden/pie_ssp_relro_preset_spec.spl
```

No `build-harden-probe` (or equivalent) target exists in any build script.
`run_qemu_systest` therefore still returns `missing-media:<path>` and all
three specs classify RED, exactly as reported.

**A second, independent defect was found while re-investigating**: the
contract's own `harden_qemu_args()` (`src/os/qemu_systest_contract.spl:390`)
boots via `-kernel build/os/simpleos_x86_64_harden_probe.elf` plus
`-device isa-debug-exit,iobase=0xf4,iosize=0x04`. Per
`.claude/rules/board-runnable.md` this is explicitly the forbidden pattern —
QEMU `-kernel` pass semantics and `isa-debug-exit` are dev-harness-only
shortcuts that never run on the physical board or under real firmware (OVMF
pflash / EDK2 / OpenSBI). So even after the two build artifacts are produced,
this harness as currently specified would still not be board-runnable; the
QEMU args need to move to a real-firmware boot path (OVMF pflash for x86_64)
before a PASS here could be claimed as anything but QEMU-only.

**Why this stays OPEN rather than being fixed in this pass**: resolving it
for real requires net-new engineering, not a small patch —

1. A new SimpleOS kernel probe (capability-gate exec enforcement, a hardened
   malloc with guard-page and double-free detection, and PIE/RELRO/BIND_NOW/
   NX/SMEP/SMAP/SSP toggles that self-report via the exact serial markers in
   this doc) — this is a new kernel-level component, not a bug fix to
   existing code.
2. A FAT32-image packer invocation for the probe's SMF payloads.
3. A rework of `harden_qemu_args()` to boot through a real-firmware proxy
   (OVMF pflash) instead of `-kernel`/`isa-debug-exit`, to satisfy
   board-runnable.
4. A real physical-board bring-up path for the same probe artifact (per
   board-runnable.md's board-evidence bar), or an explicit, filed exception
   if hardware is genuinely unavailable.

None of this is a Rust-seed edit, but it is squarely OS kernel/build-system
feature work comparable in size to the other `simpleos_harden_*` campaign
items already tracked under `.spipe/simpleos_harden_*` — out of scope to
fabricate as a quick fix here. Leaving this OPEN honestly rather than
claiming partial progress; no code changes were made to this doc's target
artifacts in this pass.
