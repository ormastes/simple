# Cross-Compile Linker Matrix (2026-11-17)

Status matrix for linking and running Hello-world style programs per OS and CPU,
for both the native linker (lld) and the Simple linker
(`src/compiler/70.backend/linker/`). Tables are updated as lanes land.

Legend: ✅ linked and ran · ⏳ not done · 🔧 in progress · ❌ unsupported yet · — not planned

## Native linker (lld), as of 2026-11-17

| OS | x86_64 | x86 32 (i686) | arm64 | arm32 (armv7) | riscv64 | riscv32 |
|----|--------|---------------|-------|---------------|---------|---------|
| Linux | ✅ | ⏳ | ⏳ | ⏳ | ⏳ | — |
| Windows | ✅ (x64) | — | ✅ (#9999, #10051) | — | — | — |
| FreeBSD | ⏳ | — | ⏳ | — | — | — |
| SimpleOS | ⏳ | ⏳ | ⏳ | ⏳ | ⏳ | ⏳ |
| Bare-metal EFI | ✅ (#9879) | ⏳ | ✅ (#9879) | 🔧 (PE machine 0x01c4 vs 0x01c2) | ✅ (#9879) | ✅ (#10024) |

## Simple linker, as of 2026-11-17

| OS | x86_64 | x86 32 (i686) | arm64 | arm32 (armv7) | riscv64 | riscv32 |
|----|--------|---------------|-------|---------------|---------|---------|
| Linux | ✅ (3.4 s, #10037; was 4.5 s / 820 MB; target < 2 s / < 500 MB) | ❌ | ⏳ | ❌ (raw only) | ❌ | — |
| Windows (PE/COFF) | 🔧 (shared PE EFI emitter #10098) | — | 🔧 (#10098) | — | — | — |
| FreeBSD | 🔧 (cross-link via --sysroot, #10193; run pending) | — | ⏳ | — | — | — |
| SimpleOS | ⏳ | ❌ | ⏳ | ❌ | ❌ | ❌ |
| Bare-metal EFI (new row) | 🔧 (--linker simple check, #10165; boot run pending) | 🔧 | ✅ (#10102) | 🔧 | 🔧 | 🔧 |

Notes:
- Windows (Simple linker) is a new PE/COFF lane covering x64 and arm64.
- Bare-metal (Simple linker): lanes started; arm64 boots on AAVMF (#10102). The shared PE32/PE32+ EFI emitter landed in #10098.
- arm32 EFI root cause: `lld-link -machine:arm` writes PE machine 0x01c4, but
  EDK2 ARM accepts only 0x01c2. With those 2 bytes patched, AAVMF32 booted a
  test app from a vfat image on virtio-blk-pci.

## Lanes

One lane per gap.

- Native bare-metal: i686, arm32 (riscv32 landed, #10024).
- Simple bare-metal: x86_64, i686, arm32, riscv64, riscv32 (arm64 landed, #10102).
- Native FreeBSD x86_64.
- Native SimpleOS x86_64.
- Simple FreeBSD.
- Simple SimpleOS.
- Simple Windows PE.
- Linux hosted lane (both linkers).

## Lint and test-runner matrix

Phase 2: all pending the p2 rebuild.

| Tool | Phase 2 |
|------|---------|
| Lint | ⏳ pending p2 rebuild |
| Test runner | ⏳ pending p2 rebuild |

## Maintenance

The tables are updated as lanes land. Real-firmware boot only (OVMF / AAVMF /
AAVMF32 / OpenSBI); see `.claude/rules/board-runnable.md`.

## Phase 2 status

The next p2 blocker is the `stage2_module_path_naming` identity check.
The HIR snapshot origin skip fix (#10108) has landed.

## Small-job slot

Small-job slot (2026-11-18): while the heavy p2 bootstrap runs, small lane jobs go through xc-wsl-scripts/small_slot.sh — one lane at a time, RAM ≥8 GB, C: ≥25 GB, ulimit 8 GB, nice 10, timeout 1800, QEMU 256M (FreeBSD VM 2 GB).
