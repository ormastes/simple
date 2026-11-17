# Cross-Compile Linker Matrix (2026-11-17)

Status matrix for linking and running Hello-world style programs per OS and CPU,
for both the native linker (lld) and the Simple linker
(`src/compiler/70.backend/linker/`). Tables are updated as lanes land.

Legend: ✅ linked and ran · ⏳ not done · 🔧 in progress · ❌ unsupported yet · — not planned

## Native linker (lld), as of 2026-11-17

| OS | x86_64 | x86 32 (i686) | arm64 | arm32 (armv7) | riscv64 | riscv32 |
|----|--------|---------------|-------|---------------|---------|---------|
| Linux | ✅ | ⏳ | ⏳ | ⏳ | ⏳ | — |
| Windows | ✅ (x64) | — | 🔧 (PR #9999) | — | — | — |
| FreeBSD | ⏳ | — | ⏳ | — | — | — |
| SimpleOS | ⏳ | ⏳ | ⏳ | ⏳ | ⏳ | ⏳ |
| Bare-metal EFI | ✅ (#9879) | ⏳ | ✅ (#9879) | 🔧 (PE machine 0x01c4 vs 0x01c2) | ✅ (#9879) | ⏳ |

## Simple linker, as of 2026-11-17

| OS | x86_64 | x86 32 (i686) | arm64 | arm32 (armv7) | riscv64 | riscv32 |
|----|--------|---------------|-------|---------------|---------|---------|
| Linux | ✅ (4.5 s / 820 MB; target < 2 s / < 500 MB) | ❌ | ⏳ | ❌ (raw only) | ❌ | — |
| Windows (PE/COFF) | 🔧 | — | 🔧 | — | — | — |
| FreeBSD | ⏳ | — | ⏳ | — | — | — |
| SimpleOS | ⏳ | ❌ | ⏳ | ❌ | ❌ | ❌ |
| Bare-metal EFI (new row) | 🔧 | 🔧 | 🔧 | 🔧 | 🔧 | 🔧 |

Notes:
- Windows (Simple linker) is a new PE/COFF lane covering x64 and arm64.
- Bare-metal (Simple linker) lanes have all started.
- arm32 EFI root cause: `lld-link -machine:arm` writes PE machine 0x01c4, but
  EDK2 ARM accepts only 0x01c2. With those 2 bytes patched, AAVMF32 booted a
  test app from a vfat image on virtio-blk-pci.

## Lanes

One lane per gap.

- Native bare-metal: i686, arm32, riscv32.
- Simple bare-metal: x86_64, i686, arm64, arm32, riscv64, riscv32.
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
