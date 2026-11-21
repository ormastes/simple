# Cross-Compile Linker Matrix (2026-11-17)

Status matrix for linking and running Hello-world style programs per OS and CPU,
for both the native linker (lld) and the Simple linker
(`src/compiler/70.backend/linker/`). Tables are updated as lanes land.

Legend: ✅ linked and ran · ⏳ not done · 🔧 in progress · ❌ unsupported yet · — not planned

## Native linker (lld), as of 2026-11-19

| OS | x86_64 | x86 32 (i686) | arm64 | arm32 (armv7) | riscv64 | riscv32 |
|----|--------|---------------|-------|---------------|---------|---------|
| Linux | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Windows | ✅ | 🔧 (triple fixed; needs LLVM backend + 32-bit RuntimeValue) | ✅ | — | — | — |
| FreeBSD | ✅ | — | ✅ | — | ✅ | — |
| SimpleOS | ⏳ | ⏳ | ⏳ | ⏳ | ⏳ | ⏳ |
| Bare-metal EFI | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |

## Simple linker, as of 2026-11-19

| OS | x86_64 | x86 32 (i686) | arm64 | arm32 (armv7) | riscv64 | riscv32 |
|----|--------|---------------|-------|---------------|---------|---------|
| Linux | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Windows (PE/COFF) | ✅ | 🔧 (C ok, Simple program needs redeploy) | ✅ (structural) | — | — | — |
| FreeBSD | ✅ | — | ✅ | — | ✅ | — |
| SimpleOS | ✅ | ⏳ (sysroot being built) | 🔧 (links, boot needs user-mode launch) | ⏳ (sysroot being built) | 🔧 (links, boot needs user-mode launch) | ⏳ (sysroot being built) |
| Bare-metal EFI | 🔧 (boot transcript pending) | ✅ | ✅ | ✅ | 🔧 (boot transcript pending) | 🔧 (boot transcript pending) |

FreeBSD cells: FreeBSD 14.4 VMs (arm64/amd64 cloud-init, riscv64 via
`check-freebsd-riscv64-bootstrap-qemu.shs --smoke`), dynamic, PIE and static hello
all rc=42 with both linkers. Windows arm64 is a structural compare against lld
(`check-windows-pe-internal-link.shs`); no arm64 Windows guest is available.

### PRs since #10219

- #10225, #10226 — COMDAT mark on weak replacement / dedup by group signature; ARM BLX->BL, THM_JUMP19 errors
- #10227, #10232 — SimpleOS riscv64 user link via internal ELF engine, script INPUT() and -L search
- #10230, #10237 — i686 bare-metal EFI boots on OVMF IA32 (Simple linker, lld)
- #10238, #10240 — ARM interworking veneers (.veneer section, keyed by symbol + offset)
- #10239 — arm32 Simple-linker EFI lane
- #10252 — i386 (i686-w64-windows-gnu) in the PE/COFF linker
- #10254, #10261 — static IFUNC (IPLT/IGOT/IRELATIVE) for all ELF targets
- #10256 — boot linker SHF_MERGE/SHF_STRINGS pooling like ld.lld
- #10258, #10265, #10266 — armv7 static glibc, dynamic/PIE, Thumb B.W veneer, ARM TLS GD/LDM/LDO
- #10263 — riscv32 raw ELF32 + Simple-linker riscv32 OpenSBI boot
- #10264 — i386 dynamic ET_EXEC/PIE
- #10268, #10269, #10270 — riscv64 glibc static/dynamic/PIE; rv32 musl static; bug docs
- #10273 — FreeBSD aarch64/riscv64 cross-link (symver @@, COMDAT dedup)
- #10274, #10275 — riscv64 undefined-weak PC-rel; script .got, lld PT_LOAD split
- #10279, #10286, #10290 — SimpleOS 32-bit userland (i686, riscv32 sysroot/crt0/syscall + links)
- #10281 — export executable definitions referenced by DSOs (FreeBSD `environ`)
- #10289 — FreeBSD riscv64 lane generates sshd host keys
- #10291, #10292 — PE/COFF: no forced mingw tlssup; i386 `__load_config_used`

Notes:
- Windows (Simple linker): in-house PE/COFF linker covers x64, arm64 and i386 (#10252); i686 C links run, the Simple program needs a compiler redeploy.
- Bare-metal EFI (Simple linker): shared PE32/PE32+ emitter (#10098); arm64 (#10102), i686 (#10230) and arm32 (#10239) boot; x86_64/riscv64/riscv32 link but the boot transcript is pending.
- arm32 EFI (lld): `lld-link -machine:arm` writes PE machine 0x01c4 while EDK2 ARM accepts only 0x01c2; the lane patches those 2 bytes and AAVMF32 boots the app.
- SimpleOS: x86_64 runs; arm64/riscv64 link (#10227) but boot needs a user-mode launch; i686/arm32/riscv32 sysroots are being built (#10279, #10286, #10290).

## Lanes

Open gaps only.

- Native Windows i686: seed now emits `i686-pc-windows-gnu` and `--target=i686-w64-windows-gnu` (was i686-unknown-linux-gnu / x86_64). Remaining: Cranelift has no i686 ("Support for this target has not been implemented yet") so it needs an `--features llvm` seed (LLVM 18 dev libs absent in the WSL lane), C `RuntimeValue` is u64 vs i32 in LLVM on 32-bit, and i386 `_` decoration in stubs.rs/cc_detect x86_64-only cross driver.
- Native SimpleOS (all CPUs).
- Simple Windows i686 (redeploy).
- Simple SimpleOS arm64/riscv64 boot; i686/arm32/riscv32 sysroots.
- Simple bare-metal EFI boot transcripts: x86_64, riscv64, riscv32.

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
