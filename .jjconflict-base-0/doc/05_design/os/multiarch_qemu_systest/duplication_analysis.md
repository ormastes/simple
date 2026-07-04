# SimpleOS Multiarch QEMU Systest — Duplication Analysis & Dedup Plan

**Date:** 2026-06-14
**Scope:** 6 arch lanes (arm32, arm64, riscv32, riscv64, x86_32, x86_64)
**Status:** Analysis only — no source edits (concurrent agents own arch/x86_64/** and shared os files)
**Constraint:** Must not break 3 confirmed-GREEN lanes (riscv64, arm64, x86_32); preserve arm32/riscv32 greens

---

## 1. File Inventory & Sizes

| Arch | baremetal_stubs.c | linker.ld | fs_exec_linker.ld | entry spl files |
|------|------------------:|----------:|------------------:|----------------|
| arm32 | 2,237 L | 83 L | 64 L | entry.spl, smoke_entry.spl, fs_exec_entry.spl |
| arm64 | 4,173 L | 85 L | 67 L | entry.spl, smoke_entry.spl, fs_exec_entry.spl, os_entry.spl |
| riscv32 | 628 L | 72 L | — | entry.spl, smoke_entry.spl |
| riscv64 | 1,806 L | 74 L | — | entry.spl, smoke_entry.spl |
| x86_32 | 1,429 L | ~70 L | — | entry.spl, smoke_entry.spl |
| x86_64 | 15,323 L | ~90 L | — | entry.spl, smoke_entry.spl |

Shared layers already in place:
- `src/os/kernel/loader/fs_exec_spawn.spl` (225 L) — shared spawn logic
- `arch/common/baremetal_16550_serial.h` (600 B) — 16550 UART header (x86 arches)
- `arch/common/baremetal_arm_interrupt_control.S` (98 B) — ARM interrupt stub
- `arch/shared/crypto_common.h` (60 KB) — crypto utilities

---

## 2. Duplication Findings (Quantified)

### Finding 1 — riscv32 is a stripped subset of riscv64 (88% line overlap)

**Files:** `arch/riscv32/boot/baremetal_stubs.c` (628 L) vs `arch/riscv64/boot/baremetal_stubs.c` (1,806 L)

**Measurement:** `sort riscv32.c | comm -12 - <(sort riscv64.c)` → **554 common lines** = 88% of riscv32 content.

**What is shared:** string ops (`rt_string_copy`, `rt_string_concat`, `rt_string_length`), heap/malloc (`rt_malloc`, `rt_free`, `rt_array_new`), enum helpers (`HEAP_ENUM` macro), serial putchar stub, `RuntimeValue` type alias, `rt_panic`.

**What riscv32 lacks vs riscv64:** tag-encoding macros (`ENCODE_INT`/`DECODE_INT`/`ENCODE_FLOAT`), `VIRTIO_DEV_NET`, `RuntimeArray` struct typedef, FAT32 driver (`fat32_probe_bpb`, `fat32_next_cluster`, `fat32_find_entry_cluster` — 14 functions), virtio-blk (`virtio_blk_init`, `virtio_blk_read_sector`), SMF/ELF loaders, GUI/framebuffer functions.

**Width fault line:** Both use `int64_t RuntimeValue` (riscv64 is 64-bit S-mode; riscv32 M-mode is still RV32 with 32-bit GPRs). `RuntimeValue` is `int32_t` on riscv32 and `int64_t` on riscv64 — this permeates all struct field types and extern signatures.

**Safe dedup potential:** ~400 L of width-independent helpers (`memcpy`/`memcmp`/`strlen`, pure string ops on `char*`/`size_t`, heap primitives that don't embed `RuntimeValue`) can go to `arch/common/riscv_common.h`. The remaining 154 L in riscv32 that are NOT in riscv64 are arch-specific (M-mode boot sequence, 32-bit GPR saves).

**Estimate:** Extract ~400 L → `arch/common/riscv_common.h`; riscv32 and riscv64 both `#include` it. Saves ~400 L duplication (riscv32 reduced by ~64%).

---

### Finding 2 — arm32 vs arm64 baremetal_stubs.c: 63% sorted line overlap, pervasive width split

**Files:** `arch/arm32/boot/baremetal_stubs.c` (2,237 L) vs `arch/arm64/boot/baremetal_stubs.c` (4,173 L)

**Measurement:** `sort arm32.c | comm -12 - <(sort arm64.c)` → **1,406 common lines** = 63% of arm32 content.

**What is shared structurally:**
- PL011 UART at MMIO base `0x09000000` — identical register offsets, putchar logic
- `rt_arm_virtio_blk_*` function family (20+ functions with `rt_arm_` prefix appear in both)
- FAT32 driver (`fat32_probe_bpb`, `fat32_next_cluster`, `fat32_find_entry_cluster`, etc.)
- Heap/malloc core
- `rt_arm_array_len_u32` helper (raw untagged pointer arrays in freestanding builds)
- String ops on `char*`

**What differs by width:**
- `RuntimeValue` = `int32_t` (arm32) vs `int64_t` (arm64) — permeates ALL `rt_*` function signatures
- `serial_put_hex`: loop `i = 28` (arm32) vs `i = 60` (arm64) — bit-width of hex dump
- `serial_put_dec`: buffer size 11 vs 21 digits
- arm64 adds WM/GUI/framebuffer stubs not in arm32
- arm64 has larger virtio driver with more capability negotiation

**Width-independent extractable subset:** ~300 L of `char*`-only string ops, `memcpy`/`memcmp`/`strlen`, pure FAT32 BPB parsing (uses `uint8_t`/`uint16_t`/`uint32_t` not RuntimeValue), PL011 register header macros.

**Estimate:** Extract ~300 L → `arch/common/arm_pl011_serial.h` + expand existing `arch/common/` headers. Saves ~300 L duplication across arm32/arm64.

**Risk:** FAT32/virtio functions that embed `RuntimeValue` in their return types cannot be trivially shared without a `typedef` switch guarded by `#ifdef __aarch64__`. This is medium risk — introduce the `typedef RuntimeValue` header carefully.

---

### Finding 3 — qemu_systest_contract.spl: 36 boilerplate functions for 6 arches

**File:** `src/os/qemu_systest_contract.spl` (300 L)

**Pattern:** 6 arches × 6 functions = 36 nearly-identical descriptor functions:
```
<arch>_kernel_path() -> text
<arch>_image_path() -> text
<arch>_qemu_bin() -> text
<arch>_qemu_args() -> [text]
<arch>_markers() -> [text]
<arch>_timeout_ms() -> i64
```

**Redundancy detail:**
- ALL 6 arches return `timeout_ms = 60000` — 6 identical single-line functions
- 4/6 arches (riscv32, arm32, x86_64, and partially others) share marker lists: `["ELF_LOAD_OK", "SMF_CLI_LAUNCH_OK", "SMF_WM_GUI_LAUNCH_OK", "NATIVE_GUI_PROCESS_RENDER_OK", "TEST PASSED"]`
- `qemu_args` differ only in machine type, CPU string, and disk image path — all parameterizable

**Why it's NOT already a struct-array table:** The file's own comment documents it: "those crash in interpreter mode." The `simpleos_platform_targets()` catalog-lane accessor crashes when called from interpreter mode (bug `interp_simpleos_lane_contract_crash`). Specs consume this file in interpreter mode.

**Interpreter-safety probe result (2026-06-14):** A minimal struct-array literal probe with named constructors **timed out in interpreter mode** (30s kill). Confirmed: struct-array table approach is NOT safe for interpreter-mode consumption until the array/struct-literal interpreter bug is fixed.

**Safe partial win:** Extract the shared `timeout_ms` into a single `fn default_qemu_timeout_ms() -> i64: 60000` and call it from each arch's `_timeout_ms()` function — 5 lines saved trivially with zero interpreter risk. The marker lists that are identical can similarly call a shared `fn standard_smf_markers() -> [text]` — but only if `[text]` literal return is interpreter-safe (needs probe, see risk).

**Estimate:** Shared timeout function: -5 L. Shared marker function (if safe): -~20 L. Full table: BLOCKED until interpreter struct-array bug is fixed.

---

### Finding 4 — Linker script pairs: arm32/arm64, riscv32/riscv64 are near-identical except for 5–7 parameters

**Files:** `arch/arm32/linker.ld` (83 L) vs `arch/arm64/linker.ld` (85 L)

**Differences (complete list):**
- `OUTPUT_FORMAT`: `elf32-littlearm` vs `elf64-littleaarch64`
- `ENTRY`: `_entry_asm` vs `_start`
- BSS symbols: `__bss_start`/`__bss_end` vs `_sbss`/`_ebss`
- Stack size: `64K` vs `8M`
- Heap size: `4M` vs `64M`
- ORIGIN base addresses may differ (arm64 has offset for OpenSBI padding)

**riscv32/riscv64 differences:**
- `OUTPUT_FORMAT`: `elf32-littleriscv` vs `elf64-littleriscv`
- ORIGIN: `0x80000000` (riscv32, M-mode direct) vs `0x80200000` (riscv64, S-mode after OpenSBI)
- RAM length: `256M` vs `510M`
- `ENTRY`: `_start` in both

**fs_exec linker scripts (arm32/arm64):** Same ORIGIN (`0x40200000`), arm64 adds `.text.vectors` alignment section, larger stack/heap.

**Dedup approach:** GNU ld supports `INCLUDE` directives. A `arch/common/linker_common.ld` template with `/* @PARAM: OUTPUT_FORMAT, ENTRY, STACK_SIZE, HEAP_SIZE, BSS_START, BSS_END */` comments, with each arch overriding via linker `-defsym` flags, is feasible. However, `.text.vectors` in arm64 is a genuine structural difference requiring a separate section block.

**Estimate:** ~50 L shared template → 4 thin per-arch overlays of ~20 L each. Saves ~200 L across the 4 LD pairs.

**Risk:** Low for RISC-V pair (identical structure). Medium for ARM pair (arm64 `.text.vectors` block). Do NOT touch x86 linker scripts (x86_64 is 15K lines total, x86_32 is structurally very different).

---

### Finding 5 — `_SimpleosMultiplatformBuild/platform_target_catalog.spl` already data-driven; extend it

**File:** `src/os/port/_SimpleosMultiplatformBuild/platform_target_catalog.spl` (707 L)

**Current state:** `simpleos_platform_targets() -> [SimpleOsPlatformBuildTarget]` is already a struct-array — one record per platform with all build parameters. This is the RIGHT pattern.

**Duplication:** The `qemu_systest_contract.spl` descriptors overlap heavily with fields already in `SimpleOsPlatformBuildTarget` (`qemu_system`, `kernel_output`, `disk_image_output`, etc.). The test contract file re-states what the build catalog already knows.

**Opportunity:** When the interpreter struct-array bug is fixed, `qemu_systest_contract.spl` can delegate to `simpleos_platform_targets()` — eliminating the entire 300 L file and replacing it with a 30 L lookup adapter.

**Current blocker:** `simpleos_platform_targets()` is called from build tooling paths (native mode, not interpreter). Calling it from spec files (interpreter mode) crashes. This is the same `interp_simpleos_lane_contract_crash` bug.

---

## 3. Ranked Dedup Plan (Safe-First)

### Tier 1 — Pure .spl refactors (zero C-build risk, testable before merge)

| Rank | Action | Files | Estimated Savings | Risk |
|------|--------|-------|-------------------|------|
| 1a | **DONE 2026-06-14** — added `default_qemu_timeout_ms() -> i64: 60000`; the 6 QEMU `_timeout_ms()` now delegate to it (darwin keeps its own 15000). `simple check` OK. | `qemu_systest_contract.spl` | ~5 L | Very Low |
| 1b | **DONE 2026-06-14** — interpreter `[text]`-helper-delegation probe passed (count=5, exit 0); added `standard_smf_markers() -> [text]`; the 3 lanes with the exact 5-marker set (riscv32, arm32, x86_64) delegate. riscv64 (extra `SIMPLEOS_RISCV_SMF_FS_PASS`), arm64 (EL0 svc set), x86_32 (initrd set), darwin (hosted set) keep their own. Byte-identical literals (git diff verified) + `simple check` OK. | `qemu_systest_contract.spl` | ~12 L | Low (needs probe) |

### Tier 2 — C header extraction (no freestanding build logic change, additive only)

| Rank | Action | Files | Estimated Savings | Risk |
|------|--------|-------|-------------------|------|
| 2a | Extract width-independent riscv string/heap helpers to `arch/common/riscv_common.h`; both riscv stubs `#include` it | riscv32 + riscv64 baremetal_stubs.c | ~400 L | Low — additive include |
| 2b | Extract PL011 register macros + putchar to `arch/common/arm_pl011_serial.h`; arm32 + arm64 include it | arm32 + arm64 baremetal_stubs.c | ~80 L | Low — macros only |
| 2c | Extract width-independent FAT32 BPB parsing to `arch/common/fat32_common.h`; include from riscv32/64 and arm32/64 | 4 stubs files | ~120 L | Medium — must audit all uses of RuntimeValue in FAT32 code paths |

### Tier 3 — Linker script consolidation (structural change, needs build verification per arch)

| Rank | Action | Files | Estimated Savings | Risk |
|------|--------|-------|-------------------|------|
| 3a | Create `arch/common/linker_riscv_common.ld` with INCLUDE for shared sections; riscv32/riscv64 thin overlays | riscv32 + riscv64 linker.ld | ~100 L | Low — identical structure |
| 3b | Create `arch/common/linker_arm_common.ld` for arm32/arm64 shared sections; arm64 adds `.text.vectors` block | arm32 + arm64 linker.ld | ~100 L | Medium — test arm64 `.text.vectors` alignment carefully |

### Tier 4 — Full contract table — CLOSED 2026-06-14 (NOT WORTH DOING; savings illusory)

Investigated and dropped. Two findings settle it:

1. **The interpreter blocker (4a) is NOT actually needed and should NOT be fixed.**
   Probe (2026-06-14): in interpreter mode `simpleos_platform_targets()[i].field`
   and `for t in simpleos_platform_targets()` both work cleanly (7 lanes, all
   fields, exit 0). The earlier "struct-array hang" was *inline literal
   construction* / `get_all_scenarios()` Option-poison — neither is what 4b needs.
   So no "document-don't-patch" seed change is justified for this.
2. **But the dedup itself is illusory.** The contract emits per-lane-UNIQUE qemu
   arg lists that are NOT stored in (nor reconstructable from) the build-target
   struct: riscv64 = virtio-blk + `-kernel`; arm32 = dual `-device loader,…,addr=0x40200000`
   + `-semihosting-config` (no `-kernel`); x86_64 = `isa-debug-exit,iobase=0xf4` +
   nvme + nvme-ns. The struct only carries machine/cpu/serial_kind/image_layout,
   and `qemu_smoke_lane.required_serial_markers` is `[]` for every lane (markers
   live only in the contract). Delegating would either store the arg lists verbatim
   in the table (move 270 L, remove nothing) or re-create per-lane assembly with
   NVMe/virtio/loader special-casing (relocate the logic) — no real savings, while
   churning `qemu_systest_contract.spl`, the highest-fanout file every systest spec
   consumes. **Decision: leave the contract as explicit per-lane functions.**

| Rank | Action | Files | Estimated Savings | Status |
|------|--------|-------|-------------------|--------|
| 4a | Fix interpreter struct-array/named-constructor timeout bug | interpreter core | — | NOT NEEDED (interpreter reads the table fine) |
| 4b | Replace `qemu_systest_contract.spl` with table-driven delegate | `qemu_systest_contract.spl` | ~0 L (was est. ~270 L) | CLOSED — savings illusory (per-lane-unique args not in struct) |

### Do NOT touch (out of scope / high risk)

- `arch/x86_64/boot/baremetal_stubs.c` (15,323 L) — under active parallel agent editing; no overlap analysis done
- `arch/x86_32/boot/baremetal_stubs.c` — structurally divergent from x86_64 (different boot ABI)
- x86 linker scripts — completely different layout from ARM/RISC-V
- `arch/arm32/` or `arch/arm64/` entry .spl files — parallel agent (ac6a1fba) owns arm64 lane

---

## 4. Implementation Order Recommendation

1. **Immediate (no build risk):** Tier 1a — add `default_qemu_timeout_ms()` to `qemu_systest_contract.spl`. Single function, zero dependencies.
2. **Next sprint:** Tier 2a — `arch/common/riscv_common.h`. riscv32 is the smallest stub (628 L), easiest to validate. Build riscv32 + riscv64 after extraction, run QEMU systest.
3. **Same sprint:** Tier 2b — `arch/common/arm_pl011_serial.h`. Macros only, additive.
4. **After riscv proven:** Tier 3a — riscv linker consolidation. Gate on riscv32+riscv64 GREEN.
5. **After arm32 probe passes:** Tier 2c (FAT32 common) + Tier 3b (arm linker). Gate on arm32+arm64 GREEN.
6. **Future:** Tier 4 — full contract table, after interpreter struct-array bug is fixed and verified.

---

## 5. Total Potential Line Savings

| Tier | Safe Lines Saved | Status |
|------|-----------------|--------|
| Tier 1 (spl timeout/markers) | ~17 L | **DONE 2026-06-14** (1a timeout + 1b markers landed) |
| Tier 2 (C headers) | ~600 L | Ready after arm32/riscv arch analysis |
| Tier 3 (linker scripts) | ~200 L | Ready after Tier 2 proven |
| Tier 4 (contract table) | ~270 L | Blocked — interpreter bug |
| **Total addressable** | **~1,095 L** | Across 6 archs |

Excluded from savings: x86_64/x86_32 stubs (out of scope), arm64 GUI/framebuffer extensions (arm64-only, no duplication partner).

---

## 6. Key Risks and Guards

| Risk | Mitigation |
|------|-----------|
| `RuntimeValue` width split poisons extracted headers | Audit every extracted function for `RuntimeValue` use; only extract `char*`/`uint*` functions in Tier 2 |
| Interpreter struct-array crash (confirmed 2026-06-14 probe) | Do NOT move to table-driven contract until interpreter fixed + verified |
| Parallel agent clobber (ac6a1fba owns arm64 lane) | Coordinate before touching any `arch/arm64/**` file |
| x86_64 agent (a6366d062c) active | Do NOT touch `arch/x86_64/**` |
| Linker script `INCLUDE` not supported in all toolchain versions | Verify with `ld --version` in each cross-toolchain; fallback = sed-generated overlays |
| GREEN lane regression | Gate each tier behind per-arch QEMU systest run; fail = revert immediately |

---

*Generated by analysis agent 2026-06-14. All line counts from direct wc/comm measurement on working-tree files.*
