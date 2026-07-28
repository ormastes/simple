# `rt_arm_virtio_` prefix allowlist defeats the fabricated-rt guard on a storage path

**Status:** open
**Scope:** `src/compiler/70.backend/backend/llvm_native_link.spl` (pure-Simple
SimpleOS freestanding link guard); affects any arch whose guest kernel links the
VirtIO-BLK driver without a real `baremetal_stubs.c` implementation
**Observed:** 2026-07-28
**Supersedes/corrects:** `doc/08_tracking/todo/blocked_p1_audit_2026-07-28.md` §3 C2

## Summary

The fabricated-`rt_*` link guard exists and works, but
`simpleos_rt_symbol_is_optional_backend`
(`src/compiler/70.backend/backend/llvm_native_link.spl:1752`) allowlists
`rt_arm_virtio_` **as a prefix**. That places an entire block-storage read path
into the "nil is the intended answer / backend unavailable" bucket, which is not
true of it. The guard's own docstring argues, correctly and at length, against
exactly this move for `rt_simd_`:

> NOT a prefix here on purpose: `rt_simd_`. That family is dominated by
> ARITHMETIC kernels ... where nil is silent numeric corruption, not
> "unavailable" -- a `rt_simd_` prefix would have swallowed exactly the bug
> class this guard exists to catch.

`rt_arm_virtio_blk_read_sector_direct` / `_sector_bytes` are storage reads, not
capability probes. They meet the docstring's own criterion for exclusion and
should be allowlisted by exact name (or not at all), not by prefix.

## Why the nil answer is not safe here

`virtio_blk_arm_read_sector_bytes`
(`src/os/drivers/virtio/_VirtioBlk/driver_class.spl:389-396`) treats the status
word as: `0xFFFFFFFF` → fail, non-zero → fail, **zero → success**. A weak
zero-returning stub therefore reports *success*, after which
`rt_arm_virtio_blk_sector_bytes()` — also stubbed — yields an empty buffer. The
caller sees "read succeeded, here are your sectors", not "backend unavailable".

`_arm_read_sector` (`src/os/services/vfs/arm_fs_exec_vfs.spl:190-197`) partially
catches this via a length check and logs `direct_sector_failed`, but still
returns the short buffer to `_arm_fat32_probe_bpb` / `_arm_fat_next` /
`_arm_read_cluster`. FAT32 metadata parsed from a zero buffer is silent
mis-parse, not a clean failure.

**Severity note (do not overstate):** the declared surface is **read-only**.
`rt_arm_virtio_blk_mmio_write_u32` writes device *registers*, not sectors; there
is no sector-write extern. The realistic failure is silently wrong reads and
FAT32 mis-parse, not write-drop or on-media data loss.

## Declared vs defined (verified 2026-07-28)

Method: anchored greps over the whole tree, `.spl`/`.c`/`.h`/`.rs`/`.ll`, plus
`nm`/`objdump` on a built artifact. `auto_stubs.c` is generated and its bodies
are counted as MISSING, per the guard's own definition.

| Site | Count | Kind |
|---|---|---|
| `src/os/drivers/virtio/_VirtioBlk/driver_class.spl:118-132` | **12** | `extern fn` declarations |
| same file, call sites | 8 | references (not declarations) |
| `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs` | 13 | seed `RuntimeFuncSpec` registrations |
| `arch/arm64/boot/baremetal_stubs.c` | **14** | **real strong definitions** |
| `arch/arm32/boot/baremetal_stubs.c` | **14** | **real strong definitions** |
| `arch/x86_64/boot/baremetal_stubs.c` | 14 | `__attribute__((weak))` constant-return stubs |
| `arch/riscv32`, `riscv64`, `x86_32` `baremetal_stubs.c` | 0 | absent |

So the population is **12 declared externs, 14 defined on arm32/arm64**, not
"20 declared, zero defined".

## Corrections to audit §3 C2

C2 states 20 declared externs with "zero definitions anywhere ... resolves to
nothing **on any arch**". Both halves are wrong:

1. **Method error.** C2's evidence was
   `grep -rl 'rt_arm_virtio_blk' src/ --include=*.c --include=*.h` → empty. The
   implementations do not live under `src/`; they are at
   `examples/09_embedded/simple_os/arch/{arm64,arm32}/boot/baremetal_stubs.c`.
   The search scope excluded the answer. "20" is a count of *references* in
   `driver_class.spl`, not of declarations.
2. **Reachability is arm64-only, not "every architecture".**
   `vfs_boot_init_virtio_fat32` has exactly one production caller:
   `examples/09_embedded/simple_os/arch/arm64/gui_entry_desktop.spl:153`. Tests
   actively assert the RV64 and x86_64 guests do *not* call it
   (`test/02_integration/os/port/simpleos_font_asset_staging_spec.spl:123`,
   `test/01_unit/os/gui_entry_desktop_production_render_contract_spec.spl:198`).
   The one arch that reaches this code is the one that implements it for real.

The residual risk is therefore **not** an unimplemented driver. It is the
prefix allowlist above, which would let a *future* arch (or a refactor moving
the arm64 entry) link a fabricated storage path with the guard staying green.

## WEAK-stub evidence (actual, not theoretical)

Artifact: `build/simpleos_wm_fullscreen_evidence/simpleos_wm_production_desktop.elf`
(ELF 32-bit i386, prebuilt; produced by an earlier run, not by this
investigation). Tooling: system `nm`/`objdump`. `bin/simple` was **not** used —
`readlink -f bin/simple` resolves to the Rust seed and no pure-Simple binary is
deployed.

```
$ nm <elf> | grep rt_arm_virtio_blk
080161c0 W rt_arm_virtio_blk_configure_queue
080161e0 W rt_arm_virtio_blk_mmio_read_u32
08016200 W rt_arm_virtio_blk_mmio_read_u64
08016220 W rt_arm_virtio_blk_mmio_write_u32
08016240 W rt_arm_virtio_blk_queue_base
08016250 W rt_arm_virtio_blk_set_mmio_base

$ nm <elf> | awk '$2=="W" && $3~/^rt_/' | wc -l   → 60
$ nm <elf> | awk '$1=="U" && $2~/^rt_/'  | wc -l   → 0
```

The hazard is real and present in a built artifact. Mitigating context: all six
are already in `fabrication_allowlist()` /`allow_arm_virtio()` in
`test/03_system/check/simpleos_kernel_fabricated_rt_symbol_guard_spec.spl:250-261`,
whose comment already anticipates this precisely — *"these become
correctness-class the moment an aarch64 guest is built -- retire them from this
list then."* The read/data externs (`read_sector_direct`, `sector_bytes`,
`prepare_read`, `status_u8`, `wait_completion`, `dma_base`) are **not** linked
into this x86 guest at all, which is why only six appear.

## Proposed fix (not applied here)

In `simpleos_rt_symbol_is_optional_backend`, drop `rt_arm_virtio_` from the
prefix list and re-admit only the genuine capability/register probes by exact
name, applying the rule the docstring already states. Anything on the sector
path (`read_sector_direct`, `read_prefix`, `sector_bytes`, `read_hello_smf`)
must not be optional. Expect this to require the arm64 guest to keep supplying
real bodies — which it already does — and to make a riscv64/x86 guest that links
the driver fail closed, which is the intent.

## Non-goals

Do **not** implement a VirtIO-BLK driver for the arches that lack one. arm64 and
arm32 already have real implementations; no other arch currently reaches this
code. This item is about the guard's allowlist granularity only.
