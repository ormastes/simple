# `native-build --emit-object` regression: "cannot convert object to int" (generic, content/target-independent)

**Date:** 2026-07-19
**Area:** compiler/native-build, `--emit-object` code path specifically
**Status:** OPEN — blocks NVMe rv32 SMP firmware build (and the default rv32
firmware build, and any other caller of `--emit-object`)

## Summary

While reworking `examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs`'s
`NVME_RV32_SMP=1` branch to flatten every SMP source into one module (fixing
the original `unresolved name: _rv32_io_command_valid` bug — module-PRIVATE
underscore names crossing files in multi-file `--entry-closure` mode; see
"Flatten fix — RESOLVED" below), the resulting single-module 472-function
file compiled cleanly through `phase2:parse`, `aot:lower_to_mir` (all 472
functions), `aot:borrow_check`, and `aot:process_async`, then failed inside
`aot:optimize_mir` with:

```
error: semantic: type mismatch: cannot convert object to int
```

with no file/line/function attribution.

**Root cause, isolated 2026-07-19 (bisected from a ~13.5min full-file compile
down to ~1min reproductions):** this is **not** a bug in the firmware source,
not pattern-specific, not target-specific, and not `--entry-closure`-specific.
It reproduces from the most trivial possible program:

```simple
fn f(x: i64) -> i64:
    x + 1

fn main() -> i64:
    f(41)
```

via `native-build --backend llvm --entry-closure --target <ANY> --emit-object
-o out.o`. Confirmed on:
- `riscv32-unknown-none` (the firmware target) — fails.
- `x86_64-unknown-linux-gnu` — fails, identically, deterministically (repeated).
- Both `src/compiler_rust/target/bootstrap/simple` (Rust seed, dated
  2026-07-19 04:33) and `bin/simple` (self-hosted, symlink to
  `release/x86_64-unknown-linux-gnu/simple`, dated 2026-07-18 22:58) — both fail.

**The discriminating flag is `--emit-object` itself**, not `--entry-closure`
or target:
- `native-build --backend llvm --entry-closure --target x86_64-unknown-linux-gnu
  -o out` (no `--emit-object`, normal full link) on the identical trivial
  program: **succeeds** (`Linked: .../out (16 KB) via clang`).
- `native-build --backend llvm --target x86_64-unknown-linux-gnu --emit-object
  -o out.o` (no `--entry-closure`) on the identical program: **fails**,
  identical error.
- `SIMPLE_NATIVE_BUILD_EMIT_OBJECT=1` env var (as `build.shs` sets it) makes
  no difference either way — the `--emit-object` CLI flag is sufficient to
  trigger it on its own.

So: **any `native-build ... --emit-object` invocation on the current binaries
is broken, regardless of target or source content.** This binary
(`target/bootstrap/simple`, 04:33 today) is newer than the one that built
`build/nvme_fw_rv32.bootstrap_full_probe.elf` in 5.2s on 2026-07-05 per
`doc/08_tracking/bug/nvme_rv32_firmware_build_timeout_2026-07-05.md` — this
looks like a regression introduced between those two builds, likely from
ongoing parallel-session compiler bootstrap activity in this shared repo
(`ps aux` showed concurrent `bootstrap-memory-sync` stage3/stage4
native-build cycles running during this investigation).

## Why this blocks the SMP firmware build specifically

`build.shs` (both the default AND the reworked SMP branch) MUST use
`--emit-object` for the rv32 firmware: the freestanding binary needs a custom
4-hart (SMP) or single-hart (default) `_start` asm stub and a custom linker
script (`src/os/kernel/arch/riscv32/linker.ld`), so it emits an object file
and links it manually with `ld.lld` rather than using native-build's normal
auto-link path (which the control test above shows still works, but doesn't
support the custom `_start`/linker-script requirement).

## Flatten fix — RESOLVED (do not re-derive)

The original diagnosis for this lane (multi-file `--entry-closure` compiling
`entry_smp.spl` + 189 copied `logic*.spl` files, failing with `unresolved
name: _rv32_io_command_valid` because `*_cases.spl` files reference
module-PRIVATE underscore names from `*_core.spl` — legal only within one
module) **is fixed**. `build.shs`'s `NVME_RV32_SMP=1` branch now flattens the
same way the default branch already does: the SAME base concat (all
`logic*.spl` except `logic.spl`/`logic_check.spl`, then `logic.spl` with
`use` lines stripped, then the direct-entry footer) plus entry.spl's filtered
`nvme_fw_rv32_selftest`+helpers (its `_uart_put`/`main`/
`rt_rv32_boot_optional_nvme_fw_selftest` dropped — real duplicates, see
below) plus entry_smp.spl (use-stripped, `i32`→`i64` transformed same as
every other appended file) — one module,
`build/os/generated_smp/nvme_fw_smp_direct_entry.spl`, 3954 lines, 472
functions, zero duplicate top-level `fn`/`val` names, `grep -c
_rv32_io_command_valid` = 17 (matches the default's count). A guard fn
(`smp_check_collisions`) in `build.shs` fails the build loudly on any future
top-level-name collision instead of silently shadowing.

Two real collisions were found + fixed during this work:
1. The wave-3 IPC/pool/nand/fourcore/coro core files
   (`logic_ipc_layout_core.spl` etc.) already match the `logic*.spl` glob in
   the base step — appending them a second time (as an earlier draft of this
   fix attempted, and as the original task instructions assumed) is a hard
   duplicate-definition collision. They must NOT be appended separately.
2. `entry.spl`'s `_uart_put`, `main`, and
   `rt_rv32_boot_optional_nvme_fw_selftest` duplicate definitions already
   present (`entry_smp.spl` defines its own `_uart_put`; the base footer
   already defines `main` and `rt_rv32_boot_optional_nvme_fw_selftest`) — an
   awk paragraph filter drops exactly those three from the appended
   `entry.spl` content, keeping `nvme_fw_rv32_selftest` + its `_emit_*`
   helpers (which entry_smp.spl's hart0 path needs and which are NOT part of
   the default's base flatten — the default omits `entry.spl` entirely and
   calls the raw `nvme_fw_rv32_logic_selftest()` instead, since its own
   `_start` asm prints the PASS banner itself).

## Impact

Both `build/nvme_fw_rv32.elf` (default) and `build/nvme_fw_rv32_smp.elf` (SMP)
are unbuildable while this regression stands, **independent of any firmware
source content** — this is not something further `.spl` firmware changes can
route around. `build/nvme_fw_rv32.elf` is currently absent on disk.

## Flatten validated end-to-end (2026-07-19, via the working full-link path)

A second real bug was found and fixed while validating the flatten through a
path that does NOT hit the `--emit-object` wall: `native-build --backend llvm
--entry-closure --target x86_64-unknown-linux-gnu -o <exe>` (no
`--emit-object`) on the *actual*
`build/os/generated_smp/nvme_fw_smp_direct_entry.spl` first failed at parse
with `Syntax error at 3434:39: reserved keyword 'val' cannot be used as a
parameter name` — `entry_smp.spl` declared `extern fn
rt_rv32_shm_store(idx: i64, val: i64)` and `fn shm_put(idx: i64, val: i64):`,
both using the reserved keyword `val` (see `.claude/rules/language.md`
reserved-keyword list) as a plain parameter name. Fixed in
`examples/09_embedded/simpleos_nvme_fw/fw_rv32/entry_smp.spl` by renaming the
parameter to `v` in both declarations and their one call site. Notably, the
`--emit-object` path's parser did **not** flag this (it got all the way to
`aot:optimize_mir` before the generic error above) — the two code paths
disagree on this rule, a smaller, secondary discrepancy worth a note in the
"Next check" below.

After the fix, the full-link compile of the real 472-function flattened file
**succeeded**: `Build complete: 1 compiled, 0 cached, 0 failed`, `Linked:
.../nvme_fw_smp_fulllink_validate2_exe (22 KB) via clang`, 15.4s total. The
only diagnostics were harmless `[WARN] Failed to load imported types from
[...]` lines for the pre-existing (default-flatten-inherited) `use
logic_x_cases.*` lines that point at files no longer present standalone —
non-fatal, same as the default flatten already tolerates.

**This closes the loop**: the flatten mechanism and its content are fully
correct and proven through parse/HIR/MIR/borrow-check/optimize/codegen/link.
The *only* remaining blocker to producing the real riscv32 object/ELF is the
generic `--emit-object` regression documented above, which is target- and
content-independent and not fixable by further `.spl` changes.

## Next check

Bisect the seed's `--emit-object` handling directly (smallest repro: the
2-function `f`/`main` program above, ~1 min per iteration) rather than
anything firmware-shaped — `doc/03_plan/agent_tasks/simple_os_rv64_native_build_timeout.md`
already documents the same `cannot convert object to int` message recurring
in `symbol_to_operand()` / bootstrap-flat symbol-table lookup for native AOT
paths; this may be the same code path re-regressing, or the `--emit-object`
branch specifically skipping a step the normal full-link path performs (e.g.
a symbol-table finalization pass that only runs before linking, not before
raw object emission).
