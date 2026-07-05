# NVMe rv32 firmware build: native-build timeout before ELF

**Date:** 2026-07-05
**Area:** compiler/native-build, SimpleOS rv32, NVMe firmware evidence
**Status:** OPEN

## Symptom

The firmware-specific rv32 wrapper times out before producing
`build/nvme_fw_rv32.elf`:

```bash
NVME_RV32_BUILD_TIMEOUT_SECS=60 sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs
```

Observed result:

```text
NVME_RV32_BUILD_FAILED code=124 timeout=60s out=build/test-artifacts/nvme_fw_rv32_build.out err=build/test-artifacts/nvme_fw_rv32_build.err
```

The native-build subprocess emits no compiler diagnostics before the timeout.
The wrapper now writes preflight source/entry/target markers before invoking
native-build so future timeout logs are not empty.

Follow-up differential evidence:

- `bin/simple` with the canonical full source set still timed out within 60s
  with empty native-build output.
- `src/compiler_rust/target/bootstrap/simple` with the same full source set
  built `build/nvme_fw_rv32.bootstrap_full_probe.elf` in about 5.2s.

The wrapper keeps `bin/simple` as the default and exposes
`NVME_RV32_SIMPLE_BIN` for explicit diagnostic runs.

## Impact

`test/03_system/app/nvme_firmware/nvme_rv32_baremetal_boot_spec.spl` fails
closed when `build/nvme_fw_rv32.elf` is absent, so NVMe firmware runtime PASS
evidence remains blocked.

## Distinction

This is not the resolved silent-255 rv32 native-build bug tracked in
`doc/08_tracking/bug/native_build_rv32_baremetal_silent_255_2026-06-30.md`.
That bug covered cross-target routing and freestanding runtime symbols. This
bug is the current firmware wrapper timing out before producing the firmware
ELF.

## Next Check

Run the wrapper with the shortest timeout that reproduces the timeout, inspect
`build/test-artifacts/nvme_fw_rv32_build.{out,err}`, then narrow native-build to
the slow compile/load phase before claiming firmware runtime evidence.

## Root Cause — localized (2026-07-05)

The timeout is **NOT** a compiler-pass infinite loop, and **NOT** an
over-broad `--source src` parse or a bloated entry closure. Differential
phase-localization on the self-hosted `bin/simple`:

- `--entry-closure` works correctly: the driver reports
  `[native-build] Entry closure files: 31` (verified with `--verbose` +
  `SIMPLE_NATIVE_BUILD_TRACE_CLOSURE=1`) and computes it in well under a second.
  `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1` correctly suppresses the driver's
  implicit whole-`src` bulk-load (`src/compiler/80.driver/driver.spl:301`).
- After the 31-file closure is computed, the run still times out. The stderr is
  dominated by warnings from **compiler-internal** files that boot.spl never
  imports — 52+ distinct files under `src/compiler/10.frontend/*`,
  `src/compiler/15.blocks/*`, `src/compiler/90.tools/lint/*`, plus gc-warnings
  for `std.nogc_sync_mut.sffi.llvm_loader / cuda_sffi / vulkan_sffi`.

Why those appear: `simple native-build` dispatches **interpreted**
(`src/app/cli/dispatch.spl` → `try_simple_app` → `cli_run_file`). The interpreter
uses lazy module loading, so the heavy load is deferred until
`cli_native_build` actually **calls** `compiler_driver_run_compile`
(`src/app/io/_CliCompile/compile_targets.spl:353`). At that point the
self-hosted interpreter must parse & load the entire self-hosted **compiler
backend from source** (frontend → typecheck → MIR → LLVM codegen → lint,
hundreds of thousands of lines) *before compiling a single line of firmware*.
Confirmation: a trivial script that only `use`-imports `cli_native_build` but
never calls it loads in 0.06 s / 26 MB RSS; the timeout only appears once the
driver is actually invoked.

The Rust seed (`src/compiler_rust/target/bootstrap/simple`) builds the same
source set in ~5.2 s because its compiler is **compiled into the binary** — it
never re-parses the compiler from source. The self-hosted binary re-interprets
the whole compiler graph on every `native-build` invocation, and its throughput
on that cold-load is >30x slower, exceeding any practical wrapper timeout.

**Localized phase:** interpreter cold-load (parse + module resolution) of the
self-hosted compiler backend that runs the AOT driver — *upstream* of the
firmware front-end. Not parse/resolve/typecheck/MIR/codegen **of the firmware
sources**.

### Concrete next step (pure-Simple fix, multi-session)

Stop re-interpreting the compiler to run `native-build`. `bin/simple` already
contains the compiler compiled to native code; the fix is to route
`native-build` (and its worker) to a **compiled** dispatch path instead of
`cli_run_file`-interpreting `native_build_main.spl` → `run
native_build_worker.spl`. Options, smallest first:
1. Add a compiled-in `native-build` subcommand entry that calls
   `cli_native_build` directly from the already-compiled binary image, bypassing
   `try_simple_app`/`cli_run_file` for this command (dispatch change in
   `src/app/cli/dispatch.spl` + `dispatch/table.spl`).
2. Cache a compiled artifact of the worker's compiler graph (SMF) and have
   `native_build_main` exec the cached compiled worker rather than `run
   worker.spl`.
This is an architecture change to the dispatch/execution model and needs its own
session + bootstrap re-verification; it must not regress the interpreted-default
dispatch contract for other subcommands.

### Diagnostic ELF + firmware-marker gap

Built the ELF via the seed for diagnostics only (NOT a permanent switch):
`NVME_RV32_SIMPLE_BIN=src/compiler_rust/target/bootstrap/simple
NVME_RV32_BUILD_TIMEOUT_SECS=180 sh
examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs` →
`build/nvme_fw_rv32.elf` (ELF 32-bit RISC-V, ~303 KB, ~5 s).

### Update — hook rooted, runtime stop narrowed (2026-07-05)

The wrapper now generates a build-only entry root at
`build/os/generated/os/kernel/arch/riscv32/nvme_fw_boot_root.spl` and a sibling
`boot` symlink to the rv32 boot C stubs. With the diagnostic seed compiler:

```bash
NVME_RV32_SIMPLE_BIN=src/compiler_rust/target/bootstrap/simple \
NVME_RV32_BUILD_TIMEOUT_SECS=60 \
sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs
```

the ELF builds, and `llvm-nm build/nvme_fw_rv32.elf` shows a strong
`rt_rv32_boot_optional_nvme_fw_selftest` plus `entry__nvme_fw_rv32_selftest`.
So the earlier hook-rooting gap is closed for diagnostic builds.

The QEMU runtime PASS marker is still not green. Serial output reaches:

```text
RV32 NVME FW BEGIN
R
E
J
M
B
S
P
H
Q
I
F
A
```

and then stops before reactor marker `C`. Current remaining runtime blocker:
`rv32_reactor_selftest()` does not complete on rv32 baremetal. Host logic still
passes via `bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl`.

`nvme_rv32_baremetal_boot_spec.spl` still **fails** on this seed ELF: QEMU boots
and prints `SimpleOS RV32`, the `[BOOT]` markers, and `LOG OK`, but **not** the
firmware markers the spec requires (`ALL RV32 NVME FW CHECKS PASS`, `HEAP OK`,
`SVC OK`). So the firmware self-test hook is not being invoked/linked into the
booted image — a **separate** firmware-wiring gap in the rv32 boot path,
independent of this build-timeout bug and of the compiler used to build.

### CORRECTION — not a wiring gap; two on-target faults, one fixed (2026-07-05, later)

The "hook not invoked/linked" diagnosis above is **wrong**. The selftest hook
**is** wired and **does** run: `boot.spl:boot_main` calls
`rt_rv32_boot_optional_nvme_fw_selftest()` (the strong `@export` hook in
`fw_rv32/entry.spl`), and on boot the serial prints `RV32 NVME FW BEGIN` and
executes the per-stage selftests. The earlier "stops before `C`" was **output
buffering / kill-timing**, not the true stop point. A GDB stub attach
(`-gdb tcp::…`, `bt`) gave the real backtrace:

```text
PC = 0x00000000                         (trapped to mtvec=0 -> exec zeros -> hang)
#1 rt_as_string+30
#3 rt_native_eq
#4 rt_native_neq
#5 logic.rv32_policy_target_selftest
#6 entry.nvme_fw_rv32_selftest
#7 boot_main
```

**Fault 1 (FIXED): baremetal silent hang in the value runtime.** The seed
lowers the selftest's scalar `i64` `==`/`!=` through `rt_native_eq` /
`rt_native_neq`, which call `rt_as_string(operand)` -> `rt_as_heap`
(`src/os/kernel/arch/riscv64/boot/freestanding_runtime.c`). `rt_as_heap`
treated any 8-aligned value `>= 0x10000` (or a HEAP-tagged value) as a raw heap
pointer and dereferenced `header->object_type`. For a misclassified integer
operand this load hits **unmapped** memory; with no trap vector installed
during early boot the CPU traps to `mtvec=0`, executes zeros, and hangs
silently (no exception is logged — the earlier `-d int` run simply had not
reached the fault yet). This is the same silent-hang class the existing
`< 0x10000` floor guard already documented.

Fix applied: bound the candidate `header` to the mapped RAM window before the
load. All real heap objects (runtime-allocated in `[0x87000000,0x88000000)` per
`g_freestanding_heap_*`, or `rt_extern_heap`-wrapped C statics in the loaded
image) live in `[0x80000000,0x88000000)`; anything outside is a misclassified
integer and is rejected (returns 0 -> `lhs==rhs` path, which the disassembly
confirms is a correct 64-bit compare). New `#define RT_RAM_WINDOW_BASE/END` +
extended guard in `rt_as_heap`. **Result:** the selftest now runs to completion
and boot proceeds — the serial prints all 21 stage letters, then `MEM OK`,
`PMM OK`, **`HEAP OK`**, **`SVC OK`**, `BOOT OK`. Two of the three required
markers (`HEAP OK`, `SVC OK`) now pass.

**Fault 2 (STILL OPEN, blocks `ALL RV32 NVME FW CHECKS PASS`): seed rv32 `i64`
codegen miscompiles the selftest value-flow.** With the hang gone, the selftest
completes but reports **every** stage failing (`_emit_fail_mask` prints all of
`REJMBSPHQIFACTDWLYKGN`), while the host logic reference passes cleanly
(`bin/simple run fw_rv32/logic_check.spl` -> `RV32 NVME FW LOGIC OK`).
`rt_native_eq`'s equality path is a correct 64-bit compare (verified in
disassembly: loads both operands as `{lo,hi}` register pairs, XOR lo+hi, `seqz`),
so the operands themselves are wrong: the seed's rv32 lowering of the selftest
bodies' `i64` arithmetic / XOR chains / `i64` function returns (routed through
the ANY / `rt_native_eq` channel) produces wrong values on-target. This is the
correctness facet of the seed ANY/tag-box wall (SEED-specific; pure-Simple
codegen is clean). It is fixable only by (a) building the ELF with the
self-hosted compiler — blocked by the interpreter cold-load timeout that is the
subject of this very bug — or (b) a seed rv32 `i64`/ANY codegen fix. It is
**not** a firmware-wiring gap and cannot be closed by touching `boot.spl` or
`entry.spl`.

Do **not** paper over Fault 2 by masking failing stage bits (e.g. `& 65535`) to
force `_emit_pass()` — that is a fake pass; the spec's PASS marker must reflect a
genuine `fail == 0` from real on-target checks.

**Spec status now:** scenario 2 ("proves the boot hook is wired") **passes**;
scenario 1 fails on exactly one expectation, `ALL RV32 NVME FW CHECKS PASS`
(both `HEAP OK` and `SVC OK` now pass). Command:
`bin/simple test test/03_system/app/nvme_firmware/nvme_rv32_baremetal_boot_spec.spl --mode=interpreter --clean --timeout 90 --sequential`.

### Native-build main fast path attempted (2026-07-05)

`src/app/cli/native_build_main.spl` now calls the pure Simple
`cli_native_build(args)` implementation directly by default and keeps the old
`native_build_worker.spl` subprocess only behind bootstrap/interpret/explicit
`SIMPLE_NATIVE_BUILD_FORCE_WORKER` fallback guards, or when the caller passes
`--timeout` so parent-enforced timeout semantics are preserved. This removes one
known worker-spawn/cold-load layer from untimed `simple native-build` and is
covered by `test/01_unit/app/cli_native_build_main_contract_spec.spl` plus the
refreshed SimpleOS/QMP source contract.

The RV32 firmware wrapper still timed out before producing
`build/nvme_fw_rv32.elf`:

```sh
NVME_RV32_BUILD_TIMEOUT_SECS=180 sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs
# NVME_RV32_BUILD_FAILED code=124 timeout=180s
```

So this bug remains open. The next blocker is the remaining native-build
compiler-load/codegen time for the RV32 source set, not just the old worker
entrypoint.
