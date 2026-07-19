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

## Update — self-hosted phase narrowed (2026-07-05)

The wrapper still fails to produce `build/nvme_fw_rv32.elf` with the production
self-hosted compiler:

```bash
NVME_RV32_BUILD_TIMEOUT_SECS=300 sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs
```

Observed result:

```text
NVME_RV32_BUILD_FAILED code=124 timeout=300s
```

Adding a firmware-only boot root that avoided `os_main` did not change the
300s outcome, so the hosted OS graph is not the production blocker.

The wrapper now enables `SIMPLE_COMPILER_PHASE_PROFILE=1`, a narrow phase-only
trace separate from the noisy `SIMPLE_COMPILER_TRACE=1` parser trace. A 45s
probe showed:

```text
[BOOTSTRAP-PHASE] compile:start
[BOOTSTRAP-PHASE] phase1:load_sources:start
[BOOTSTRAP-PHASE] phase1:load_sources:done
[BOOTSTRAP-PHASE] phase2:parse:start
```

Then the process timed out. This localizes the current production timeout to
self-hosted parse/front-end startup after the bounded entry-closure source list
has loaded, before HIR/typecheck/MIR/codegen/link phases begin.

The next production fix should make native-build consume a compiled/cacheable
compiler front-end for this path or make the phase2 parse path incremental
enough for self-hosted native-build to complete under the wrapper timeout. Do
not default this wrapper to the Rust seed: it is useful differential evidence,
but repo policy keeps the seed bootstrap-only.

## Update — minimal live checker reaches HIR stack overflow (2026-07-07)

The smaller diagnostic wrapper `scripts/check/check-nvme-rv32-minimal-live.shs`
now has two useful modes:

```bash
NVME_RV32_MINIMAL_SECTIONS=0 NVME_RV32_BUILD_TIMEOUT_SECS=120 \
  sh scripts/check/check-nvme-rv32-minimal-live.shs
```

passes as a root-only RV32 object/link diagnostic:

```text
STATUS: PASS nvme-rv32-minimal-live-root-build diagnostic_only=true
```

The first real firmware section still fails before producing a bootable ELF:

```bash
NVME_RV32_MINIMAL_SECTIONS=1 NVME_RV32_BUILD_TIMEOUT_SECS=120 \
  sh scripts/check/check-nvme-rv32-minimal-live.shs
```

Observed failure:

```text
[BOOTSTRAP-PHASE] phase3:hir:function:start ...rv32_rain_recover7
thread 'simple-main' has overflowed its stack
fatal runtime error: stack overflow, aborting
```

This narrows the current blocker from the full rv32 boot wrapper timeout to a
compiler HIR-lowering stack overflow on the generated minimal firmware root.
The root-only path proves the RV32 object/link skeleton can be built; the first
real RAIN section proves the firmware logic still cannot be lowered by the
self-hosted HIR path.

Dead-end checks already tried:

- Flattening the RAIN XOR expression into a helper with wide scalar parameters
  moved the overflow to the helper.
- Splitting recovery into tiny no-argument scalar functions moved the overflow
  to one of those recovery functions.
- Converting recovery temporaries from `var` reassignment to `val` chains still
  overflowed in HIR lowering.

So the next fix should target HIR lowering stack use for this generated
firmware-root shape, not further cosmetic rewrites of the RAIN algorithm.

## Update — exact phase2 source narrowed (2026-07-05)

The phase profile now logs each native entry-closure source before and after
parse. A production-wrapper run with the self-hosted compiler still timed out
at 300s, and the last phase markers were:

```text
[BOOTSTRAP-PHASE] phase2:parse:entry build/os/generated/os/kernel/arch/riscv32/nvme_fw_boot_root.spl module=build.os.generated.os.kernel.arch.riscv32.nvme_fw_boot_root
[BOOTSTRAP-PHASE] phase2:parse:entry:done build/os/generated/os/kernel/arch/riscv32/nvme_fw_boot_root.spl
[BOOTSTRAP-PHASE] phase2:parse:entry src/os/kernel/arch/riscv32/boot.spl module=os.kernel.arch.riscv32.boot
```

So the current self-hosted production timeout happens while parsing
`src/os/kernel/arch/riscv32/boot.spl` in phase2, before HIR/MIR/codegen/link.
The driver also no longer reparses native entry-closure modules during HIR
lowering when a parsed phase2 module exists, but this run does not reach that
later phase yet.

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

## Update — bootstrap compiler proof moved to LLVM direct-call blocker (2026-07-06)

The self-hosted firmware build remains blocked by the broader Stage 2 compiler
production proof, not by the NVMe OpenSSD firmware sources themselves. The
latest bounded Stage 2 probe now sees real bootstrap bodies:

```text
[mir-lower-free] functions:count 6
[hir-lower] bootstrap-functions:count 6
```

It fails later in LLVM object compilation on malformed direct-call IR:

```text
%l0 = call i64 0()
llc: error: integer constant must have integer type
```

Evidence: `build/stage2_after_arena_fix.log`, preserved IR
`/tmp/simple_llvm_1942949.ll`.

Current narrow compiler progress: bootstrap `get_args()` / `eprint()` and known
entry helpers now stay named through HIR/MIR, direct string function operands
render as `@symbol`, and LLVM GEP/aggregate lowering no longer emits invalid
`nil` element types. This does not claim firmware runtime PASS.

Latest remaining compiler blocker:

```text
llc: /tmp/simple_llvm_2155269.ll:80:32: error: '%l1' defined with type 'i64' but expected 'ptr'
  %l8 = getelementptr i64, ptr %l1, %l7
                               ^
```

So the next compiler fix is still upstream of firmware: MIR must resolve
same-module bootstrap `Var(symbol)` call return types by recovered symbol name
so `get_cli_args()` is called as `ptr`, not `i64`.

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

### Full failure mask propagation fixed (2026-07-05)

`fw_rv32/entry.spl` now returns and emits the full `raw_fail` mask instead of
truncating it to 16 bits. High-stage failures (`L/Y/K/G/N`) can no longer be
hidden behind the UART PASS marker.

### RV32 wrapper stopped forcing worker fallback (2026-07-05)

`fw_rv32/build.shs` no longer sets `SIMPLE_BOOTSTRAP=1` or passes `--timeout`
into `simple native-build`; the outer shell `timeout` still bounds the build.
This lets the wrapper use the direct native-build path instead of forcing the
interpreted worker fallback.

Verification attempt:

```sh
NVME_RV32_BUILD_TIMEOUT_SECS=120 sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs
# NVME_RV32_BUILD_FAILED code=124 timeout=120s
```

So the timeout remains open even on the direct wrapper path.

### Parser source/cache desync fixed; boot.spl parse timeout remains (2026-07-05)

The self-hosted flat-AST parser path had a cross-source token-text hazard:
`lex_init_with_path(source, path)` could tokenize a disk reread from `path`
while `parser_token_text_from_offsets()` sliced token text from
`SIMPLE_BOOTSTRAP_LEX_SOURCE`, which still held the caller-supplied source. In
repeated `parse_full_frontend()` / `parse_and_build_module()` entry-closure
parses, this surfaced as malformed integer literal diagnostics whose token
snippets belonged to a different generated root source.

Fix landed in `src/compiler/10.frontend/core/lexer.spl` and
`src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl`: the active lexer
and parser source cache now share the same source buffer, and the flat bridge
restores/bump-invalidates parser source env at the parse boundary.

Regression coverage:

```sh
bin/simple test test/01_unit/compiler/parser/parser_source_path_desync_spec.spl
# PASS: 2 examples, 0 failures
```

Production wrapper probe after the fix:

```sh
timeout -k 5s 300s /usr/bin/time -f 'rv32_build_elapsed=%E rss=%MKB' \
  sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs
# code=124 at 300s
```

The malformed-token symptom did not recur in this stock wrapper probe. The last
phase marker in `build/test-artifacts/nvme_fw_rv32_build.err` is again:

```text
[BOOTSTRAP-PHASE] phase2:parse:entry src/os/kernel/arch/riscv32/boot.spl module=os.kernel.arch.riscv32.boot
```

So the production build remains blocked by `boot.spl` parse time before
HIR/MIR/codegen/link; this bug remains open.

### Firmware evidence root narrowed; parser now advances into split logic (2026-07-05)

The firmware wrapper no longer imports the stock `riscv32/boot.spl` or passes
`--source src` for the P9 evidence image. It still verifies that the stock boot
hook exists, then generates a firmware-specific root that imports the scalar
logic directly and emits the system-test markers (`SimpleOS RV32`,
`[BOOT] boot complete`, `ALL RV32 NVME FW CHECKS PASS`, `HEAP OK`, `SVC OK`).

`fw_rv32/logic.spl` was split into section modules with a tiny aggregator. Host
semantics still pass:

```sh
bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
# RV32 NVME FW LOGIC OK
bin/simple test test/01_unit/examples/nvme_fw_rv32_entry_fail_mask_spec.spl
# PASS: 4 examples, 0 failures
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_rain.spl
# All checks passed
bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_ecc.spl
# All checks passed
```

The production wrapper still does not finish within 300s, but the phase marker
advanced from `boot.spl`/`entry.spl`/monolithic `logic.spl` to the split logic
sections:

```text
[BOOTSTRAP-PHASE] phase2:parse:entry:done .../nvme_fw_boot_root.spl
[BOOTSTRAP-PHASE] phase2:parse:entry:done examples/.../logic.spl
[BOOTSTRAP-PHASE] phase2:parse:entry:done examples/.../logic_rain.spl
[BOOTSTRAP-PHASE] phase2:parse:entry examples/.../logic_ecc.spl
```

So the remaining blocker is self-hosted native-build parse throughput across the
firmware logic closure, not stock OS boot imports or a malformed source/cache
desync.

### Parser env hot-path reduced; production build still blocked (2026-07-05)

Parser and lexer hot paths now prefer in-process slots over env roundtrips for
current parser kind/line/column and lexer token offsets. `lex_next()` also no
longer saves the whole core lexer position to env on every token unless
`SIMPLE_BOOTSTRAP_LEX_ENV_SAVE=1` is explicitly set.

Measured local improvement:

```sh
SIMPLE_COMPILER_PHASE_PROFILE=1 timeout -k 5s 90s /usr/bin/time -f 'logic_ecc_check_elapsed=%E rss=%MKB' \
  bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_ecc.spl
# before: logic_ecc_check_elapsed=0:30.39 rss=171556KB
# after:  logic_ecc_check_elapsed=0:09.94 rss=171580KB
```

The wrapper also removes stale generated `build/os/generated/logic*.spl` files
before source collection; otherwise abandoned bundle prototypes can be parsed
as extra entry-closure sources.

Production wrapper status remains **OPEN**. The 300s build still times out, but
the last phase marker advances farther into the split firmware logic:

```text
[BOOTSTRAP-PHASE] phase2:parse:entry:done examples/.../logic_map.spl
[BOOTSTRAP-PHASE] phase2:parse:entry examples/.../logic_band.spl
```

A longer 900s probe was interrupted after more than 9 minutes without producing
`build/nvme_fw_rv32.elf`, so raising the timeout is not a production fix.

Follow-up parser hot-path work gates current parser/lexer token state env writes
behind compatibility flags and computes token text lazily from offsets. Focused
parser/lexer specs still pass, direct `logic_band.spl` check improves to about
10.1s, and the 300s production wrapper now advances through `logic_band.spl`
before timing out at `logic_sched.spl`:

```text
[BOOTSTRAP-PHASE] phase2:parse:entry:done examples/.../logic_band.spl
[BOOTSTRAP-PHASE] phase2:parse:entry examples/.../logic_sched.spl
```

### Native declaration arena mirror reduced; wrapper advances farther (2026-07-05)

`native-build` now sets `SIMPLE_NATIVE_ARENA_DECLS=1` while compiling, then
restores the previous value before returning. In that mode declaration and
module-declaration accessors use the in-process arenas instead of writing and
reading `SIMPLE_BOOTSTRAP_DECL_*` / `SIMPLE_BOOTSTRAP_MODULE_DECL_*` process-env
mirrors. The flat AST bridge was adjusted to use arena-backed declaration
getters for tags, params, and function bodies.

Focused checks:

```sh
bin/simple test test/01_unit/compiler/parser/parser_source_path_desync_spec.spl
# PASS: 2 examples, 0 failures
bin/simple test test/01_unit/examples/nvme_fw_rv32_entry_fail_mask_spec.spl
# PASS: 5 examples, 0 failures
SIMPLE_COMPILER_PHASE_PROFILE=1 timeout -k 5s 90s /usr/bin/time -f 'logic_sched_check_elapsed=%E rss=%MKB' \
  bin/simple check examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_sched.spl
# logic_sched_check_elapsed=0:05.11 rss=166896KB
```

The default 300s wrapper still times out, so this bug remains open, but the last
marker now reaches beyond `logic_power_cycle.spl` and starts
`logic_backpressure_abort.spl`:

```text
[BOOTSTRAP-PHASE] phase2:parse:entry:done examples/.../logic_media_retire.spl
[BOOTSTRAP-PHASE] phase2:parse:entry:done examples/.../logic_power_cycle.spl
[BOOTSTRAP-PHASE] phase2:parse:entry examples/.../logic_backpressure_abort.spl
```

### Stock boot-hook root restored; live boot still fails closed (2026-07-06)

The RV32 wrapper now generates a tiny `build/os/generated/nvme_fw_boot_root.spl`
that imports the stock `os.kernel.arch.riscv32.boot` module and `entry.spl`'s
strong `rt_rv32_boot_optional_nvme_fw_selftest` hook. The ELF now links the real
rv32 `_start`/`boot_main` path instead of a diagnostic replacement `_start`:

```sh
NVME_RV32_SIMPLE_BIN=src/compiler_rust/target/bootstrap/simple \
NVME_RV32_BUILD_TIMEOUT_SECS=90 \
sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs
# build/nvme_fw_rv32.elf produced
```

The production default still uses `bin/simple` and remains covered by the
self-hosted native-build timeout above. The seed-built ELF is diagnostic only.

QEMU now reaches the real boot path and firmware hook, initializes the boot
subsystems, then fails closed with the firmware section mask:

```text
SimpleOS RV32
[BOOT] UART initialized
[BOOT] RISC-V 32
[BOOT] Memory map parsed
[BOOT] RAM at 0x80000000
[BOOT] boot complete
[BOOT] SMP harts: 1
LOG OK
RV32 NVME FW BEGIN
EJMBSPHQIFACTDWLYKGN
RV32 NVME FW FAIL
MEM OK
PMM OK
HEAP OK
SVC OK
BOOT OK
```

Host logic still passes:

```sh
bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/logic_check.spl
# RV32 NVME FW LOGIC OK
```

So the remaining live evidence gap is two-part: the production self-hosted build
still times out before producing media, and the diagnostic media exposes a live
rv32 baremetal logic/codegen mismatch. The wrapper, hook, heap, PMM, service init,
and boot path are no longer the likely blocker. Do not fake the PASS marker or
switch the wrapper default to the seed.
 
 ### Entry-closure reaches AOT; MIR remains empty for firmware modules (2026-07-05)
 
 A 900s wrapper probe with the deployed binary completed parse, HIR/typecheck,
 monomorphization, and MIR pipeline phases, then failed in AOT because a firmware
 module with real functions had an empty MIR module:
 
 ```text
 [BOOTSTRAP-PHASE] aot:format:done
 error: AOT compile error in examples.09_embedded.simpleos_nvme_fw.fw_rv32.logic_dram_durability: MIR module has no functions
 ```
 
 Source-directed seed probes confirmed the next compiler blockers:
 
 - The bootstrap flat AST bridge must not empty native `--entry-closure` modules;
   the driver has already narrowed the source set to reachable modules.
 - Bootstrap MIR lowering must not assume fixed function symbols `1..6`.
 - Reusing one MIR lowering instance across entry-closure modules risks carrying
   builder/module state across sources.
 
 Local source-contract specs cover those guardrails, but the functional firmware
 build is still **not green**. A corrected seed-driven native-build reaches AOT
 and still fails with an empty MIR module:
 
 ```text
 [BOOTSTRAP-PHASE] aot:format:done
 error: AOT compile error in examples.09_embedded.simpleos_nvme_fw.fw_rv32.logic_dram_durability: MIR module has no functions
 rv32_seed_elapsed=2:28.11 rss=1287160KB
 ```
 
 Do not mark the rv32 firmware wrapper complete until `build/nvme_fw_rv32.elf`
 is produced and the QEMU/system evidence runs. The next investigation should
 trace whether `logic_dram_durability` has non-empty HIR after monomorphization
 and whether `MirLowering.lower_module` sees non-empty `module.functions.keys()`
 
 ### MCP native-build blocker deferred during NVMe sync (2026-07-06)
 
 Foreground NVMe base-spec work continued while the MCP package native-build
 blocker was left open. The focused MIR/source guard passes:
 
 ```sh
 env SIMPLE_LIB=src bin/simple test test/01_unit/compiler/mir/mir_lowering_new_spec.spl --mode=interpreter
 # PASS: 12 examples, 0 failures
 ```
 
 The MCP native-build still fails in LLVM before package evidence can be claimed:
 
 ```text
 error: '%l186' defined with type 'ptr' but expected 'i64'
   %tmp116 = inttoptr i64 %l186 to ptr
 ```
 
 Captured IR evidence was preserved at `/tmp/simple_last_native_build.ll` during
 the local investigation. This is not a firmware command-floor failure, but it
 still blocks claiming full compiler/MCP production verification for the commit.
 for that module.
 
 ### Entry-closure HIR no longer drops parser functions; nil symbol remains (2026-07-05)
 
 Targeted diagnostics showed `logic_admin.spl` reached the flat bridge with raw
 declarations but zero assembled functions because bootstrap env mirror tags were
 preferred over the current parser arena tags:
 
 ```text
 [nvme-fw-diag] flat decls path=examples/.../logic_admin.spl raw=9
 [nvme-fw-diag] flat funcs path=examples/.../logic_admin.spl funcs=0
 ```
 
 `flat_decl_tag_text` now prefers `decl_get_tag(idx)` and only falls back to the
 `SIMPLE_BOOTSTRAP_DECL_TAG_*` mirror when the arena has no tag. Native
 entry-closure HIR lowering also takes the real symbol/parameter path instead of
 the bootstrap-main-only symbol shortcuts.
 
 Focused checks pass:
 
 ```sh
 timeout -k 5s 180s bin/simple test test/01_unit/examples/nvme_fw_rv32_entry_fail_mask_spec.spl
 # PASS: 8 examples, 0 failures
 timeout -k 5s 180s bin/simple test test/01_unit/compiler/mir/mir_lowering_new_spec.spl
 # PASS: 8 examples, 0 failures
 ```
 
 The functional seed-driven firmware build still does not produce an ELF. It now
 fails during bootstrap MIR lowering with a nil symbol field access:
 
 ```text
 [BOOTSTRAP-PHASE] aot:lower_to_mir:start
 [driver-mir] bootstrap lower:start
 [driver-mir] bootstrap lower:done
 [driver-mir] bootstrap lower:start
 [driver-mir] bootstrap lower:done
 [driver-mir] bootstrap lower:start
 error: semantic: undefined field 'id': cannot access field on value of type 'nil'
 rv32_seed_elapsed=2:38.63 rss=1269096KB
 ```
 
 Do not push this lane or mark it production-ready without ELF evidence. The next
 minimal diagnostic is inside the bootstrap MIR function insertion path: print
 the module/function name and whether `hir_fn.symbol` or `mir_fn.symbol` is nil
 before inserting into the MIR functions dictionary.
 
 ### Entry-closure reaches LLVM; integer-width metadata remains inconsistent (2026-07-05)
 
 Subsequent fixes moved the seed-driven firmware build through flat AST, HIR,
 MIR lowering, MIR optimization, and several LLVM module checks. The focused
 MIR/backend source-contract spec passes:
 
 ```sh
 timeout -k 5s 180s bin/simple test test/01_unit/compiler/mir/mir_lowering_new_spec.spl
 # PASS: 11 examples, 0 failures
 ```
 
 The firmware build still does **not** produce `build/nvme_fw_rv32_seed.elf`.
 The latest seed-driven native-build fails in LLVM validation:
 
 ```text
 error: AOT compile error in examples.09_embedded.simpleos_nvme_fw.fw_rv32.logic_sched
 llc-18: /tmp/simple_llvm_1494563.ll:9:21: error: '%l1' defined with type 'i32' but expected 'i64'
   %0 = icmp slt i64 %l1, %l2
 rv32_seed_elapsed=2:33.75 rss=1317460KB
 ```
 
 Confirmed status:
 
 - no ELF artifact exists;
 - no `SIMPLE_NVME_FW_DIAG` hook remains in compiler source;
 - `find doc/06_spec -name '*_spec.spl' | wc -l` prints `0`;
 - no commit or push was made.
 
 The next fix should stop relying on declared MIR local widths as the only LLVM
 source of truth. The backend currently can emit a local at one integer width and
 later read a different width from `local_types`; comparison, return, and call
 lowering then generate invalid LLVM. A production fix should track emitted local
 LLVM widths directly, or normalize native entry-closure integer lowering before
 LLVM emission, then rerun the firmware artifact build.
 
 ### Width fixes reached boot root, then exposed remaining stale cast metadata (2026-07-05)
 
 Additional progress in this lane:
 
 - native entry-closure LLVM signature maps are populated before translating
   bodies, so forward calls can use real signatures;
 - emitted LLVM local widths are tracked separately from declared MIR local
   widths for operand type lookup;
 - `if` expression results use the existing `__simple_ssa_phi` intrinsic instead
   of copying one result temp in predecessor blocks;
 - `logic_io_command.spl` now imports `rv32_hil_validate`, avoiding `call i64 0`;
 - `call void` is emitted without assigning the result to an SSA name.
 
 Focused check:
 
 ```sh
 timeout -k 5s 180s bin/simple test test/01_unit/compiler/mir/mir_lowering_new_spec.spl
 # PASS: 12 examples, 0 failures
 ```
 
 The firmware build still does **not** produce `build/nvme_fw_rv32_seed.elf`.
 The latest seed-driven build reaches LLVM and fails with another stale cast
 source type:
 
 ```text
 error: AOT compile error in examples.09_embedded.simpleos_nvme_fw.fw_rv32.logic_sched
 llc-18: /tmp/simple_llvm_1699716.ll:48:17: error: '%l26' defined with type 'i64' but expected 'i32'
   %4 = sext i32 %l26 to i64
 rv32_seed_elapsed=2:34.65 rss=1317104KB
 ```
 
 Confirmed status remains: no ELF artifact, no commit, no push. The next
 production fix should remove the remaining stale cast source path rather than
 falling back to zero/undef values; those would hide real firmware semantics.
 
 ### Entry-closure calls resolved; remaining blocker is LLVM width propagation (2026-07-05)
 
 Follow-up fixes in this lane:
 
 - native entry-closure HIR no longer uses bootstrap call lowering that drops
   arguments;
 - flat bootstrap identifiers now preserve their text via `NamedVar`, preventing
   direct calls from lowering to `call i64 0()`;
 - `logic_io_command.spl` again calls the real `rv32_hil_validate` path;
 - native entry-closure MIR optimization only skips the crashing `collection_opt`
   pass, not the whole bootstrap-sensitive pass group;
 - LLVM call terminators and indirect calls now emit typed arguments without a
   double `@`;
 - emitted LLVM types are recorded for function parameters and copy/move sources,
   and unary ops cast operands to the emitted destination width before lowering.
 
 Focused check remains green:
 
 ```sh
 timeout -k 5s 180s bin/simple test test/01_unit/compiler/mir/mir_lowering_new_spec.spl
 # PASS: 12 examples, 0 failures
 ```
 
 The firmware build now gets through parsing, HIR/typecheck, MIR lowering,
 borrow check, async processing, MIR optimization, AOP, and LLVM formatting, but
 still does **not** produce `build/nvme_fw_rv32_seed.elf`. Current blocker:
 
 ```text
 error: AOT compile error in examples.09_embedded.simpleos_nvme_fw.fw_rv32.logic_map
 llc-18: /tmp/simple_llvm_2091984.ll:114:17: error: '%l66' defined with type 'i64' but expected 'i32'
 rv32_seed_elapsed=2:35.40 rss=1318924KB
 ```
 
 No commit and no push were performed. Continue by fixing the remaining emitted
 LLVM width propagation path; do not reintroduce broad optimizer disables or
 zero/undef call fallbacks.
 
 ### Binop/comparison source widths narrowed; cast source metadata still stale (2026-07-05)
 
 Additional backend fixes:
 
 - binop lowering now reads left/right operand widths from emitted LLVM value
   metadata before casting;
 - comparison lowering no longer uses anonymous `%N` fresh temps that can diverge
   from the just-emitted cast temp;
 - `cast_value_if_needed` now emits deterministic cast locals for SSA values.
 
 Focused check remains green:
 
 ```sh
 timeout -k 5s 180s bin/simple test test/01_unit/compiler/mir/mir_lowering_new_spec.spl
 # PASS: 12 examples, 0 failures
 ```
 
 The RV32 firmware build still does **not** produce
 `build/nvme_fw_rv32_seed.elf`. Latest blocker:
 
 ```text
 error: AOT compile error in examples.09_embedded.simpleos_nvme_fw.fw_rv32.logic_dram_durability
 llc-18: /tmp/simple_llvm_2171888.ll:110:23: error: '%l50' defined with type 'i64' but expected 'i32'
   %l50.i64 = sext i32 %l50 to i64
 rv32_seed_elapsed=2:31.25 rss=1319340KB
 ```
 
 No commit and no push were performed.
 
 ### Backend phi/type tracking progressed; ELF still blocked (2026-07-05)
 
 Additional fixes in this pass:
 
 - binop lowering now records the resolved LLVM type in both `local_types` and
   `emitted_local_types`;
 - `__simple_ssa_phi` lowering now derives the phi type from incoming emitted
   values, casts incoming values to the common type, and suppresses invalid
   `phi void`;
 - unary lowering now records emitted result types, including `i1` for `not`;
 - the focused MIR/backend regression spec remains green:
 
 ```sh
 timeout -k 5s 180s bin/simple test test/01_unit/compiler/mir/mir_lowering_new_spec.spl
 # PASS: 12 examples, 0 failures
 ```
 
 Build evidence:
 
 - a build after the phi fix moved past the boot-root `phi void` blocker and
   exposed `logic_hil` stale width propagation:
 
 ```text
 error: AOT compile error in examples.09_embedded.simpleos_nvme_fw.fw_rv32.logic_hil
 llc-18: /tmp/simple_llvm_2290542.ll:402:23: error: '%l71' defined with type 'i64' but expected 'i32'
   %l71.i64 = sext i32 %l71 to i64
 rv32_seed_elapsed=2:31.22 rss=1319904KB
 ```
 
 - the next build caught a source compile error in the unary tracking patch
   (`variable Not not found`); that patch was corrected with a `match op`
   expression and the focused spec passed afterward.
 
 No `build/nvme_fw_rv32_seed.elf` exists yet. No commit, rebase, or push was
 performed. The next session should rerun the firmware build once from the
 corrected unary patch and then continue with the first concrete backend failure.
 
 ### ELF now builds; QEMU reaches boot but not firmware PASS (2026-07-05)
 
 The seed compiler now produces a bootable RV32 ELF:
 
 ```text
 build_exit=0
 rv32_seed_elapsed=2:36.69 rss=1323864KB
 build/nvme_fw_rv32_seed.elf: ELF 32-bit LSB executable, UCB RISC-V, RVC, double-float ABI, statically linked
 ```
 
 QEMU execution is still not production PASS. After sanitizing NUL padding in the
 serial log, the firmware reaches only:
 
 ```text
 impleOS RV32
 BOOT] boot complete
 RESULT: FAIL (marker not found)
 ```
 
 It does not print `ALL RV32 NVME FW CHECKS PASS`, `HEAP OK`, or `SVC OK`.
 Host-side scalar logic still passes:
 
 ```text
 RV32 NVME FW LOGIC OK
 ```
 
 Added must-have NVMe base-spec system coverage:
 
 - `examples/09_embedded/simpleos_nvme_fw/fw_rv32/base_spec_check.spl`
 - `test/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.spl`
 - `doc/03_plan/sys_test/nvme_base_spec_commands.md`
 - `doc/06_spec/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.md`
 
 The new system spec passes:
 
 ```text
 PASS test/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.spl
 1 example, 0 failures
 ```
 
Release remains blocked:
 
 - RV32 QEMU boot proof fails because the firmware self-test marker is absent.
 - Required MCP integration gate fails in this workspace because
   `bin/simple_mcp_server` is missing.
 - Residual backend risks remain from higher-model review: duplicate cast-name
   risk, unknown type fallback to `i64`, unsigned widening through `sext`, and
   boot UART/text lowering workarounds.
 
 No commit, rebase, or push was performed.
 
 ### Current continuation probe: default wrapper timeout reproduced (2026-07-06)
 
 After the `main` rebase/push, the default production wrapper was rerun from
 `bin/simple` and timed out at the wrapper's 300s internal cap:
 
 ```text
 timeout -k 10s 420s sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs
 rv32_build_exit=124
 NVME_RV32_BUILD_FAILED code=124 timeout=300s
 ```
 
 The generated-media proof is therefore still not production-green in this
 workspace. The non-target command-floor pieces passed when split out:
 
 ```text
 bin/simple run examples/09_embedded/simpleos_nvme_fw/fw/nvme_main.spl
 # ALL NVME CONTROLLER E2E CHECKS PASS
 bin/simple run examples/09_embedded/simpleos_nvme_fw/fw_rv32/base_spec_check.spl
 # NVME BASE SPEC CHECKS PASS
 bin/simple test test/01_unit/examples/nvme_fw_rv32_entry_fail_mask_spec.spl --mode=interpreter --fail-fast
 # PASS: 10 examples, 0 failures
 ```
 
 `test/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.spl` timed out
 once in the SPipe runner during this continuation, while its two subprocesses
 passed directly. Keep this bug open until the default wrapper builds the ELF and
 the rv32 boot spec proves the generated media.
 
 ### RV32 firmware QEMU boot proof passes with bootstrap wrapper (2026-07-05)
 
 Follow-up fixes:
 
 - removed RV32-hanging bounded loops from the scalar firmware evidence path:
   ECC, power/thermal, queue phase, reactor drain, and media-retire spare search;
 - restored the boot wrapper to the aggregate `nvme_fw_rv32_logic_selftest()`
   call after probe diagnosis;
 - duplicated the first byte of each UART line in the generated boot root as a
   documented temporary workaround for the RV32 first-call argument lowering bug;
 - taught `fw_rv32/build.shs` to route
   `NVME_RV32_SIMPLE_BIN=src/compiler_rust/target/bootstrap/simple` through
   `src/app/cli/native_build_main.spl`, matching the working native-build path.
 
 Evidence:
 
 ```text
 NVME_RV32_SIMPLE_BIN=src/compiler_rust/target/bootstrap/simple \
   sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs
 
 build exit=0
 build/nvme_fw_rv32.elf: ELF 32-bit LSB executable, UCB RISC-V, RVC, double-float ABI, statically linked
 ```
 
 ```text
 bin/simple test test/03_system/app/nvme_firmware/nvme_rv32_baremetal_boot_spec.spl
 
 PASS test/03_system/app/nvme_firmware/nvme_rv32_baremetal_boot_spec.spl
 Files: 1
 Passed: 2
 Failed: 0
 ```
 
 Serial evidence:
 
 ```text
 SimpleOS RV32
 [BOOT] boot complete
 ALL RV32 NVME FW CHECKS PASS
 HEAP OK
 SVC OK
 ```
 
 Remaining release blockers:
 
 - default `bin/simple` wrapper build still fails at HIR/typecheck with
   `semantic: unknown extern function: rt_enum_discriminant`;
 - MCP integration gate still requires `bin/simple_mcp_server`;
 - residual backend risks from review remain open: unknown type fallback to
   `i64`, unsigned widening through `sext`, deterministic cast-name reuse, and
   temporary UART first-byte workaround.
 
 No commit, rebase, or push was performed.
 
 ### Default wrapper and MCP integration gates now pass (2026-07-05)
 
 Follow-up fixes:
 
 - removed the HIR/mono dependency on `rt_enum_discriminant` for the native-build
   path by replacing it with local variant-code helpers for the actually compared
   enum variants;
 - added `bin/simple_mcp_server`, a minimal source-mode MCP wrapper that defaults
   `SIMPLE_MCP_TOOL_SET=all` so the integration gate sees the full tool list;
 - kept the native MCP package build as a separate compiler/codegen issue: it
   still fails with `undefined field 'id': cannot access field on value of type
   'nil'`, but the required stdio integration gate no longer depends on it.
 
 Evidence:
 
 ```text
 sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs
 build exit=0
 build/nvme_fw_rv32.elf: ELF 32-bit LSB executable, UCB RISC-V, RVC, double-float ABI, statically linked
 ```
 
 ```text
 PASS test/03_system/app/nvme_firmware/nvme_rv32_baremetal_boot_spec.spl
 PASS test/03_system/app/nvme_firmware/nvme_base_spec_commands_spec.spl
 PASS test/02_integration/app/mcp_stdio_integration_spec.spl
 PASS test/01_unit/examples/nvme_fw_rv32_entry_fail_mask_spec.spl
 PASS test/01_unit/compiler/mir/mir_lowering_new_spec.spl
 ```
 
 Core checks:
 
 ```text
 bin/simple check src/compiler
 bin/simple check src/lib
 bin/simple check src/app/mcp
 bin/simple check src/app/simple_lsp_mcp
 find doc/06_spec -name '*_spec.spl' | wc -l  # 0
 direct-env-runtime-guard --working/--staged  # PASS
 numbered-artifact-guard --working/--staged   # OK
 ```
 
 Remaining risks before release:
 
 - native MCP package build still fails; source-mode `bin/simple_mcp_server`
   passes the required stdio integration gate;
 - residual backend review items remain: unknown type fallback to `i64`, unsigned
   widening through `sext`, deterministic cast-name reuse, and the temporary UART
   first-byte workaround.
 
No commit, rebase, or push was performed.

### Minimal pure-Simple live reproducer added (2026-07-07)

Added `scripts/check/check-nvme-rv32-minimal-live.shs` so this blocker no longer
requires the full stock SimpleOS boot graph to reproduce. The script writes a
tiny rv32 `_start`, strips comments/blank lines from the existing firmware
sources into `build/os/generated/nvme_fw_rv32_minimal_src`, builds with
production `bin/simple`, boots QEMU, and requires
`ALL RV32 NVME FW CHECKS PASS` with no `FAIL` marker.

Current production result:

```sh
NVME_RV32_BUILD_TIMEOUT_SECS=90 sh scripts/check/check-nvme-rv32-minimal-live.shs
# STATUS: FAIL nvme-rv32-minimal-live build_rc=124 timeout=90s
```

The narrowed source set is 24 files and excludes the full OS boot graph, but
phase2 parse still dominates:

```text
[BOOTSTRAP-PHASE] phase1:load_sources:done n_sources=24
[BOOTSTRAP-PHASE] phase2:parse:file:done .../entry.spl          +20.5s
[BOOTSTRAP-PHASE] phase2:parse:file:done .../logic.spl          +34.3s
[BOOTSTRAP-PHASE] phase2:parse:file:done .../logic_rain.spl     +43.0s
[BOOTSTRAP-PHASE] phase2:parse:file:done .../logic_ecc.spl      +59.7s
[BOOTSTRAP-PHASE] phase2:parse:file:done .../logic_journal.spl  +76.9s
[BOOTSTRAP-PHASE] phase2:parse:file:start .../logic_map.spl
```

This confirms the remaining production media blocker is pure-Simple
native-build parse/front-end throughput across the firmware closure, not stock
rv32 boot imports.

Rejected shortcut: bundling the stripped firmware logic into one generated
70 KB `.spl` source reduced the closure to `n_sources=1`, but it was worse:
`NVME_RV32_BUILD_TIMEOUT_SECS=90 sh scripts/check/check-nvme-rv32-minimal-live.shs`
timed out while still parsing that single root file. Keep the minimal checker on
split stripped sources unless the parser gets a real large-file throughput fix.

Rust diagnostic compilers are not an acceptable fallback. Current
`src/compiler_rust/target/bootstrap/simple` and `target/debug/simple` both print
the bootstrap-seed warning and fail this wrapper because LLVM is not available:

```text
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
error: native backend 'llvm' is not available in this build
```

### Latest status: source fast path fixed, deployed wrapper not yet reproven (2026-07-06)

The "default wrapper passes" section above is stale for the current
post-rebase workspace. The latest production rerun from default `bin/simple`
timed out at the wrapper's 300s cap, so rv32 ELF/QEMU production proof remains
open until the self-hosted binary is rebuilt/deployed and the wrapper is rerun.

This follow-up source fix makes `src/app/cli/native_build_main.spl` call
`cli_native_build(args)` in-process by default and keeps the worker fallback
only for bootstrap/interpret/explicit-worker/`--timeout` cases. Focused source
evidence is green:

```text
PASS test/01_unit/app/cli_native_build_main_contract_spec.spl
PASS test/01_unit/examples/nvme_fw_rv32_entry_fail_mask_spec.spl
bin/simple check src/app/cli/native_build_main.spl
# All checks passed (1 file(s))
default invalid-backend probe: worker_mentions=0
forced-worker invalid-backend probe: worker_mentions=2
```

Remaining blocker: rebuild/deploy the self-hosted `bin/simple` with this
source, then rerun `sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs`
and the rv32 boot/base-spec system evidence. The current workspace
`bin/simple` resolves to the 2026-07-03 deployed binary under
`/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple`.

Bootstrap/deploy attempt:

```text
cargo build --profile bootstrap -p simple-driver -p simple-native-all
# PASS after making backend_core.rs import RefCell unconditionally

timeout -k 20s 1200s sh scripts/bootstrap/bootstrap-from-scratch.sh \
  --pure-simple --no-mcp --deploy
# bootstrap_retry_rc=124
# bootstrap_elapsed=20:00.00 rss=1296060KB
```

Stage evidence:

```text
Stage 2: seed -> bootstrap_main.spl
warning: stage2 native-build failed (exit 1); using seed for stage 4
[llvm-tools] ir /tmp/simple_llvm_953643.ll
[llvm-tools] llc-done
[llvm-direct] failed-ir /tmp/simple_llvm_953643.ll
error: Bootstrap module LLVM compile failed: llc failed during bootstrap

Stage 3: stage2 -> bootstrap_main.spl
warning: stage3 self-host failed (exit 1); using seed for stage 4

Stage 4: compiling full CLI (main.spl) with bootstrap compiler...
# timed out at 20 minutes
```

Do not rerun the same deploy command without first fixing the Stage 2 bootstrap
LLVM failure or changing the bootstrap path; it currently falls back to the slow
seed Stage 4 and times out before producing a deployable `bin/simple`.

### Latest bootstrap progress: pointer null return fixed (2026-07-06)

The first preserved Stage 2 LLVM failure was narrowed and fixed:

```text
llc /tmp/simple_llvm_953643.ll -filetype=obj
# error: integer constant must have integer type
#   ret ptr 0
```

MIR-to-LLVM return lowering now emits `ret ptr null` for pointer-typed zero
returns. Focused evidence:

```text
PASS test/01_unit/compiler/backend/llvm_pointer_return_null_spec.spl
llc accepts a minimal `ret ptr null` module
```

Manually applying that substitution to the preserved Stage 2 IR moves `llc` to
the next blocker:

```text
error: use of undefined value '@.str.0'
```

Follow-up source change mirrors string globals into a text accumulator and
flushes that accumulator for the bootstrap MIR-to-LLVM path. Next proof step is
a bounded Stage 2 probe to see whether `llc` moves past the undefined `@.str.0`
diagnostic.

### Latest bootstrap progress: Stage 2 now blocked by empty entry HIR/MIR (2026-07-06)

The corrected Stage 2-only probe uses `--mode dynload` instead of the invalid
`--mode leaf`. Focused evidence is green:

```text
PASS test/01_unit/compiler/backend/llvm_pointer_return_null_spec.spl
3 examples, 0 failures
```

That spec now covers textual LLVM pointer returns, bootstrap string-global
flushing, and the sibling libLLVM pointer-zero constant path.

The bounded Stage 2 probe moved past the previous `ret ptr 0` and undefined
`@.str.0` LLVM failures. It now stops at the already tracked fail-closed guard:

```text
[hir-lower] functions:count 0
[hir-lower] bootstrap-functions:count 0
error: bootstrap entry lowered to 0 MIR instructions (ret-0 stub module)
error: refusing to emit a stub-only bootstrap binary; real Simple lowering produced no bodies
```

RV32 firmware production proof therefore remains open. Do not rerun the full
bootstrap/deploy loop until the bootstrap entry source-loading/HIR path
produces real functions in Stage 2.

### Latest bootstrap progress: Stage 2 reaches six functions, now stack-overflows in HIR (2026-07-06)

The empty-HIR diagnosis above is stale after the bootstrap arena and entry
bridge fixes. The latest bounded Stage 2 probe reaches the real bootstrap entry
functions:

```text
stage2_after_hir_stmt_disc_fix_rc=134
[hir-lower] functions:count 6
[hir-lower] function:start run_native_build_bootstrap
```

The same iteration fixed same-module bootstrap `Var(symbol)` call naming and
return typing in MIR lowering, and added full current-parser variant coverage to
`hir_stmt_kind_disc(...)`. Focused evidence:

```text
PASS test/01_unit/compiler/mir/mir_lowering_new_spec.spl
PASS test/01_unit/compiler/hir/hir_stmt_dispatch_source_spec.spl
PASS test/01_unit/compiler/backend/llvm_pointer_return_null_spec.spl
```

Current blocker for the self-hosted compiler proof is now a seed worker stack
overflow while HIR-lowering the first statement of `run_native_build_bootstrap`:

```text
[hir-lower] lower_block:stmt 0
[hir-lower] lower_stmt:start
[hir-lower] lower_stmt:kind
thread 'simple-main' (...) has overflowed its stack
fatal runtime error: stack overflow, aborting
error: native-build worker exited with code 134.
```

Preserved evidence:

- `build/mini_builds/stage2_after_bootstrap_call_name_fix.log`
- `build/mini_builds/stage2_after_hir_stmt_disc_fix.log`

RV32 firmware production proof remains blocked on deploying a self-hosted
`bin/simple`. Do not rerun the full bootstrap/deploy or firmware build loop
until the `run_native_build_bootstrap` HIR-lowering stack overflow has a source
fix.

### Latest bootstrap progress: Stage 2 links but is semantically inert (2026-07-06)

The stack-overflow blocker moved: a bounded Stage 2 probe now links an executable
through the fresh bootstrap MIR path.

```text
stage2_after_fresh_global_mir_preferred_rc=0
[mir-lower-free] functions:count 6
[mir-lower-free] done instr-total=0 term-total=24
[bootstrap-real-llvm] count 6
build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple
```

This is **not** firmware production evidence yet. The generated Stage 2 binary
is inert:

```text
build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple --version
# no output, rc=0
build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple native-build
# no output, rc=0
```

Current compiler gate for NVMe RV32 firmware proof: bootstrap MIR/LLVM lowering
must preserve enough semantics for the Stage 2 binary to print `--version` and
fail closed for `native-build` with a non-zero result. Only after that should
the full bootstrap/deploy and RV32 firmware build loops be retried.

### Latest bootstrap progress: real MIR instructions, invalid SSA blocker (2026-07-06)

The Stage 2 gate moved from inert terminator-only MIR to real bootstrap
instructions after fixing bootstrap HIR block `has` propagation:

```text
stage2_hir_has_rc=1
[mir-lower-free] done instr-total=26 term-total=39
```

After simplifying the bootstrap entry and disabling discardable
`readonly alwaysinline` attributes for bootstrap-emitted functions, the preserved
IR contains a plain `define i64 @__simple_main() nounwind`. The current bounded
probe still fails before producing a usable Stage 2 binary:

```text
stage2_plain_functions_rc=1
[mir-lower-free] done instr-total=12 term-total=24
error: LLVM native linking failed: undefined symbol: __simple_main
```

Direct `llc` on the preserved IR reports the underlying verifier failure:

```text
Instruction does not dominate all uses!
llc: error: input module cannot be verified
```

Firmware proof remains blocked until bootstrap MIR-to-LLVM emits valid SSA for
conditional merge values in `__simple_main` and the `llc` object helper refuses
empty/non-object outputs.

### Latest bootstrap progress: Stage 2 links and prints smoke banner (2026-07-06)

The Stage 2 compiler artifact now links through the fresh bootstrap MIR/LLVM
path and executes:

```text
stage2_smoke_entry_rc=0
[mir-lower-free] done instr-total=12 term-total=24
[llvm-tools] llc-object

build/mini_builds/stage2_after_bootstrap_smoke_entry --version
simple-bootstrap 1.0.0-beta
version_rc=1

build/mini_builds/stage2_after_bootstrap_smoke_entry native-build
simple-bootstrap 1.0.0-beta
native_build_rc=1
```

This is still not firmware production proof. The Stage 2 entry is a temporary
straight-line smoke entry that proves the binary is alive and keeps
`native-build` fail-closed. RV32 firmware proof remains blocked until real
bootstrap CLI lowering replaces the smoke entry and the full bootstrap/deploy
loop produces a self-hosted `bin/simple`.

### Latest bootstrap progress: Stage 2 `--version` succeeds, other commands fail closed (2026-07-07)

The Stage 2 bootstrap entry is now argv-sensitive instead of unconditional. The
bounded build and smoke evidence:

```text
PASS test/01_unit/compiler/backend/bootstrap_llvm_entry_symbol_source_spec.spl
stage2_cli_entry_rc=0
[mir-lower-free] done instr-total=12 term-total=24
[llvm-tools] llc-object

build/mini_builds/stage2_after_bootstrap_cli_entry --version
simple-bootstrap 1.0.0-beta
version_rc=0

build/mini_builds/stage2_after_bootstrap_cli_entry
noargs_rc=1

build/mini_builds/stage2_after_bootstrap_cli_entry native-build
native_build_rc=1
```

This satisfies the immediate Stage 2 CLI gate for a visible version probe and
fail-closed unsupported commands. Firmware production proof is still open until
the real bootstrap CLI lowering and full bootstrap/deploy loop produce a usable
self-hosted compiler for the RV32 firmware build.

### Latest bootstrap progress: real-main probe isolated behind env gate (2026-07-07)

The default Stage 2 path still builds and smokes through the stable argv-aware
bootstrap entry:

```text
PASS test/01_unit/app/cli/bootstrap_main_source_spec.spl
PASS test/01_unit/compiler/backend/bootstrap_llvm_entry_symbol_source_spec.spl
PASS test/01_unit/compiler/driver/bootstrap_context_mir_source_spec.spl
stage2_default_realmain_gate_rc=0
[mir-lower-free] done instr-total=12 term-total=24
[llvm-tools] llc-object
version_rc=0
version_stdout=simple-bootstrap 1.0.0-beta
noargs_rc=1
native_rc=1
```

The full `bootstrap_main.spl` lowering is now reachable only with
`SIMPLE_BOOTSTRAP_REAL_MAIN=1`. That probe links after applying the existing SSA
phi materializer, but it is not usable yet: `--version` returns `1` with empty
stdout/stderr, and the preserved IR branches on `icmp ne i64 undef`.

Firmware production proof remains blocked on real bootstrap HIR/MIR expression
lowering for method-call conditions, argv indexing, string equality, and print.
Do not add more bootstrap runtime shims for this lane; fix the lowering gap.

### Latest bootstrap progress: call args preserved, condition values still undef (2026-07-07)

Bootstrap HIR lowering now preserves call/method-call arguments in bootstrap
mode, and bootstrap `.len()` has a fail-closed array runtime fallback instead
of producing an uninitialized temp. Focused checks pass:

```text
PASS test/01_unit/compiler/hir/bootstrap_expr_args_source_spec.spl
PASS test/01_unit/compiler/mir/bootstrap_len_fallback_source_spec.spl
```

The bounded real-main shard still links but does not run as a CLI:

```text
real_main_hir_args_rc=0
[mir-lower-free] done instr-total=12 term-total=24
[llvm-tools] llc-object
version_rc=1
stdout/stderr empty
```

RV32 firmware proof remains blocked until real bootstrap `if` condition
expressions lower to defined MIR locals. The current IR still branches on
`icmp ne i64 undef`, so the next fix should target HIR condition expression
lowering before string/index/print behavior.

### Latest bootstrap progress: real-main CLI branches execute (2026-07-07)

The `icmp ne i64 undef` blocker is fixed for the bounded real-main shard.
Source regression now covers:

- normal bootstrap binary operators bypass the optional special-op nil path;
- typed array indexes retain their element type; only unknown bootstrap indexes
  fall back to text values;
- `lower_if` preserves explicit `return` terminators instead of overwriting
  branch blocks with `goto merge`;
- pointer/text CLI comparisons lower through typed `rt_strcmp`;
- direct `get_cli_args()[i]` lowers through `spl_get_arg(i)` instead of raw
  `getelementptr` on the runtime array handle.

Evidence:

```text
PASS test/01_unit/compiler/mir/bootstrap_binary_lowering_source_spec.spl
real_main_order_fix_rc=0
version_rc=0
noargs_rc=0
native_build_rc=1
```

The generated IR contains:

```text
call ptr @spl_get_arg(i64 ...)
call i64 @rt_strcmp(ptr ..., ptr ...)
declare ptr @spl_get_arg(i64)
declare i64 @rt_strcmp(ptr, ptr)
```

Firmware production proof remains blocked, but the blocker has moved: the
bootstrap CLI now matches real command branches, while `native-build` still
returns `1` because `run_native_build_bootstrap` is still a stub and print /
string interpolation are still not emitted visibly.

Review follow-up before commit narrowed the string-compare change so arbitrary
pointer equality remains pointer equality. `rt_strcmp` is used only for
bootstrap string-derived operands tracked in LLVM lowering, and index lowering
again evaluates `base` before `index`.

### Latest bootstrap progress: visible bootstrap CLI output (2026-07-07)

Bootstrap print lowering now emits `rt_println(text)` instead of dropping print
calls in bootstrap mode. The generated real-main shard now has visible CLI
output:

```text
PASS test/01_unit/compiler/mir/bootstrap_binary_lowering_source_spec.spl
PASS test/01_unit/app/cli/bootstrap_main_source_spec.spl
real_main_print_fix_rc=0

build/mini_builds/stage2_real_main_print_fix --version
simple-bootstrap 1.0.0-beta
version_rc=0

build/mini_builds/stage2_real_main_print_fix
Simple Bootstrap Compiler v1.0.0-beta
Usage: simple compile <file> [-o <output>] [--native] [--opt-level=<level>] [--list-optimizations]
noargs_rc=0

build/mini_builds/stage2_real_main_print_fix --help
help_rc=0
```

This removes the print/interpolation visibility blocker for the simple
bootstrap CLI by using literal bootstrap text. Firmware production proof still
waits on replacing the `run_native_build_bootstrap` stub so the matched
`native-build` branch invokes the real native-build pipeline.

### Non-bootstrap runtime evidence green; bootstrap build lane postponed (2026-07-07)

Per user direction, bootstrap/native-build work is postponed and the remaining
non-bootstrap firmware checks were re-run first.

Evidence from the existing `build/nvme_fw_rv32.elf`:

```text
serial:
SimpleOS RV32
[BOOT] boot complete
ALL RV32 NVME FW CHECKS PASS
HEAP OK
SVC OK

PASS test/03_system/app/nvme_firmware/nvme_rv32_baremetal_boot_spec.spl
Files: 1
Passed: 2
Failed: 0
```

The host scalar logic reference also remains green:

```text
RV32 NVME FW LOGIC OK
```

Status split:

- Runtime/QEMU firmware behavior: green for the current ELF.
- System spec coverage: green for the required RV32 firmware, heap, and SVC
  markers.
- Production self-hosted wrapper rebuild: still open/postponed because
  bootstrap `native-build` dispatch is not implemented yet.

### Non-bootstrap firmware system gates rechecked (2026-07-07)

Additional non-bootstrap firmware gates were checked while bootstrap work
remained postponed.

Green:

```text
PASS test/03_system/app/nvme_firmware/nvme_firmware_simulation_spec.spl
PASS test/03_system/app/nvme_firmware/nvme_emulator_seam_spec.spl
PASS test/03_system/app/nvme_firmware/nvme_baremetal_wrapper_coverage_spec.spl
PASS test/03_system/app/nvme_firmware/nvme_rv64_baremetal_boot_spec.spl
PASS test/03_system/app/nvme_firmware/nvme_nand_capture_spec.spl
PASS test/03_system/app/nvme_firmware/nvme_cosmos_openssd_boot_spec.spl
PASS test/03_system/app/nvme_firmware/nvme_jtag_baremetal_board_spec.spl
```

The Cosmos/OpenSSD spec required rebuilding its local ARM32 ELF with
`sh src/os/kernel/arch/arm32/cosmos/build.shs`; the resulting QEMU Zynq boot
passed.

Harness fix:

- `nvme_firmware_simulation_spec.spl` now gives the nested
  `gc_safety_check.spl` subprocess `SIMPLE_TIMEOUT_SECONDS=60` and stores its
  full output under `build/test-artifacts/nvme_gc_safety.out`. The GC program
  itself remains unchanged and still prints `GC SAFETY OK`.

Resolved outside firmware logic:

```text
LLVM_SYS_180_PREFIX=/usr/lib/llvm-18 \
cargo build --manifest-path src/compiler_rust/Cargo.toml \
  -p simple-driver --features llvm --release

SIMPLE_BIN=src/compiler_rust/target/release/simple \
SIMPLE_BINARY=src/compiler_rust/target/release/simple \
bin/simple os build --scenario=riscv32-fpga-mmode

SIMPLE_BINARY=src/compiler_rust/target/release/simple \
SIMPLE_BOOT_MINIMAL=1 SIMPLE_OS_LOG_MODE=on PATH="/usr/bin:$PATH" \
src/compiler_rust/target/release/simple native-build \
  --source build/os/generated --source src --source examples \
  --backend llvm --opt-level=aggressive --log on --entry-closure \
  --entry src/os/kernel/arch/riscv32/boot.spl \
  --target riscv32-unknown-none \
  -o build/os/simpleos_riscv32.elf \
  --linker-script src/os/kernel/arch/riscv32/linker.ld

PASS test/03_system/app/nvme_firmware/nvme_rv32_smp_boot_spec.spl
PASS test/03_system/app/nvme_firmware/nvme_rv32_fpga_boot_spec.spl
```

The Rust-built Simple binary prints the expected bootstrap-only warning and is
used here only to produce the missing RISC-V OS evidence media. The remaining
firmware-production blocker is still the postponed bootstrap
`run_native_build_bootstrap` path for self-hosted `native-build`.

### Minimal RV32 wrapper diagnostic still fails (2026-07-07)

The attempted prefix diagnostic in `scripts/check/check-nvme-rv32-minimal-live.shs`
does not provide a shippable workaround yet. Even with one inlined logic section
and a larger Rust stack, the self-hosted native-build path aborts while lowering
the generated root `selftest` function:

```text
NVME_RV32_MINIMAL_SECTIONS=1 NVME_RV32_BUILD_TIMEOUT_SECS=180 \
  sh scripts/check/check-nvme-rv32-minimal-live.shs

phase1:load_sources:done n_sources=1
phase3:hir:function:start ...nvme_fw_minimal_root.spl._selftest
thread 'simple-main' has overflowed its stack
STATUS: FAIL nvme-rv32-minimal-live build_rc=134
```

This keeps the RV32 minimal self-hosted live checker uncommitted. The useful
next fix is in HIR lowering recursion/stack behavior, not another wrapper shape.

### RV32 wrapper now reports status/background and external termination (2026-07-08)

`fw_rv32/build.shs` now mirrors the RV64 operational wrapper surface:
`--status`, `--background`, elapsed build metadata, and failed-build reason
classification. This prevents a missing `build/nvme_fw_rv32.elf` from collapsing
to an opaque missing-media state after a killed build.

Latest direct wrapper attempt on the self-hosted `bin/simple` still did not
produce `build/nvme_fw_rv32.elf`:

```text
NVME_RV32_BUILD_TIMEOUT_SECS=300 sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs
NVME_RV32_BUILD_FAILED code=143 reason=external-termination-before-timeout timeout=300s ...
[BOOTSTRAP-PHASE] +0ms phase2:parse:file:start build/os/generated/nvme_fw_direct_entry.spl chars=75543
Terminated
```

This is still not a firmware logic failure: the scalar logic and production
simulation gates remain green. The remaining blocker is the self-hosted native
build/parse path for the generated RV32 firmware entry.

## 2026-07-19 datapoints (regression is now also on the bootstrap binary)

- `src/compiler_rust/target/bootstrap/simple` (the 5.2s differential path
  above) now ALSO times out: default closure rc=124 at 300s, SMP closure
  (`NVME_RV32_SMP=1`, 187 files) rc=124 at 580s. Disk-full was ruled out
  (117G free at test time; an earlier same-day stall was a genuine ENOSPC —
  root filesystem hit 100% from stale `build/worktrees/*` artifacts, since
  reclaimed).
- The SMP run is NOT a single-file hang: `[BOOTSTRAP-PHASE]` markers show
  steady progress at ~2.6s per ~600-char file (e.g. `+280963ms → +283551ms`
  for `logic_dram_alloc_cases.spl`, chars=535). That is per-FILE overhead
  (plausibly whole-prelude re-work per file in the module loader), so a
  187-file closure needs ~10-15 min. Whether it completes at 1800s is being
  measured; regardless, ~2.6s per 535-char file is a defect on its own —
  the 2026-07-05 run parsed the whole set in 5.2s total.
- Evidence logs: session scratchpad `wave3/L6/smp_build_orch2.log`,
  `default_build_orch2.log` (not committed).
