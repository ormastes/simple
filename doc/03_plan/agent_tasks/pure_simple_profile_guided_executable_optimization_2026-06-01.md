# Pure Simple Profile-Guided Executable Optimization Agent Plan

Date: 2026-06-01

## Restart Checkpoint: 2026-06-01 09:55 UTC

Remote `origin/main` is at:

```text
4116932bdf feat: consume loaded sprof records in layout bridge
```

Important local state:
- The worktree contains many unrelated user/agent edits outside this feature.
  Do not reset or clean them.
- The profile-optimization feature files are clean relative to `HEAD` at this
  checkpoint.
- A previous `jj log` attempt saw `.git/index.lock`; if it recurs, first check
  for live `git`/`jj`/`gh` processes with `ps`/`fuser` before removing any stale
  lock.
- Use `env -u GITHUB_TOKEN jj git push --bookmark main` for push. The process
  environment had an invalid `GITHUB_TOKEN`, but `gh auth setup-git` configured
  a valid stored GitHub token.

## Restart Checkpoint: 2026-06-01 10:20 UTC

Command-level native profile-counter smoke is now proven with the rebuilt
release driver:

```bash
RUST_MIN_STACK=67108864 SIMPLE_LIB=src src/compiler_rust/target/release/simple run \
  src/app/compile/llvm_direct.spl \
  test/unit/compiler/backend/_codegen_smoke.spl \
  /tmp/simple_pgo_smoke \
  --simple-profile-counters --verbose
```

Evidence:

```text
exit=0
binary_exists=yes
metadata_exists=yes
metadata_has_counter=yes
```

The durable sidecar path is `/tmp/simple_pgo_smoke.simple-profile-counters`,
and it contains `__simple_profile_counter_*_function_entry` rows for the small
native compile fixture.

Additional implementation in this checkpoint:
- renamed compiler effect self-test entrypoints away from `main`;
- changed Rust import flattening to drop imported `main` functions;
- made `llvm_direct.spl` parse direct `simple run` args via `get_cli_args`;
- made `llvm_direct.spl` generate a local textual C fixture before applying
  Simple-owned profile counters, avoiding the currently broken
  `simple compile --backend=c` path that writes SMF bytes;
- fixed the native profile-counter metadata prelude brace interpolation so
  generated C uses an initializer list.

Pushed implementation now includes:
- `src/app/optimize/sprof_loader.spl`
  - persistent `.sprof` text/file loader;
  - typed `SprofCounterRecord` materialization in `SprofLoadedProfile`;
  - profile writer;
  - native metadata plus final counter snapshot importer;
  - reloadable `.sprof` file write from native counter snapshots.
- `src/app/compile/native_profile_counter.spl`
  - native counter ABI helpers;
  - C-source function-entry instrumentation for `--simple-profile-counters`;
  - runtime extraction from metadata plus final counts into `.sprof` lines.
- `src/app/optimize/profile_layout_cli.spl`
  - settlement/native metadata parser;
  - profile-layout bridge that consumes loaded `.sprof` records;
  - optimizer CLI bridge through `simple optimize --layout-plan`.
- `src/app/optimize/executable_layout.spl`
  - Pure-Simple BOLT-like layout planner without external BOLT;
  - hot/cold placement and deterministic manifest text.
- `src/os/baremetal/profile/breakpoint_counter.spl`
  - software-breakpoint patch/restore/rearm memory model;
  - icache flush evidence;
  - cleanup ledger and sampled-only fallback contracts.

Verified before this restart note:

```bash
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple check \
  src/app/optimize/sprof_loader.spl \
  src/app/optimize/profile_layout_cli.spl \
  test/system/app/optimize/feature/sprof_loader_spec.spl \
  test/system/app/optimize/feature/profile_layout_cli_spec.spl

SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple test \
  test/system/app/optimize/feature/sprof_loader_spec.spl --fail-fast

SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple test \
  test/system/app/optimize/feature/profile_layout_cli_spec.spl --fail-fast

SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple test \
  test/system/app/compile/feature/native_profile_counter_spec.spl --fail-fast

SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple test \
  test/system/app/optimize/feature/pure_simple_executable_layout_spec.spl --fail-fast

SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple test \
  test/system/os/baremetal/feature/breakpoint_counter_profile_spec.spl --fail-fast

find doc/06_spec -name '*_spec.spl' | wc -l
```

Known verification caveat:
- Running some SPipe specs may invoke doc generation and currently expose an
  unrelated parser/docgen failure in
  `src/compiler/10.frontend/flat_ast_bridge_part2.spl`. That is tracked in
  `doc/08_tracking/bug/spipe_docgen_flat_ast_bridge_parse_error_2026-06-01.md`
  and should not be confused with the profile optimization slice.

## Restart Checkpoint: 2026-06-01 10:05 UTC

Additional implementation completed:
- `src/app/compile/native_profile_counter.spl`
  - added `native_profile_counter_metadata_path(output_file)` so native
    profile-counter metadata has a durable `<output>.simple-profile-counters`
    location instead of being tied to the temporary generated C file.
- `src/app/compile/llvm_direct.spl`
  - writes `--simple-profile-counters` metadata to the durable output sidecar
    path and fails the compile if metadata cannot be written.
- `src/app/optimize/profile_layout_cli.spl`
  - added `profile_layout_write_manifest_file(...)` for the file-level
    `metadata/.sprof -> --layout-plan -> manifest` bridge.
- `src/app/optimize/main.spl`
  - routes `simple optimize --layout-plan` through the file-level bridge.
- `test/system/app/compile/feature/native_profile_counter_spec.spl`
  - covers durable sidecar metadata path.
- `test/system/app/optimize/feature/profile_layout_cli_spec.spl`
  - covers end-to-end native metadata plus observed counts written as `.sprof`
    and consumed into a layout manifest file.
- `src/compiler/00.common/effects_solver.spl`
  - fixed stale `EffectTag.Sync`/`EffectTag.Async` references to the canonical
    `EffectTag.PureTag`/`EffectTag.SuspendingTag` names after the actual native
    compile smoke exposed the enum drift.

Verification after this slice:

```bash
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple check \
  src/compiler/00.common/effects_solver.spl \
  src/app/compile/native_profile_counter.spl \
  src/app/compile/llvm_direct.spl \
  src/app/optimize/profile_layout_cli.spl \
  src/app/optimize/main.spl

SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple test \
  test/system/app/optimize/feature/sprof_loader_spec.spl --fail-fast
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple test \
  test/system/app/optimize/feature/profile_layout_cli_spec.spl --fail-fast
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple test \
  test/system/app/optimize/feature/pure_simple_executable_layout_spec.spl --fail-fast
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple test \
  test/system/app/compile/feature/native_profile_counter_spec.spl --fail-fast
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple test \
  test/system/os/baremetal/feature/breakpoint_counter_profile_spec.spl --fail-fast

git diff --check -- \
  src/app/compile/native_profile_counter.spl \
  src/app/compile/llvm_direct.spl \
  src/app/compile/__init__.spl \
  src/app/optimize/profile_layout_cli.spl \
  src/app/optimize/main.spl \
  test/system/app/compile/feature/native_profile_counter_spec.spl \
  test/system/app/optimize/feature/profile_layout_cli_spec.spl

find doc/06_spec -name '*_spec.spl' | wc -l
```

All focused checks/specs above passed, `git diff --check` was clean, and the
`doc/06_spec` executable-spec count was `0`.

Completion-audit gap closure at 2026-06-01 10:20 UTC:
- Command-level native smoke is proven. `llvm_direct.spl` now reaches its own
  entrypoint under `simple run`, compiles a small textual C fixture with clang,
  writes the native output, and writes durable
  `<output>.simple-profile-counters` metadata.
- Evidence command:

```bash
RUST_MIN_STACK=67108864 SIMPLE_LIB=src src/compiler_rust/target/release/simple run \
  src/app/compile/llvm_direct.spl \
  test/unit/compiler/backend/_codegen_smoke.spl \
  /tmp/simple_pgo_smoke \
  --simple-profile-counters --verbose
```

- Observed result: `exit=0`, `binary=yes`, `metadata=yes`,
  `metadata_has_counter=yes`.

## Completion Audit Result

All explicit audit bullets are satisfied by current evidence:
- `--simple-profile-counters` command smoke writes a native binary and durable
  sidecar metadata with `__simple_profile_counter_*_function_entry` records.
- Native metadata plus observed counts writes a reloadable `.sprof` through
  `sprof_write_native_counter_profile_file`, covered by
  `sprof_loader_spec.spl`.
- The optimize layout file bridge consumes `.sprof` plus executable metadata
  and writes a layout manifest, covered by `profile_layout_cli_spec.spl`.
- Bare-metal invalid address, opcode mismatch, missing icache flush, cleanup,
  and rearm behavior are covered by `breakpoint_counter_profile_spec.spl`.
- External BOLT invocation is rejected by `executable_layout.spl` and covered by
  `pure_simple_executable_layout_spec.spl`.

## Next Restart Plan

The completion audit above was superseded by the native-ownership correction:
Rust is seed/runtime infrastructure only. The real optimizer implementation
must stay in Simple and generated C. The next concrete gap was consuming the
generated-C section map in the Simple native compile path.

## Restart Checkpoint: 2026-06-01 Native Section Map Consumption

Implemented in the current slice:
- `src/app/compile/native_layout_section_map.spl`
  - parses `SIMPLE_LAYOUT_SECTION_*` macros emitted by the optimizer;
  - rejects empty, malformed, unsafe, or unused section maps;
  - prefixes matching generated-C function definitions with section macros.
- `src/app/compile/llvm_direct.spl`
  - adds `--simple-layout-section-map=PATH`;
  - reads the generated-C section map;
  - applies it after optional Simple native profile-counter instrumentation;
  - fails closed on map diagnostics before invoking the C compiler.
- `test/system/app/compile/feature/native_layout_section_map_spec.spl`
  - covers parsing, fail-closed validation, disabled behavior, and function
    mapping.

This is a Simple/C implementation slice, not a Rust linker seed change.

Remaining larger gaps:
- actual QEMU/live target runners for x86/i386/x86_64, ARM/Thumb/AArch64, and
  RISC-V/RVC breakpoint evidence;
- measured before/after executable performance evidence for the full
  profile-counter -> `.sprof` -> layout-map -> native build flow.

## Restart Checkpoint: 2026-06-01 Native Symbol-Order Evidence

Implemented in the current slice:
- `src/app/optimize/profile_layout_native_smoke.spl`
  - writes the Simple-generated `native-symbol-order` artifact beside the
    generated-C section map;
  - maps the Simple symbols to the generated C++ static symbol spelling used by
    this native lane;
  - links the optimized smoke binary with `lld` and
    `--symbol-ordering-file=<generated-order>`;
  - records `nm -an` evidence for the final optimized binary;
  - records that the non-profile baseline binary has zero
    `__simple_profile*` counter symbols.
- `src/app/optimize/profile_layout_cli.spl`
  - extends `ProfileLayoutNativeEvidence` with final native symbol-order text,
    a verified order boolean, and the non-profile counter-symbol count;
  - rejects native evidence when the optimized binary does not prove
    `dispatch -> parse -> rare` order or when non-profile builds contain
    counter symbols.
- `test/system/app/optimize/feature/profile_layout_native_smoke_spec.spl`
  - now asserts final optimized native symbol order and zero counter leakage in
    the non-profile build.
- `test/system/app/optimize/feature/profile_layout_cli_spec.spl`
  - covers the stricter evidence contract and the missing-order rejection path.

This closes the prior smoke-only weakness where the generated-C section map was
applied but the final native binary order was not inspected.

Remaining larger gaps:
- measured before/after executable performance evidence for the full
  profile-counter -> `.sprof` -> layout-map -> native build flow.

## Restart Checkpoint: 2026-06-01 QEMU Breakpoint Runner Bridge

Implemented in the current slice:
- `src/os/baremetal/profile/breakpoint_counter_qemu.spl`
  - maps x86/i386/x86_64, ARM/Thumb/AArch64, and RISC-V/RVC targets to QEMU
    binaries, machines, CPUs, and `-kernel` serial command args;
  - exposes a host QEMU binary probe;
  - runs a supplied image under QEMU when both the image and binary exist;
  - extracts `simple-breakpoint-evidence;...` serial lines and feeds them into
    the existing fail-closed evidence validator;
  - reports `unsupported_arch`, `missing_image`, `qemu_unavailable`, or
    `missing_serial_evidence` instead of claiming target proof.
- `test/system/os/baremetal/feature/breakpoint_counter_target_adapter_spec.spl`
  - covers runner plans, command fragments, serial evidence parsing, and
    fail-closed missing-proof behavior.

Remaining larger gaps:
- build or stage the actual per-arch breakpoint probe images that emit serial
  evidence lines for x86/i386/x86_64, ARM/Thumb/AArch64, and RISC-V/RVC;
- run those images under QEMU and capture live patch/trap/count/restore/rearm/
  cleanup/icache evidence;
- measured before/after executable performance evidence for the full
  profile-counter -> `.sprof` -> layout-map -> native build flow.

## Restart Checkpoint: 2026-06-01 Breakpoint Probe Image Contract

Implemented in the current slice:
- `src/os/baremetal/profile/breakpoint_counter_probe_image.spl`
  - defines the supported probe-image arch matrix: `i386`, `x86_64`,
    `arm32`, `thumb`, `aarch64`, `riscv32`, `riscv32c`, `riscv64`,
    `riscv64c`;
  - maps each arch to deterministic source/output paths, linker script,
    compiler, serial driver, QEMU binary, and build arguments;
  - defines the required serial evidence fields consumed by the QEMU evidence
    parser;
  - generates freestanding C probe source text for each supported arch with
    original instruction bytes, trap bytes, restore/rearm operations, icache
    flush calls, arch-specific serial writes, and parser-valid serial evidence;
  - exposes a Simple staging function that writes
    `build/baremetal/breakpoint_probe/<arch>/breakpoint_probe.c`;
  - provides `src/os/baremetal/profile/breakpoint_counter_probe_stage.spl`,
    which staged all 9 probe sources on this host with
    `status=written;requested=9;written=9;failed=0`;
  - now generates probe-specific linker scripts and boot entry shims instead
    of reusing full SimpleOS kernel linker scripts;
  - fails closed with `missing_probe_source`, `compiler_unavailable`, or
    `missing_probe_elf` until real build artifacts exist.
- `test/system/os/baremetal/feature/breakpoint_counter_probe_image_spec.spl`
  - covers the arch matrix, build/run readiness statuses, compiler arguments,
    serial evidence contract, generated source artifact content, and
    idempotent all-arch staging.
- `src/os/baremetal/profile/breakpoint_counter_qemu.spl`
  - now adds `-monitor none` when serial is bound to stdio, avoiding QEMU's
    monitor/serial stdio conflict;
  - distinguishes RISC-V 32-bit QEMU CPU planning (`rv32`) from RV64 (`rv64`).

Build evidence from this host:
- Built: `i386`, `x86_64` as the x86-family 32-bit multiboot probe under the
  x86_64 QEMU target, `arm32`, `thumb`, `aarch64`, `riscv32`, `riscv32c`,
  `riscv64`, `riscv64c`. ARM-family probes use host Clang cross targets rather
  than missing GCC cross toolchains.
- Live QEMU serial evidence captured: `i386`, x86-family `x86_64`, `arm32`,
  `thumb`, `aarch64`, `riscv32`, `riscv32c`, `riscv64`, and `riscv64c`.
  x86 probes include a Xen PVH `XEN_ELFNOTE_PHYS32_ENTRY` note so QEMU
  `-kernel` enters `_entry32`; Thumb probes enter in ARM state and branch to
  the Thumb-marked `probe_main`; RV32/RVC32 direct-boot with `-bios none` at
  `0x80000000`, avoiding the missing host OpenSBI RV32 firmware.

Remaining larger gaps:
- measured before/after executable performance evidence for the full
  profile-counter -> `.sprof` -> layout-map -> native build flow.

## Restart Checkpoint: 2026-06-01 Native Counter Insertion

Implemented in the current slice:
- `src/app/compile/native_profile_counter.spl`
  - derives generated-C counter slots for `function_entry`, entry
    `basic_block`, return `edge`, and direct-call `call_path` sites;
  - inserts all four counter classes behind the explicit profile build path;
  - keeps disabled/non-profile builds clean through the existing build audit.
- `test/system/app/compile/feature/native_profile_counter_spec.spl`
  - covers full C slot derivation;
  - verifies emitted C contains all planned counter increments and metadata.

Remaining larger gaps:
- actual QEMU/live target runners for x86/i386/x86_64, ARM/Thumb/AArch64, and
  RISC-V/RVC breakpoint evidence;
- measured before/after executable performance evidence for the full
  profile-counter -> `.sprof` -> layout-map -> native build flow.

If resumed for release/sync, run the focused gates below and commit only the
scoped files.

Final requirement artifacts now exist at:
- `doc/02_requirements/feature/pure_simple_profile_guided_executable_optimization_2026-06-01.md`
- `doc/02_requirements/nfr/pure_simple_profile_guided_executable_optimization_2026-06-01.md`

Current verification evidence is summarized in
`doc/09_report/pure_simple_profile_guided_executable_optimization_2026-06-01.md`.

1. Re-check feature cleanliness without touching unrelated dirty files:

```bash
git status --short -- \
  src/app/optimize/sprof_loader.spl \
  src/app/optimize/profile_layout_cli.spl \
  src/app/optimize/executable_layout.spl \
  src/app/compile/native_profile_counter.spl \
  src/app/compile/llvm_direct.spl \
  src/os/baremetal/profile/breakpoint_counter.spl \
  test/system/app/optimize/feature/sprof_loader_spec.spl \
  test/system/app/optimize/feature/profile_layout_cli_spec.spl \
  test/system/app/optimize/feature/pure_simple_executable_layout_spec.spl \
  test/system/app/compile/feature/native_profile_counter_spec.spl \
  test/system/os/baremetal/feature/breakpoint_counter_profile_spec.spl
```

2. Completion audit before marking done:
   - prove `--simple-profile-counters` generates instrumented C and sidecar
     metadata from a small native compile fixture;
   - prove native metadata plus observed counts writes a reloadable `.sprof`;
   - prove `simple optimize --layout-plan` consumes that `.sprof` plus metadata
     and writes a layout manifest;
   - prove bare-metal patching covers invalid address, opcode mismatch, missing
     icache flush, cleanup, and rearm behavior;
   - prove no external BOLT invocation exists in the optimize path.

3. If completion audit finds gaps, prioritize these implementation slices:
   - add an end-to-end optimize app spec for
     `metadata -> .sprof -> --layout-plan -> manifest`;
   - add a small native compile smoke for `--simple-profile-counters` that
     asserts generated C contains `__simple_profile_counters[...] += 1u` and
     writes `.simple-profile-counters` metadata;
   - add a CLI/helper around native counter snapshot import if operators need a
     command-level entrypoint instead of calling `sprof_write_native_counter_profile_file`;
   - extend bare-metal patch evidence with one failure-path spec for
     `memory_original_mismatch` or `patch_out_of_bounds` if missing.

4. Re-run focused gates after any edits:

```bash
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple check \
  src/app/optimize/sprof_loader.spl \
  src/app/optimize/profile_layout_cli.spl \
  src/app/optimize/executable_layout.spl \
  src/app/compile/native_profile_counter.spl \
  src/app/compile/llvm_direct.spl \
  src/os/baremetal/profile/breakpoint_counter.spl

SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple test \
  test/system/app/optimize/feature/sprof_loader_spec.spl --fail-fast
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple test \
  test/system/app/optimize/feature/profile_layout_cli_spec.spl --fail-fast
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple test \
  test/system/app/compile/feature/native_profile_counter_spec.spl --fail-fast
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple test \
  test/system/app/optimize/feature/pure_simple_executable_layout_spec.spl --fail-fast
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple test \
  test/system/os/baremetal/feature/breakpoint_counter_profile_spec.spl --fail-fast

git diff --check -- <touched feature files>
find doc/06_spec -name '*_spec.spl' | wc -l
```

5. Commit only scoped feature/doc files with path-limited `jj commit`, then push:

```bash
jj commit -m "feat: <profile optimization slice>" <scoped files>
env -u GITHUB_TOKEN jj git fetch
jj rebase -d main@origin
jj bookmark set main -r @-
env -u GITHUB_TOKEN jj git push --bookmark main
```

## Phase 0: Stabilize Current State

Status: completion audit passed on 2026-06-01. Scoped feature work remains
dirty in the worktree alongside unrelated pre-existing edits, so any commit
should still be path-limited.

Evidence:
- `llvm_direct.spl --simple-profile-counters` emits native binaries plus
  durable `.simple-profile-counters` sidecars for minimal and `_codegen_smoke`
  fixtures.
- Observed native counter snapshots write reloadable `.sprof` files, and
  `src/app/optimize/main.spl --layout-plan` consumes the `.sprof` plus manifest
  input to produce a deterministic hot/cold layout manifest.
- Focused SPipe specs passed: sprof loader 23, native profile counters 30,
  profile layout CLI 8, executable layout 15, bare-metal breakpoint profile 22.
- Required compiler/lib/MCP gates passed, `git diff --check` passed,
  placeholder-test scan found no matches, and `find doc/06_spec -name
  '*_spec.spl' | wc -l` returned `0`.

## Phase 1: Persistent Profile Loader

Status: first implementation slice exists at `src/app/optimize/sprof_loader.spl`
with persisted profile text loading, file-load wrapper, validation status,
counter merge summaries, bounded diagnostics, and hot-path policy helpers.
Contract coverage exists at
`test/system/app/optimize/feature/sprof_loader_spec.spl`. Native metadata plus
observed counter snapshots now write reloadable `.sprof` files through the
profile writer.

Deliverables:
- `.sprof` reader/validator in optimize/profile common surface;
- merge summary keyed by module identity, workload label, schema version;
- opt-in load path for optimize app and startup loader;
- diagnostics for corrupt/stale/incompatible records.

Exit gates:
- startup load overhead measured under 5%;
- no hot-path reread/shell/full-tree scan;
- tests for corrupt, stale, incompatible, and exact records.

## Phase 2: Native Counter Feature

Status: first implementation slice exists at
`src/app/compile/native_profile_counter.spl` with native counter kinds,
explicit profile-build enablement, stable identity checks, and bounded call-path
policy. Contract coverage exists at
`test/system/app/compile/feature/native_profile_counter_spec.spl`. Command-level
`llvm_direct.spl --simple-profile-counters` smoke now emits a native binary and
durable sidecar metadata. The native counter helper now also parses runtime
counter snapshots, rejects malformed or incomplete readback, and creates a
write-gated `.sprof` import plan from metadata plus final counter values.
`llvm_direct.spl` now runs the same Simple-owned counter artifact audit in the
native compile lane and fails normal native builds if generated C contains
profile-counter symbols, increments, or metadata without
`--simple-profile-counters`.

Deliverables:
- native function/block/edge counter ABI;
- counter emission behind explicit profile build flag;
- compile-path audit proving normal native builds do not add counter artifacts;
- runtime snapshot readback parser and `.sprof` import plan;
- call-path summary with bounded memory.

Exit gates:
- instrumentation overhead under target budget;
- disabled counters compile out or remain cold;
- interpreter/JIT and native counter names share stable identity;
- executable runner emits the snapshot text consumed by the import plan.

## Phase 3: Pure-Simple Executable Optimizer

Status: first implementation slice exists at
`src/app/optimize/executable_layout.spl` with layout steps, transform
eligibility, external-BOLT rejection, and manifest-entry validation. Contract
coverage exists at
`test/system/app/optimize/feature/pure_simple_executable_layout_spec.spl`.
The file-level profile-layout bridge consumes executable metadata plus `.sprof`
input and writes a deterministic layout manifest. The bridge now also writes
Simple-owned native symbol order files and generated-C section map headers for
the same hot/cold plan, so the BOLT-like path produces consumable Simple/C
artifacts without Rust seed linker changes or external BOLT. It also now has a
checked native evidence report that ties `.sprof` input, manifest generation,
section-map application to generated C, final native symbol order, measured
before/after runtime, binary size deltas, and non-profile counter cleanliness
into one fail-closed result. A live native smoke now exists at
`test/system/app/optimize/feature/profile_layout_native_smoke_spec.spl` and
`doc/09_report/profile_layout_native_smoke_evidence_2026-06-01.md`; it builds
baseline and section-mapped native binaries from generated C and records runtime
and size evidence.

The representative full-flow evidence path now compiles an instrumented
generated-C workload, runs it with `SIMPLE_PROFILE_COUNTER_SNAPSHOT`, imports
the snapshot plus metadata into `.sprof`, emits the layout map and native symbol
order from that `.sprof`, rebuilds the optimized binary, verifies the final
`nm -an` order, and measures before/after native execution.

Deliverables:
- layout planner over Simple settlement/native metadata;
- hot function clustering and hot block fallthrough ordering;
- cold section candidate marking;
- reproducibility manifest with symbol/relocation mapping;
- native symbol order and generated-C section map artifacts.
- checked before/after evidence report over measured native runtime and size.
- live generated-C native smoke for the `profile counters -> .sprof -> section
  map -> rebuild -> runtime/size evidence` path.

Exit gates:
- optimized executable passes semantic smoke;
- representative before/after startup/runtime/size report exists;
- no external BOLT dependency.

## Phase 4: Bare-Metal Breakpoint Counter Capsule

Status: first implementation slice exists at
`src/os/baremetal/profile/breakpoint_counter.spl` with breakpoint state
transitions, over-budget auto-disarm, sampled-only fallback, cleanup-event
coverage, and patch-ledger validation. Contract coverage exists at
`test/system/os/baremetal/feature/breakpoint_counter_profile_spec.spl`. The
architecture patch profile contract now covers x86/i386/x86_64 INT3,
ARM32 BKPT, Thumb/Thumb2 BKPT, AArch64 BRK, RV32/RV64 EBREAK, and compressed
RV32C/RV64C EBREAK. Target adapter contracts now exist in
`breakpoint_counter_x86.spl`, `breakpoint_counter_arm.spl`,
`breakpoint_counter_riscv.spl`, and `breakpoint_counter_qemu.spl` for
trap-frame PC normalization and fail-closed QEMU evidence validation. Actual
QEMU runner integration that produces the evidence lines remains the next
implementation slice.

Deliverables:
- software-breakpoint site table;
- patch/trap/count/restore/rearm state machine;
- architecture-specific trap opcode, patch-byte, PC-advance, alignment, and
  icache policy matrix for x86, ARM/Thumb/AArch64, and RISC-V/RVC;
- over-budget auto-disarm;
- timer/sampling fallback;
- QEMU evidence path and hardware-unavailable reporting.
- target adapter resume plans for x86, ARM/Thumb/AArch64, and RISC-V/RVC;
- QEMU evidence normalization with arch, command, address, bytes, hits,
  latency, restore, rearm, cleanup, icache, and sampled-only fields.

Exit gates:
- breakpoints are removed before release execution;
- panic/watchdog cleanup restores patched code;
- hot loop sites transition to sampled-only after calibration.
- QEMU-backed specs prove real target patch, trap, count, restore,
  PC-advance/single-step, rearm, and cleanup for at least one x86, one ARM, and
  one RISC-V target before claiming target-backed support.

## Phase 5: Cross-Mode Verification

Commands to design/run per slice:

```bash
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple check src/app/optimize
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple check src/app/compile
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple check test/system/app/optimize/feature/sprof_loader_spec.spl test/system/app/compile/feature/native_profile_counter_spec.spl test/system/app/optimize/feature/pure_simple_executable_layout_spec.spl test/system/os/baremetal/feature/breakpoint_counter_profile_spec.spl
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple test test/system/os/baremetal/feature/breakpoint_counter_target_adapter_spec.spl --fail-fast
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple test test/unit/compiler/interpreter/tiered_jit_hotspot_spec.spl --mode=interpreter --clean
find doc/06_spec -name '*_spec.spl' | wc -l
git diff --check
```

Native/bare-metal slices add QEMU or native executable smoke gates before any
speedup claim.
