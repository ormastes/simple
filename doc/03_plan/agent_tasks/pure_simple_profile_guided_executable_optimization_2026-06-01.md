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

No implementation gap remains for this plan. If resumed for release/sync, run
the focused gates below and commit only the scoped files.

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
durable sidecar metadata.

Deliverables:
- native function/block/edge counter ABI;
- counter emission behind explicit profile build flag;
- `.sprof` writer hook;
- call-path summary with bounded memory.

Exit gates:
- instrumentation overhead under target budget;
- disabled counters compile out or remain cold;
- interpreter/JIT and native counter names share stable identity.

## Phase 3: Pure-Simple Executable Optimizer

Status: first implementation slice exists at
`src/app/optimize/executable_layout.spl` with layout steps, transform
eligibility, external-BOLT rejection, and manifest-entry validation. Contract
coverage exists at
`test/system/app/optimize/feature/pure_simple_executable_layout_spec.spl`.
The file-level profile-layout bridge consumes executable metadata plus `.sprof`
input and writes a deterministic layout manifest.

Deliverables:
- layout planner over Simple settlement/native metadata;
- hot function clustering and hot block fallthrough ordering;
- cold section candidate marking;
- reproducibility manifest with symbol/relocation mapping.

Exit gates:
- optimized executable passes semantic smoke;
- before/after startup/runtime/size report exists;
- no external BOLT dependency.

## Phase 4: Bare-Metal Breakpoint Counter Capsule

Status: first implementation slice exists at
`src/os/baremetal/profile/breakpoint_counter.spl` with breakpoint state
transitions, over-budget auto-disarm, sampled-only fallback, cleanup-event
coverage, and patch-ledger validation. Contract coverage exists at
`test/system/os/baremetal/feature/breakpoint_counter_profile_spec.spl`. The
architecture patch profile contract now covers x86/i386/x86_64 INT3,
ARM32 BKPT, Thumb/Thumb2 BKPT, AArch64 BRK, RV32/RV64 EBREAK, and compressed
RV32C/RV64C EBREAK. Actual QEMU-backed target memory/trap-handler adapters are
the next implementation slice.

Deliverables:
- software-breakpoint site table;
- patch/trap/count/restore/rearm state machine;
- architecture-specific trap opcode, patch-byte, PC-advance, alignment, and
  icache policy matrix for x86, ARM/Thumb/AArch64, and RISC-V/RVC;
- over-budget auto-disarm;
- timer/sampling fallback;
- QEMU evidence path and hardware-unavailable reporting.

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
SIMPLE_LIB=src src/compiler_rust/target/bootstrap/simple test test/unit/compiler/interpreter/tiered_jit_hotspot_spec.spl --mode=interpreter --clean
find doc/06_spec -name '*_spec.spl' | wc -l
git diff --check
```

Native/bare-metal slices add QEMU or native executable smoke gates before any
speedup claim.
