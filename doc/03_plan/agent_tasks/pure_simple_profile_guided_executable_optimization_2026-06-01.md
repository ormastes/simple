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

## Next Restart Plan

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

- Finish or isolate unrelated dirty NVMe/runtime/compiler edits before
  implementation commits.
- Keep planning docs separate from code slices.
- Re-run `git diff --check` and `find doc/06_spec -name '*_spec.spl' | wc -l`.

## Phase 1: Persistent Profile Loader

Status: first implementation slice exists at `src/app/optimize/sprof_loader.spl`
with persisted profile text loading, file-load wrapper, validation status,
counter merge summaries, bounded diagnostics, and hot-path policy helpers.
Contract coverage exists at
`test/system/app/optimize/feature/sprof_loader_spec.spl`. Binary `.sprof`
container parsing, writer integration, and startup-loader wiring remain future
work.

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
`test/system/app/compile/feature/native_profile_counter_spec.spl`. Actual
native code emission and `.sprof` writer flushing remain future work.

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
Actual settlement/native artifact rewriting remains future work.

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
`test/system/os/baremetal/feature/breakpoint_counter_profile_spec.spl`. Actual
architecture-specific instruction patch/trap/restore integration remains future
work.

Deliverables:
- software-breakpoint site table;
- patch/trap/count/restore/rearm state machine;
- over-budget auto-disarm;
- timer/sampling fallback;
- QEMU evidence path and hardware-unavailable reporting.

Exit gates:
- breakpoints are removed before release execution;
- panic/watchdog cleanup restores patched code;
- hot loop sites transition to sampled-only after calibration.

## Phase 5: Cross-Mode Verification

Commands to design/run per slice:

```bash
SIMPLE_LIB=src bin/simple check src/app/optimize
SIMPLE_LIB=src bin/simple check src/app/compile
SIMPLE_LIB=src bin/simple check test/system/app/optimize/feature/sprof_loader_spec.spl test/system/app/compile/feature/native_profile_counter_spec.spl test/system/app/optimize/feature/pure_simple_executable_layout_spec.spl test/system/os/baremetal/feature/breakpoint_counter_profile_spec.spl
SIMPLE_LIB=src bin/simple test test/unit/compiler/interpreter/tiered_jit_hotspot_spec.spl --mode=interpreter --clean
find doc/06_spec -name '*_spec.spl' | wc -l
git diff --check
```

Native/bare-metal slices add QEMU or native executable smoke gates before any
speedup claim.
