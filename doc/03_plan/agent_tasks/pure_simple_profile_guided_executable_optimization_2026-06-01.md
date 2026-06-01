# Pure Simple Profile-Guided Executable Optimization Agent Plan

Date: 2026-06-01

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
