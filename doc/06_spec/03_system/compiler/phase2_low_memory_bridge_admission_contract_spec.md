# Wave-0 Low-Memory Bridge Admission Contract

This manual describes the fail-closed system contract for preparing a focused
Wave-0 compiler bridge. It does not admit a compiler candidate and does not
authorize a bootstrap, native-all, full Stage4, WM, QEMU, or renderer run.

| Field | Value |
|-------|-------|
| Status | Preparation implemented; execution evidence pending |
| Executable spec | `test/03_system/compiler/phase2_low_memory_bridge_admission_contract_spec.spl` |
| Focused bridge | `test/02_integration/compiler/phase2_low_memory_source_reclaim_bridge.spl` |
| Live probe | `test/02_integration/compiler/phase2_low_memory_source_reclaim_live_probe.spl` |
| Runtime prerequisite | `doc/09_report/wm_wave0_core_c_runtime_capsule_2026-07-26.md` |
| Updated | 2026-07-26 |

## Purpose

The bridge must exercise the current `CompilerDriver` low-memory path while
keeping the final compiler micro-cycle unspent until an independently reviewed
runner can collect bounded, reproducible evidence. Static preparation is
necessary but is not compiler admission.

Steps identified below as supporting source review extend beyond the exact
static assertions in the executable four-scenario contract. They are manual
review obligations and are not claimed as executable test results.

## Scenario 1: Require the Exact Three Opt-Ins

1. Inspect the canonical bootstrap API and its pure predicate helper.
2. Confirm `SIMPLE_BOOTSTRAP`, `SIMPLE_BOOTSTRAP_STAGE4`, and
   `SIMPLE_BOOTSTRAP_LOW_MEMORY` are read through the canonical environment
   facade.
3. Confirm low-memory mode is enabled only when all three values are exactly
   `"1"`.
4. Confirm an unset, partial, or differently valued combination defaults to
   disabled.
5. As supporting source review, confirm the fixed bootstrap API signature and
   its existing caller remain unchanged.

Expected result: the positive control can opt in explicitly, while the
negative control remains on the normal path.

## Scenario 2: Inspect the Tracked Full-Driver Bridge and Probe

1. Confirm the focused bridge has a stable version marker and the
   `build-probe` operation asserted by the executable contract. As supporting
   source review, confirm no other operation is accepted.
2. Confirm the bridge invokes the current `CompilerDriver`. As supporting
   source review, confirm the live probe does too and neither substitutes a
   standalone reclaim helper.
3. Confirm the probe runs in check mode and reports whether low-memory mode was
   enabled.
4. Confirm the executable contract checks the named first-free and
   alias-refusal receipt fields. As supporting source review, confirm their
   expected values are `1` and `0` and no freed alias is reread.
5. Confirm the asserted exclusions for `rt_native_build` and
   bootstrap-stage4. As supporting source review, confirm neither source uses
   a seed route, native-all, or a full Stage4 workflow.

Expected result: the prepared sources cover the intended driver path and do
not hide a fallback route.

## Scenario 3: Bind Current Reclaim Ordering and Runtime Prerequisite

1. Inspect the current driver source.
2. Confirm the low-memory start marker precedes
   `reclaim_source_contents()`.
3. Confirm the reclaim call precedes the completion marker that reports the
   reclaimed count.
4. Inspect the accepted core-C runtime capsule report.
5. Confirm that report records the sole `rt_string_free` provider and clearly
   distinguishes runtime acceptance from compiler admission.

Expected result: static source ordering and the accepted dedicated runtime are
present before any compiler candidate is executed.

## Scenario 4: Keep Admission Fail Closed

1. Confirm no admission runner is present in the bridge or probe.
2. Confirm the sources do not embed no-stub policy, runtime selection,
   candidate-admission, or transport-regression orchestration.
3. Confirm no bridge execution or final micro-cycle is claimed by this
   contract.

Expected result: preparation can pass while compiler admission remains
explicitly pending.

## Required Future Execution Evidence

A separately reviewed runner must retain bounded positive and negative control
artifacts. It must record exact compiler, bridge, runtime manifest, archive,
and runtime-tree identities; executable classifiers and SHA-256 values; the
single `rt_string_free` text provider from `nm`; no-stub enforcement for every
command; exact argument vectors; timings; and maximum RSS. It must select the
accepted capsule through a dedicated `SIMPLE_RUNTIME_PATH` and retain the exact
selected path and hash in the evidence.

The positive control must set all three opt-ins, report low-memory enabled,
emit exactly one ordered start/done marker pair with a reclaimed count greater
than zero, and report the `1/0` free receipt. The negative control must omit
the opt-ins, report low-memory disabled, and emit no reclaim markers. The
focused transport and frontend gates remain 73/84 evidence obligations.
Candidate admission is necessary-only and does not complete the later
host-renderer or x86/ARM QEMU evidence lanes.

Until that runner and its exact native command receive independent
high-capability approval and execute once, the final Wave-0 micro-cycle remains
unspent.
