# Engine2D strict create: enum identity mismatch across import alias paths

Date: 2026-08-15
Status: WORKED AROUND IN STDLIB; UNDERLYING COMPILER DEFECT OPEN

## Symptom

`Engine2D.create_with_backend_strict(16, 16, "vulkan")` returned
`Err(probe)` whose diagnostic read
`requested=vulkan;selected=vulkan;status=Initialized;...;reason=Vulkan initialized`
— i.e. the probe SUCCEEDED, yet the strict path treated it as
not-initialized. This made
`scripts/check/check-vulkan-engine2d-readback.shs` report
`present_exercised=false / readback_exercised=false / spec_status=not_run /
overall=fail` on a host with a fully working NVIDIA Vulkan stack
(TITAN RTX, `simple-runtime/vulkan` feature build).

## Root cause

`src/lib/gc_async_mut/gpu/engine2d/engine.spl` imports the probe types via
the ALIAS module path:

    use std.gpu.engine2d.backend_probe.{BackendProbeResult, BackendStatus}

while the `BackendProbeResult` object is constructed inside the canonical
module (`std.gc_async_mut.gpu.engine2d.backend_probe`). Under native
codegen the two import paths yield distinct enum identities, so inside
engine.spl `probe.status == BackendStatus.Initialized` is ALWAYS false even
when `backend_status_text(probe.status)` prints `Initialized`. A repro
script importing the enum via the canonical path performed the identical
comparison on the identical probe and got `true`.

## Fix applied (stdlib workaround)

`create_with_backend_strict` now calls `backend_probe_initialized(probe)`
— the comparison executes inside the enum's defining module, where the
identity is consistent — instead of comparing `probe.status` locally
(`src/lib/gc_async_mut/gpu/engine2d/engine.spl`, import line 57 + strict
create body ~line 789). While diagnosing, the if/match tail-expression body
was also rewritten with explicit `return`s.

## Still open

- Compiler: enum values must compare equal regardless of which alias path
  the comparing module used to import the enum type.
- engine.spl has further `probe.status == BackendStatus.Initialized`
  comparisons (~lines 949-1128, backend auto-selection) that are likely
  equally false-negative under native codegen and silently degrade backend
  selection; they should be migrated to `backend_probe_initialized` or
  fixed by the compiler-level fix.

## Related

- `scripts/check/check-vulkan-engine2d-readback.shs` also passed
  `--no-daemon` to `simple test`, which the pure-Simple test runner rejects
  (`Error: unknown option: --no-daemon`) — the real flag is
  `--no-session-daemon`. Fixed in the same change; with both fixes the lane
  reports `overall=pass` with `spec_status=pass` on the TITAN RTX host.

## Follow-up census + broadened fix (2026-08-15, second pass)

Census of `BackendStatus.` comparisons OUTSIDE the defining module
(`src/lib/gc_async_mut/gpu/engine2d/backend_probe.spl`), src/lib + src/app:

| Site | Import path | Verdict |
|------|-------------|---------|
| engine.spl:942,950,952,1081,1093,1095,1121 (`== BackendStatus.Initialized`) | alias `std.gpu.engine2d.backend_probe` | UNSAFE — fixed (blob c81c4723ee33) |
| src/app/wm_compare/backend_measurement_capture.spl:294 (`==`), :563 (`!=`) | alias | UNSAFE — fixed (blob 0436dd444468) |
| src/app/wm_compare/backend_measurement_report.spl:320 (`== BackendStatus.Fallback`) | alias | UNSAFE — fixed via new exported helper `backend_probe_fallback` (report blob 306d3c057dff, backend_probe.spl blob 51393b6a2731) |
| browser_engine/simple_web_engine2d_renderer.spl:1177, simple_web_layout_engine2d_fast.spl:807 | canonical `std.gc_async_mut...` | SAFE (canonical import matches constructor identity) |
| backend_vulkan_spirv/ffi_dispatch/sffi_dispatch/backend_opencl/backend_directx | mixed | SAFE — constructor-only, no comparisons |

Fixed variants are built on `git show origin/main:` bases (the working-tree
engine.spl carries another session's font WIP and was left untouched);
stored as git blobs via `git hash-object -w`:
engine.spl c81c4723ee33c9b29cb4668caf388d0dcdb36d0c,
backend_probe.spl 51393b6a27312a9d0b816e7560dad17261ea8298,
backend_measurement_capture.spl 0436dd44446d81611b32ea55e3896955b8ac3b9f,
backend_measurement_report.spl 306d3c057dffe98e5c918dc854d8a77cd7360b11.

### Interpreter-fallback from the earlier broadened attempt: NOT REPRODUCIBLE

An earlier session reported that replacing all remaining comparisons with
`backend_probe_initialized` caused `native_execution_reason=interpreter-fallback`
in the readback lane. Re-attempted on a clean origin/main base with ALL 7
remaining engine.spl sites replaced (swap-run-restore,
`SIMPLE_BIN=build/browser-vulkan/simple sh scripts/check/check-vulkan-engine2d-readback.shs`):
the lane reports `overall=pass` / `spec_status=pass` with ZERO
"falling back to interpreter" occurrences in the evidence log. Conclusion:
the fallback was an artifact of the earlier variant's base (pre-fix working
tree carrying unrelated WIP), not of the helper-call migration itself. No
separate native-codegen bug record is warranted on current evidence.

### wm_compare validation

`bin/simple test test/03_system/gui/wm_compare/backend_measurement_{capture,report}_spec.spl`
run with the three fixed files swapped in, then on the unmodified tree:
verdicts are byte-identical (capture: `passed=0 failed=1 timeout=1
reason=daemon-worker-timeout`; report: `16 examples, 1 failure` — same
example "accepts unavailable backend lanes only with explicit reason").
Both failures are PRE-EXISTING on the unmodified tree; the fix introduces
zero delta.
