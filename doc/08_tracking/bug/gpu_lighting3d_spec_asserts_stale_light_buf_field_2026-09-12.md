# gpu_lighting3d_spec asserts a stale `light_buf` field

- Status: OPEN (2026-09-12)
- Area: lib / engine / render
- Severity: low (one red unit case, no product impact)
- Found by: TODOFIX-0 lane while implementing todos 15/16/25/26 (out of that scope, not fixed)

## Symptom

`test/01_unit/lib/nogc_sync_mut/engine/render/gpu_lighting3d_spec.spl` has been
red at `origin/main` independently of any change in this lane:

```
Stream D: GpuLightingState init
  gpu_lighting_init
    ✗ AC-4: light_buf id is valid after init
      semantic: class `GpuLightingState` has no field named `light_buf`
SPEC FILE VERDICT: ... outcome=ERROR declared>=18 executed=18 passed=17 failed=1
```

In a whole-DIRECTORY run the same defect is much worse: the file does not lose one
case, it fails to compile at all and collapses to one synthetic failure —

```
FAIL test/01_unit/lib/nogc_sync_mut/engine/render/gpu_lighting3d_spec.spl (0 passed, 1 failed)
error: compile failed (...gpu_lighting3d_spec_spec_native.spl): semantic: HIR lowering:
Unsupported feature: cannot infer field type while lowering main:
struct 'GpuLightingState' field 'light_buf'
SPEC FILE VERDICT: ... outcome=ERROR declared>=1 executed=1 passed=0 failed=1
```

So the blast radius is all 18 cases in dir/compiled mode, not the single case that
single-file (interpreted) mode reports.

## Repro

```
cd <worktree>
bin/simple test test/01_unit/lib/nogc_sync_mut/engine/render/gpu_lighting3d_spec.spl
```

Binary: Rust seed at `bin/release/aarch64-unknown-linux-gnu/simple`, sha256 prefix `3d120a6f`.
Measured identical (17 passed / 1 failed) before and after this lane's change to
`src/lib/nogc_sync_mut/engine/render/gpu_lighting3d.spl`.

## Diagnosis

`class GpuLightingState` declares the buffer field as `buffer`, not `light_buf`
(`src/lib/nogc_sync_mut/engine/render/gpu_lighting3d.spl`). The spec case was
written against an older field name and was never updated. Every other case in
the file uses `buffer` and passes.

## Fix

Rename the assertion's field access `light_buf` -> `buffer` in that one case. No
product change. Left for the owning lane rather than fixed here, per the
out-of-scope rule.
