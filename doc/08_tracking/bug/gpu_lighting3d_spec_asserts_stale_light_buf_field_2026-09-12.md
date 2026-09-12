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
