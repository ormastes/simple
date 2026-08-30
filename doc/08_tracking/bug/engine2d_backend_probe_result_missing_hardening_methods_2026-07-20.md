# Engine2D BackendProbeResult missing is_hardware/strict_failure_without_fallback (present on 3D counterpart)

## Symptom

`test/01_unit/lib/gpu/engine2d/backend_probe_strict_spec.spl` fails all 8
examples:

```
semantic: method `strict_failure_without_fallback` not found on type `BackendProbeResult`
semantic: method `is_hardware` not found on type `BackendProbeResult`
semantic: method 'probe_all_summary' not found on value of type object in nested call context
```

## Root cause

`class BackendProbeResult` is defined at
`src/lib/gc_async_mut/gpu/engine2d/backend_probe.spl:36`, but has neither an
`is_hardware` nor a `strict_failure_without_fallback` method anywhere in that
file (confirmed via grep for `fn is_hardware`/`fn strict_failure_without_fallback`
scoped to the file — no hits).

Repo-wide, both methods **do** exist, but only on the 3D backend-probe
counterpart: `src/lib/gc_async_mut/gpu/engine3d/backend_probe3d.spl` defines
`fn is_hardware` and `fn strict_failure_without_fallback` (presumably on
`BackendProbeResult3D` or a related type there). This strongly suggests the 2D
`BackendProbeResult` was meant to get the same "strict/hardened" API surface as
its 3D sibling (the spec's own name, `backend_probe_strict_spec.spl`, and its
description `"Engine2D strict backend probe diagnostics"`, match the hardening
theme) but the methods were never ported over to the 2D type, or the 2D probe
module was refactored without carrying them along.

The third failure, `method 'probe_all_summary' not found on value of type
object in nested call context`, is a related but distinct symptom (different
error shape — "on value of type object" rather than naming
`BackendProbeResult` directly) for the `"probe summary includes all hardened
backend names"` example; likely the same missing-hardening-API root cause but
not independently confirmed against a specific function definition site in
this triage pass.

## Repro

```
SIMPLE_RUST_SEED_WARNING=0 timeout 25 \
  bin/release/x86_64-unknown-linux-gnu/simple test \
  test/01_unit/lib/gpu/engine2d/backend_probe_strict_spec.spl --no-session-daemon
```

## Fix hypothesis (not attempted — src/** GPU-probe API work, out of test-shard scope)

Port `is_hardware`, `strict_failure_without_fallback`, and whatever backs
`probe_all_summary` from the 3D backend-probe module
(`src/lib/gc_async_mut/gpu/engine3d/backend_probe3d.spl`) onto the 2D
`BackendProbeResult` in `src/lib/gc_async_mut/gpu/engine2d/backend_probe.spl`,
or confirm with the GPU/engine2d owner whether the 2D probe intentionally
diverges from 3D and the spec needs to target a different/newer type instead.

## Affected specs

- `test/01_unit/lib/gpu/engine2d/backend_probe_strict_spec.spl` (8/8 examples
  fail; this is the contested gpu/engine2d area so was left unedited per this
  campaign's ENV-skip guidance, but the root cause above is a genuine,
  well-defined API gap, not an environment/hardware-availability issue)
