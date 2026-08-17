# engine2d_render_evidence_spec.spl fails to load: missing `os.kernel.arch.x86.render_capture_ack` module (2026-08-08)

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

## Summary

`test/01_unit/os/compositor/engine2d_render_evidence_spec.spl` fails at
module-load time, both in-container and on the host, with:

```
error: semantic: Cannot resolve module: os.kernel.arch.x86.render_capture_ack
error: test-runner: no examples executed
Results: 1 total, 0 passed, 1 failed
```

Found while running unit B3 (container-run verification of the existing 2D
suite,
`doc/03_plan/ui/testing/render_2d_vulkan_functional_coverage_plan_2026-08-07.md`).

## Evidence

Reproduces identically:
- In-container: `docker run ... simple test 'test/01_unit/os/compositor/engine2d_render_evidence_spec.spl' --no-session-daemon --sequential` — `Results: 1 total, 0 passed, 1 failed`.
- On host: `bin/release/x86_64-unknown-linux-gnu/simple test test/01_unit/os/compositor/engine2d_render_evidence_spec.spl --no-session-daemon --sequential` — same failure, same duration (~750ms-1.7s), confirming this is a PRODUCT defect, not a container-environment artifact.

The spec (`test/01_unit/os/compositor/engine2d_render_evidence_spec.spl:36-39`)
imports:

```
use os.kernel.arch.x86.render_capture_ack.{
    render_capture_control_wire_byte_at,
    render_capture_control_wire_byte_count
}
```

`find src/os/kernel/arch/x86*` shows only `x86_32/` and `x86_64/` — no bare
`x86/` directory, and `render_capture_control_wire_byte_at` /
`render_capture_control_wire_byte_count` do not appear anywhere in the tree
(`grep -rln "render_capture_control_wire_byte_at" src/` returns nothing). The
module this spec imports from was apparently never created — only the
neighbouring wire-encoding helper `backend_render_capture_control_line` in
`src/lib/common/renderdoc/backend_render_receipt_wire.spl` exists.

## Impact

The whole spec file (1 declared example) fails to load, so 0 examples
execute. This is the only red in the 14-spec B3 verification sweep of the
engine2d/render_opt/compositor/virtio surface; all 13 other specs pass
(151 examples, 0 failures across them).

## Unblock condition

Either create
`src/os/kernel/arch/x86/render_capture_ack.spl` exporting
`render_capture_control_wire_byte_at` and
`render_capture_control_wire_byte_count` (per-arch wire-byte accessors for
the capture-control line encoded by
`backend_render_capture_control_line`), or fix the spec's import path if the
functions were relocated/renamed elsewhere and the spec is simply stale.

## Filed by

Unit B3, `doc/03_plan/ui/testing/render_2d_vulkan_functional_coverage_plan_2026-08-07.md`,
2026-08-08. Out of scope to fix here — B3 is verification-only (collision
set: read-only, script file only).
