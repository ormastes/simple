# engine2d_render_evidence_spec.spl fails to load: missing `os.kernel.arch.x86.render_capture_ack` module (2026-08-08)
- Status: RESOLVED (2026-09-12) — module written per this record's own unblock condition; spec 2/2, see Triage 2026-09-12 (second)

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

## Triage 2026-09-12
Rule B: ran `bin/simple test test/01_unit/os/compositor/engine2d_render_evidence_spec.spl` on the deployed seed; it FAILs, confirming the defect still reproduces. Binary: /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.

## Triage 2026-09-12 (second pass — fixed)

Binary: `bin/simple` = shared clone's Rust seed, `sha256 3d120a6f…`, aarch64.

Took the first branch of this record's own **Unblock condition**: wrote
`src/os/kernel/arch/x86/render_capture_ack.spl`. (`src/os/kernel/arch/x86/`
does exist today — it holds `com1_common.spl` and `port_io_owner.spl`; the
record's `find` predates it.) The module is a fixed-width, allocation-free
guest-side encoder for the same `BRC1` line the host builds by concatenation in
`backend_render_capture_control_line`: 41 bytes, `"BRC1 " + kind + " " +
hex16(boot_id) + " " + hex16(frame_id) + "\n"`, one byte per call, 0 for an
out-of-range index. The trailing newline is why the spec compares
`guest_line == host_line + "\n"`.

That exposed a **second** landed-half behind the same load failure:
`src/os/compositor/engine2d_render_evidence.spl:17` imports `FirmwareSha256`
and `parse_sha256_hex_words` from `os.drivers.framebuffer.ramfb`, uses
`FirmwareSha256` as a receipt field type (line 71) and calls the parser (line
84) — and **neither was declared in `ramfb.spl`**, so `simpleos_render_receipt`
was unresolvable for every caller, not just this spec. Both are now declared
there: the four-word big-endian digest struct, and a byte-indexed parser over
64 hex digits returning nil on any malformed input.

```
before:  declared>=2 executed=0   (Cannot resolve module: os.kernel.arch.x86.render_capture_ack)
after:   outcome=OK declared>=2 executed=2 passed=2 failed=0
```

Neighbours re-run, no movement: `engine2d_baremetal_core_spec` 19/19,
`engine2d_baremetal_core_parity_spec` 8/8,
`compositor_engine2d_surface_spec` 10/10, `qrb2210_drm_kms_display_provider_spec`
6/6, `qrb2210_gui_entry_desktop_contract_spec` 3/3. Two neighbours are red for
unrelated pre-existing reasons and were already red:
`compositor_engine2d_window_revision_source_spec` (`unknown extern function:
rt_fs_read_text`) and `qrb2210_native_2d_composition_root_spec` (a
`# codex-impl` source-text assertion).
