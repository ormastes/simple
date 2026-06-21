# Engine2D OpenCL Session Readback Evidence Specification

> Verifies typed OpenCL readback evidence for checksum comparison and buffer readback failures without claiming unverified GPU execution.

<!-- sdn-diagram:id=opencl_session_readback_evidence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=opencl_session_readback_evidence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

opencl_session_readback_evidence_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=opencl_session_readback_evidence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2D OpenCL Session Readback Evidence Specification

Verifies typed OpenCL readback evidence for checksum comparison and buffer readback failures without claiming unverified GPU execution.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Reference | `src/lib/gc_async_mut/gpu/engine2d/opencl_session.spl` |
| Requirements | N/A |
| Plan | doc/03_plan/ui/graphics/engine/game_engine_2d3d_unification_plan_2026-06-12.md |
| Design | doc/05_design/ui/renderer_unification_2026-06-15.md |
| Research | doc/01_research/ui/render_path/gui_web_2d_render_optimization_2026-06-16.md |
| Source | `test/01_unit/lib/gpu/engine2d/opencl_session_readback_evidence_spec.spl` |
| Updated | 2026-06-21 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies typed OpenCL readback evidence for checksum comparison and buffer
readback failures without claiming unverified GPU execution.

**Source:** `src/lib/gc_async_mut/gpu/engine2d/opencl_session.spl`
**Requirements:** N/A
**Research:** doc/01_research/ui/render_path/gui_web_2d_render_optimization_2026-06-16.md
**Plan:** doc/03_plan/ui/graphics/engine/game_engine_2d3d_unification_plan_2026-06-12.md
**Design:** doc/05_design/ui/renderer_unification_2026-06-15.md

## Syntax

Use `readback_evidence()` for checksum result classification and
`read_buffer_evidence()` for staged OpenCL buffer-read failure diagnostics.

## Examples

The scenarios cover matched, unavailable, and mismatched readback checks plus
missing FFI, queue, device buffer, host buffer, invalid size, and failed buffer
readback status codes.

## Scenarios

### OpenClSession readback evidence

#### reports readback outcomes without claiming unverified OpenCL execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = OpenClSession.create()
val matched = session.readback_evidence(true, 1234, 1234)
val unavailable = session.readback_evidence(false, 1234, 1234)
val mismatch = session.readback_evidence(true, 1234, 999)

expect(matched.status_code).to_equal("readback-matched")
expect(matched.reason).to_equal("readback-checksum-matched")
expect(unavailable.success).to_equal(false)
expect(unavailable.status_code).to_equal("readback-unavailable")
expect(mismatch.status_code).to_equal("readback-mismatch")
```

</details>

#### records typed buffer readback failures before checksum validation

- var session = OpenClSession create with ffi
   - Expected: missing_ffi.status_code equals `missing-ffi`
   - Expected: missing_queue.status_code equals `missing-queue`
   - Expected: missing_buffer.status_code equals `missing-buffer`
   - Expected: missing_host.status_code equals `missing-host-buffer`
   - Expected: invalid_size.status_code equals `invalid-size`
   - Expected: readback_failed.status_code equals `readback-failed`
   - Expected: readback_failed.reason equals `opencl-buffer-read-failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_ffi = OpenClSession.create().read_buffer_evidence(1, 1, 16, 1234, 1234)
var session = OpenClSession.create_with_ffi(OpenClFfi.create_static())
val missing_queue = session.read_buffer_evidence(1, 1, 16, 1234, 1234)
session.queue = 3
val missing_buffer = session.read_buffer_evidence(0, 1, 16, 1234, 1234)
val missing_host = session.read_buffer_evidence(1, 0, 16, 1234, 1234)
val invalid_size = session.read_buffer_evidence(1, 1, 0, 1234, 1234)
val readback_failed = session.read_buffer_evidence(1, 1, 16, 1234, 999)

expect(missing_ffi.status_code).to_equal("missing-ffi")
expect(missing_queue.status_code).to_equal("missing-queue")
expect(missing_buffer.status_code).to_equal("missing-buffer")
expect(missing_host.status_code).to_equal("missing-host-buffer")
expect(invalid_size.status_code).to_equal("invalid-size")
expect(readback_failed.status_code).to_equal("readback-failed")
expect(readback_failed.reason).to_equal("opencl-buffer-read-failed")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/ui/graphics/engine/game_engine_2d3d_unification_plan_2026-06-12.md](doc/03_plan/ui/graphics/engine/game_engine_2d3d_unification_plan_2026-06-12.md)
- **Design:** [doc/05_design/ui/renderer_unification_2026-06-15.md](doc/05_design/ui/renderer_unification_2026-06-15.md)
- **Research:** [doc/01_research/ui/render_path/gui_web_2d_render_optimization_2026-06-16.md](doc/01_research/ui/render_path/gui_web_2d_render_optimization_2026-06-16.md)


</details>
