# No-GC Engine2D Draw IR Runtime Queue Spec

> This focused spec covers the no-GC Draw IR queue-dispatch helper. It proves payload checksum/SDN text generation and runtime submit/drain/dispatch receipts without importing the GC Engine2D renderer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# No-GC Engine2D Draw IR Runtime Queue Spec

This focused spec covers the no-GC Draw IR queue-dispatch helper. It proves payload checksum/SDN text generation and runtime submit/drain/dispatch receipts without importing the GC Engine2D renderer.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md |
| Source | `test/01_unit/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This focused spec covers the no-GC Draw IR queue-dispatch helper. It proves
payload checksum/SDN text generation and runtime submit/drain/dispatch receipts
without importing the GC Engine2D renderer.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md

## Syntax

The no-GC dispatch helper is imported directly from
`std.nogc_async_mut.gpu.engine2d.draw_ir_runtime_queue`. The queue identity
comes from `engine2d_host_gpu_runtime_queue_with_backend_handle`, and the test
uses only built-in SSpec matchers.

## Examples

```simple
use std.spec.step

val queue = engine2d_host_gpu_runtime_queue_with_backend_handle("vulkan", 1, 7, true, 4096)
val result = engine2d_draw_ir_runtime_queue_dispatch_only(batch, true, queue)
expect(result.runtime_dispatch.backend_handle).to_equal(7)
```

## Acceptance

The scenario builds a GPU-selected Draw IR batch, submits it through the no-GC
runtime queue helper, and asserts that the runtime receipt carries the backend
handle, payload hash, and Draw IR v2 payload text.

## Scenarios

### no-GC Engine2D Draw IR runtime queue dispatch

#### submits and dispatches a GPU-selected Draw IR payload without GC Engine2D

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- submits and dispatches a GPU-selected Draw IR payload without GC Engine2D
   - Expected: result.payload.batch_id equals `nogc-runtime`
   - Expected: result.payload.command_count equals `1`
   - Expected: result.runtime_submit.packet_id equals `1`
   - Expected: result.runtime_drain.drained equals `1`
   - Expected: result.runtime_drain.status equals `completed`
   - Expected: result.runtime_drain.last_backend_handle equals `7`
   - Expected: result.runtime_dispatch.status equals `dispatched`
   - Expected: result.runtime_dispatch.backend_handle equals `7`
   - Expected: result.runtime_dispatch.payload_hash equals `result.payload.command_checksum`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("submits and dispatches a GPU-selected Draw IR payload without GC Engine2D")
rt_host_gpu_queue_reset()
val batch = draw_ir_batch("nogc-runtime", DRAW_IR_BACKEND_GPU, draw_ir_embedding_config("surf1", "win1", 0, 0, 20, 16, 10, 1000, false), [
    draw_ir_rect("body", 2, 3, 6, 5, GREEN)
])
val queue = engine2d_host_gpu_runtime_queue_with_backend_handle("vulkan", 1, 7, true, 4096)

val result = engine2d_draw_ir_runtime_queue_dispatch_only(batch, true, queue)

expect(result.payload.batch_id).to_equal("nogc-runtime")
expect(result.payload.command_count).to_equal(1)
expect(result.runtime_submit.submitted).to_be(true)
expect(result.runtime_submit.packet_id).to_equal(1)
expect(result.runtime_drain.drained).to_equal(1)
expect(result.runtime_drain.status).to_equal("completed")
expect(result.runtime_drain.last_backend_handle).to_equal(7)
expect(result.runtime_dispatch.dispatched).to_be(true)
expect(result.runtime_dispatch.status).to_equal("dispatched")
expect(result.runtime_dispatch.backend_handle).to_equal(7)
expect(result.runtime_dispatch.payload_hash).to_equal(result.payload.command_checksum)
expect(result.runtime_dispatch.payload_text).to_contain("schema=simple-draw-ir-v2")
expect(result.queued_for_gpu).to_be(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md`
- **Design:** `doc/04_architecture/ui/simple_gui_stack.md`
- **Research:** `doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `58a006c204817865862bc7189d246c517ff98e07b73511ffc7e4954e429625bf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `58a006c204817865862bc7189d246c517ff98e07b73511ffc7e4954e429625bf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `58a006c204817865862bc7189d246c517ff98e07b73511ffc7e4954e429625bf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'submits and dispatches a GPU-selected Draw IR payload without GC Engine2D' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
