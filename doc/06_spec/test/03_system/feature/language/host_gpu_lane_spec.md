# Host/GPU lane event-flow and grammar contract

> Exercises the parser-acceptance and Engine2D lane-contract surface for the host/GPU lane grammar and event-flow diagnostics described by the host_gpu_lane design contract.

<!-- sdn-diagram:id=host_gpu_lane_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=host_gpu_lane_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

host_gpu_lane_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=host_gpu_lane_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Host/GPU lane event-flow and grammar contract

Exercises the parser-acceptance and Engine2D lane-contract surface for the host/GPU lane grammar and event-flow diagnostics described by the host_gpu_lane design contract.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/feature/host_gpu_lane.md |
| Plan | doc/03_plan/sys_test/host_gpu_lane.md |
| Design | doc/05_design/host_gpu_lane.md |
| Research | doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md |
| Source | `test/03_system/feature/language/host_gpu_lane_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Exercises the parser-acceptance and Engine2D lane-contract surface for the
host/GPU lane grammar and event-flow diagnostics described by the
host_gpu_lane design contract.

## Syntax

Canonical examples:

```simple
target.later(max_packet: 512) gpu \:
    scene.apply_draw_ir_delta(draw_ir_delta_ref)

target.later(max_packet: 512) host \:
    session.focus(hit.target_id)
```

**Requirements:** doc/02_requirements/feature/host_gpu_lane.md
**Research:** doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md
**Plan:** doc/03_plan/sys_test/host_gpu_lane.md
**Design:** doc/05_design/host_gpu_lane.md

## Scenario Model

The host/GPU lane feature has two current evidence surfaces:

1. Parser acceptance through `bin/simple check` for canonical syntax, or through
   `SIMPLE_BIN` when the spec must exercise a freshly built driver.
2. Engine2D lane-contract validation for event-flow and performance semantics.

Parser acceptance verifies that the compact grammar remains a small extension
over existing lambdas. The accepted form places the lane marker after
`later(...)` and before `\:` or `\e:`.

Engine2D lane-contract validation verifies behavior that compiler lowering and
runtime queues must preserve when they land:

- same-lane callbacks can execute directly;
- cross-lane callbacks become queue packets;
- host lane commits host semantic state;
- GPU lane accelerates render/effect/resource batches;
- GPU lane cannot mutate host-owned semantic fields;
- GPU hot-path work must be coarse grained;
- packet sizes remain bounded by declared `max_packet` contracts;
- fallback is explicit evidence rather than silent success;
- estimated GPU batch time must be lower than the CPU baseline when a strict
  backend is available.

## Event Flow

Host input starts on the host event lane. A GPU hit-test or render/effect update
may be scheduled with `target.later(...) gpu \:`. If GPU work needs to change
semantic UI state, it must send a host proposal and the final mutation runs
through `target.later(...) host \:`.

The system scenarios intentionally avoid real GPU hardware. They prove the
language surface and lane contract before backend-specific Vulkan, Metal,
WebGPU, CUDA, or DirectX evidence is required.

## Acceptance Matrix

HGL-001 canonical grammar:
`target.later() gpu \:` and `target.later() host \:` must parse through
`bin/simple check` or the configured `SIMPLE_BIN` child process.

HGL-002 host semantic mutation:
host lane code may mutate `state.checked` or focus/session state.

HGL-003 GPU render/effect batch:
GPU lane code may carry coarse Draw IR or DisplayGraphIR batch work with packet
bounds.

HGL-004 GPU semantic mutation rejection:
the lane contract rejects GPU attempts to commit host semantic fields.

HGL-005 per-widget dispatch diagnostic:
the lane contract rejects one GPU `later()` callback per widget in a loop and
requires a batch.

## Out Of Scope

This spec proves parser acceptance plus statement-position runtime marker
lowering for interpreter and native execution. It does not prove expression
position lane markers, backend device submission, or GPU readback. Those are
tracked by the implementation plan and perf report. Queue packets consume the
active backend handle when one is registered, and drain as typed unavailable
when the active handle remains `0`.

## Generated Manual Policy

The generated manual should show the primary flow first:

- canonical syntax accepted;
- host semantic mutation accepted;
- GPU render/effect batch accepted;
- GPU semantic mutation rejected;
- per-widget GPU dispatch rejected.

Executable SSpec remains folded below the manual scenarios. No screenshot,
HTML, or raster evidence is needed because this is a compiler/contract system
test, not a visual UI test. Lowered GPU lanes now enqueue, submit, and complete
one runtime packet so the host can observe a backward completion receipt without
manual drain.

## Scenarios

### host/GPU lane grammar and event-flow contract

#### should accept canonical gpu and host lane markers after later

- Check the canonical target.later(...) gpu and host grammar
- "target later
- "target later
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check the canonical target.later(...) gpu and host grammar")
val source = host_gpu_fixture(
    "target.later() gpu \\:\n" +
    "    val draw_ir_batch = \"DisplayGraphIR batch\"\n" +
    "target.later() host \\:\n" +
    "    val semantic_owner = \"host\"\n"
)

val (stdout, stderr, code) = check_source("canonical_lane_markers", source)

expect(code).to_equal(0)
expect(combined_output(stdout, stderr)).to_contain("All checks passed")
```

</details>

#### should emit runtime begin and end events around an interpreted GPU lane

- Run a GPU lane and inspect marker counters plus backend-handle queue emission
- "extern fn rt host gpu lane reset
- "extern fn rt host gpu active backend handle set
- "extern fn rt host gpu lane event count
- "extern fn rt host gpu lane begin count
- "extern fn rt host gpu lane end count
- "extern fn rt host gpu lane last lane
- "extern fn rt host gpu lane last phase
- "extern fn rt host gpu queue packet count
- "extern fn rt host gpu queue submitted count
- "extern fn rt host gpu queue completed count
- "extern fn rt host gpu queue in flight count
- "extern fn rt host gpu queue last status
- "extern fn rt host gpu queue last backend handle
- "    fn later
- "        pass do nothing
- "rt host gpu lane reset
- "rt host gpu active backend handle set
- "val target = Target
- "target later
- "print
- "print
- "print
- "print
- "print
- "print
- "print
- "print
- "print
- "print
- "print
- "print
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 53 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run a GPU lane and inspect marker counters plus backend-handle queue emission")
val source =
    "extern fn rt_host_gpu_lane_reset()\n" +
    "extern fn rt_host_gpu_active_backend_handle_set(backend_handle: i64) -> i64\n" +
    "extern fn rt_host_gpu_lane_event_count() -> i64\n" +
    "extern fn rt_host_gpu_lane_begin_count() -> i64\n" +
    "extern fn rt_host_gpu_lane_end_count() -> i64\n" +
    "extern fn rt_host_gpu_lane_last_lane() -> i64\n" +
    "extern fn rt_host_gpu_lane_last_phase() -> i64\n" +
    "extern fn rt_host_gpu_queue_packet_count() -> i64\n" +
    "extern fn rt_host_gpu_queue_submitted_count() -> i64\n" +
    "extern fn rt_host_gpu_queue_completed_count() -> i64\n" +
    "extern fn rt_host_gpu_queue_in_flight_count() -> i64\n" +
    "extern fn rt_host_gpu_queue_last_status() -> i64\n" +
    "extern fn rt_host_gpu_queue_last_backend_handle() -> i64\n\n" +
    "class Target:\n" +
    "    fn later():\n" +
    "        pass_do_nothing(\"lane runtime probe\")\n\n" +
    "rt_host_gpu_lane_reset()\n" +
    "rt_host_gpu_active_backend_handle_set(7)\n" +
    "val target = Target()\n" +
    "var body_ran = false\n" +
    "target.later() gpu \\:\n" +
    "    body_ran = true\n" +
    "print(\"body=\" + str(body_ran))\n" +
    "print(\"events=\" + str(rt_host_gpu_lane_event_count()))\n" +
    "print(\"begin=\" + str(rt_host_gpu_lane_begin_count()))\n" +
    "print(\"end=\" + str(rt_host_gpu_lane_end_count()))\n" +
    "print(\"lane=\" + str(rt_host_gpu_lane_last_lane()))\n" +
    "print(\"phase=\" + str(rt_host_gpu_lane_last_phase()))\n" +
    "print(\"queue=\" + str(rt_host_gpu_queue_packet_count()))\n" +
    "print(\"submitted=\" + str(rt_host_gpu_queue_submitted_count()))\n" +
    "print(\"completed=\" + str(rt_host_gpu_queue_completed_count()))\n" +
    "print(\"in_flight=\" + str(rt_host_gpu_queue_in_flight_count()))\n" +
    "print(\"complete_status=\" + str(rt_host_gpu_queue_last_status()))\n" +
    "print(\"complete_backend_handle=\" + str(rt_host_gpu_queue_last_backend_handle()))\n"

val (stdout, stderr, code) = run_source("gpu_lane_runtime_markers", source)
val output = combined_output(stdout, stderr)

expect(code).to_equal(0)
expect(output).to_contain("body=true")
expect(output).to_contain("events=2")
expect(output).to_contain("begin=1")
expect(output).to_contain("end=1")
expect(output).to_contain("lane=2")
expect(output).to_contain("phase=2")
expect(output).to_contain("queue=1")
expect(output).to_contain("submitted=1")
expect(output).to_contain("completed=1")
expect(output).to_contain("in_flight=0")
expect(output).to_contain("complete_status=3")
expect(output).to_contain("complete_backend_handle=7")
```

</details>

#### should emit native runtime queue evidence for a GPU lane

- Force native execution and inspect backend-handle queue counters
- "extern fn rt host gpu lane reset
- "extern fn rt host gpu active backend handle set
- "extern fn rt host gpu lane event count
- "extern fn rt host gpu lane begin count
- "extern fn rt host gpu lane end count
- "extern fn rt host gpu queue reset
- "extern fn rt host gpu queue packet count
- "extern fn rt host gpu queue submitted count
- "extern fn rt host gpu queue completed count
- "extern fn rt host gpu queue in flight count
- "extern fn rt host gpu queue last status
- "extern fn rt host gpu queue last backend handle
- "    fn later
- "rt host gpu lane reset
- "rt host gpu queue reset
- "rt host gpu active backend handle set
- "val target = Target
- "target later
- "print
- "print
- "print
- "print
- "print
- "print
- "print
- "print
- "print
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Force native execution and inspect backend-handle queue counters")
val source =
    "extern fn rt_host_gpu_lane_reset()\n" +
    "extern fn rt_host_gpu_active_backend_handle_set(backend_handle: i64) -> i64\n" +
    "extern fn rt_host_gpu_lane_event_count() -> i64\n" +
    "extern fn rt_host_gpu_lane_begin_count() -> i64\n" +
    "extern fn rt_host_gpu_lane_end_count() -> i64\n" +
    "extern fn rt_host_gpu_queue_reset()\n" +
    "extern fn rt_host_gpu_queue_packet_count() -> i64\n" +
    "extern fn rt_host_gpu_queue_submitted_count() -> i64\n" +
    "extern fn rt_host_gpu_queue_completed_count() -> i64\n" +
    "extern fn rt_host_gpu_queue_in_flight_count() -> i64\n" +
    "extern fn rt_host_gpu_queue_last_status() -> i64\n" +
    "extern fn rt_host_gpu_queue_last_backend_handle() -> i64\n\n" +
    "class Target:\n" +
    "    fn later():\n" +
    "        val marker = 1\n\n" +
    "rt_host_gpu_lane_reset()\n" +
    "rt_host_gpu_queue_reset()\n" +
    "rt_host_gpu_active_backend_handle_set(7)\n" +
    "val target = Target()\n" +
    "target.later() gpu \\:\n" +
    "    val draw_ir_batch = \"DisplayGraphIR batch\"\n" +
    "print(\"events=\" + str(rt_host_gpu_lane_event_count()))\n" +
    "print(\"begin=\" + str(rt_host_gpu_lane_begin_count()))\n" +
    "print(\"end=\" + str(rt_host_gpu_lane_end_count()))\n" +
    "print(\"queue=\" + str(rt_host_gpu_queue_packet_count()))\n" +
    "print(\"submitted=\" + str(rt_host_gpu_queue_submitted_count()))\n" +
    "print(\"completed=\" + str(rt_host_gpu_queue_completed_count()))\n" +
    "print(\"in_flight=\" + str(rt_host_gpu_queue_in_flight_count()))\n" +
    "print(\"complete_status=\" + str(rt_host_gpu_queue_last_status()))\n" +
    "print(\"complete_backend_handle=\" + str(rt_host_gpu_queue_last_backend_handle()))\n"

val (stdout, stderr, code) = run_source_native("gpu_lane_native_runtime_queue", source)
val output = combined_output(stdout, stderr)

expect(code).to_equal(0)
expect(output).to_contain("events=2")
expect(output).to_contain("begin=1")
expect(output).to_contain("end=1")
expect(output).to_contain("queue=1")
expect(output).to_contain("submitted=1")
expect(output).to_contain("completed=1")
expect(output).to_contain("in_flight=0")
expect(output).to_contain("complete_status=3")
expect(output).to_contain("complete_backend_handle=7")
```

</details>

#### should complete native GPU lane queue state before an early return

- Return from inside a native GPU lane and inspect balanced cleanup counters
- "extern fn rt host gpu lane reset
- "extern fn rt host gpu active backend handle set
- "extern fn rt host gpu lane event count
- "extern fn rt host gpu lane begin count
- "extern fn rt host gpu lane end count
- "extern fn rt host gpu queue reset
- "extern fn rt host gpu queue packet count
- "extern fn rt host gpu queue submitted count
- "extern fn rt host gpu queue completed count
- "extern fn rt host gpu queue in flight count
- "extern fn rt host gpu queue last status
- "    fn later
- "        pass do nothing
- "fn early gpu return
- "    val target = Target
- "    target later
- "rt host gpu lane reset
- "rt host gpu queue reset
- "rt host gpu active backend handle set
- "print
- "print
- "print
- "print
- "print
- "print
- "print
- "print
- "print
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 47 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Return from inside a native GPU lane and inspect balanced cleanup counters")
val source =
    "extern fn rt_host_gpu_lane_reset()\n" +
    "extern fn rt_host_gpu_active_backend_handle_set(backend_handle: i64) -> i64\n" +
    "extern fn rt_host_gpu_lane_event_count() -> i64\n" +
    "extern fn rt_host_gpu_lane_begin_count() -> i64\n" +
    "extern fn rt_host_gpu_lane_end_count() -> i64\n" +
    "extern fn rt_host_gpu_queue_reset()\n" +
    "extern fn rt_host_gpu_queue_packet_count() -> i64\n" +
    "extern fn rt_host_gpu_queue_submitted_count() -> i64\n" +
    "extern fn rt_host_gpu_queue_completed_count() -> i64\n" +
    "extern fn rt_host_gpu_queue_in_flight_count() -> i64\n" +
    "extern fn rt_host_gpu_queue_last_status() -> i64\n\n" +
    "class Target:\n" +
    "    fn later():\n" +
    "        pass_do_nothing(\"lane runtime probe\")\n\n" +
    "fn early_gpu_return() -> i64:\n" +
    "    val target = Target()\n" +
    "    target.later() gpu \\:\n" +
    "        return 42\n" +
    "    return 0\n\n" +
    "rt_host_gpu_lane_reset()\n" +
    "rt_host_gpu_queue_reset()\n" +
    "rt_host_gpu_active_backend_handle_set(7)\n" +
    "print(\"result=\" + str(early_gpu_return()))\n" +
    "print(\"events=\" + str(rt_host_gpu_lane_event_count()))\n" +
    "print(\"begin=\" + str(rt_host_gpu_lane_begin_count()))\n" +
    "print(\"end=\" + str(rt_host_gpu_lane_end_count()))\n" +
    "print(\"queue=\" + str(rt_host_gpu_queue_packet_count()))\n" +
    "print(\"submitted=\" + str(rt_host_gpu_queue_submitted_count()))\n" +
    "print(\"completed=\" + str(rt_host_gpu_queue_completed_count()))\n" +
    "print(\"in_flight=\" + str(rt_host_gpu_queue_in_flight_count()))\n" +
    "print(\"complete_status=\" + str(rt_host_gpu_queue_last_status()))\n"

val (stdout, stderr, code) = run_source_native("gpu_lane_native_early_return_cleanup", source)
val output = combined_output(stdout, stderr)

expect(code).to_equal(0)
expect(output).to_contain("result=42")
expect(output).to_contain("events=2")
expect(output).to_contain("begin=1")
expect(output).to_contain("end=1")
expect(output).to_contain("queue=1")
expect(output).to_contain("submitted=1")
expect(output).to_contain("completed=1")
expect(output).to_contain("in_flight=0")
expect(output).to_contain("complete_status=3")
```

</details>

#### should expose native submit-only queue state before completion

- Submit a native runtime queue packet, inspect SUBMITTED, then complete it
- "extern fn rt host gpu queue reset
- "extern fn rt host gpu queue emit
- "extern fn rt host gpu queue submit
- "extern fn rt host gpu queue complete
- "extern fn rt host gpu queue submitted count
- "extern fn rt host gpu queue completed count
- "extern fn rt host gpu queue in flight count
- "extern fn rt host gpu queue last status
- "rt host gpu queue reset
- "val packet id = rt host gpu queue emit
- "val submit count = rt host gpu queue submit
- "val submit status = rt host gpu queue last status
- "val submit in flight = rt host gpu queue in flight count
- "val submit total = rt host gpu queue submitted count
- "val complete before = rt host gpu queue completed count
- "val complete count = rt host gpu queue complete
- "print
- "print
- "print
- "print
- "print
- "print
- "print
- "print
- "print
- "print
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit a native runtime queue packet, inspect SUBMITTED, then complete it")
val source =
    "extern fn rt_host_gpu_queue_reset()\n" +
    "extern fn rt_host_gpu_queue_emit(lane_code: i64, kind_code: i64, payload_size: i64, backend_code: i64) -> i64\n" +
    "extern fn rt_host_gpu_queue_submit(max_packets: i64) -> i64\n" +
    "extern fn rt_host_gpu_queue_complete(max_packets: i64) -> i64\n" +
    "extern fn rt_host_gpu_queue_submitted_count() -> i64\n" +
    "extern fn rt_host_gpu_queue_completed_count() -> i64\n" +
    "extern fn rt_host_gpu_queue_in_flight_count() -> i64\n" +
    "extern fn rt_host_gpu_queue_last_status() -> i64\n\n" +
    "rt_host_gpu_queue_reset()\n" +
    "val packet_id = rt_host_gpu_queue_emit(2, 1, 8, 7)\n" +
    "val submit_count = rt_host_gpu_queue_submit(1)\n" +
    "val submit_status = rt_host_gpu_queue_last_status()\n" +
    "val submit_in_flight = rt_host_gpu_queue_in_flight_count()\n" +
    "val submit_total = rt_host_gpu_queue_submitted_count()\n" +
    "val complete_before = rt_host_gpu_queue_completed_count()\n" +
    "val complete_count = rt_host_gpu_queue_complete(1)\n" +
    "print(\"packet_id=\" + str(packet_id))\n" +
    "print(\"submit_count=\" + str(submit_count))\n" +
    "print(\"submit_status=\" + str(submit_status))\n" +
    "print(\"submit_in_flight=\" + str(submit_in_flight))\n" +
    "print(\"submit_total=\" + str(submit_total))\n" +
    "print(\"complete_before=\" + str(complete_before))\n" +
    "print(\"complete_count=\" + str(complete_count))\n" +
    "print(\"complete_status=\" + str(rt_host_gpu_queue_last_status()))\n" +
    "print(\"complete_in_flight=\" + str(rt_host_gpu_queue_in_flight_count()))\n" +
    "print(\"complete_total=\" + str(rt_host_gpu_queue_completed_count()))\n"

val (stdout, stderr, code) = run_source_native("gpu_lane_native_queue_two_phase", source)
val output = combined_output(stdout, stderr)

expect(code).to_equal(0)
expect(output).to_contain("packet_id=1")
expect(output).to_contain("submit_count=1")
expect(output).to_contain("submit_status=2")
expect(output).to_contain("submit_in_flight=1")
expect(output).to_contain("submit_total=1")
expect(output).to_contain("complete_before=0")
expect(output).to_contain("complete_count=1")
expect(output).to_contain("complete_status=3")
expect(output).to_contain("complete_in_flight=0")
expect(output).to_contain("complete_total=1")
```

</details>

#### should match native runtime queue capacity and backpressure semantics

- Fill the native runtime queue, reject one overflow packet, drain, and accept the next packet
- "extern fn rt host gpu queue reset
- "extern fn rt host gpu queue emit
- "extern fn rt host gpu queue packet count
- "extern fn rt host gpu queue drain
- "extern fn rt host gpu queue last status
- "rt host gpu queue reset
- "    last id = rt host gpu queue emit
- "val overflow id = rt host gpu queue emit
- "val queued = rt host gpu queue packet count
- "val drained = rt host gpu queue drain
- "val after drain id = rt host gpu queue emit
- "print
- "print
- "print
- "print
- "print
- "print
- "print
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fill the native runtime queue, reject one overflow packet, drain, and accept the next packet")
val source =
    "extern fn rt_host_gpu_queue_reset()\n" +
    "extern fn rt_host_gpu_queue_emit(lane_code: i64, kind_code: i64, payload_size: i64, backend_code: i64) -> i64\n" +
    "extern fn rt_host_gpu_queue_packet_count() -> i64\n" +
    "extern fn rt_host_gpu_queue_drain(max_packets: i64) -> i64\n" +
    "extern fn rt_host_gpu_queue_last_status() -> i64\n\n" +
    "rt_host_gpu_queue_reset()\n" +
    "var accepted = 0\n" +
    "var last_id = 0\n" +
    "for _i in 0..1024:\n" +
    "    last_id = rt_host_gpu_queue_emit(2, 1, 8, 1)\n" +
    "    if last_id > 0:\n" +
    "        accepted = accepted + 1\n" +
    "val overflow_id = rt_host_gpu_queue_emit(2, 1, 8, 1)\n" +
    "val queued = rt_host_gpu_queue_packet_count()\n" +
    "val drained = rt_host_gpu_queue_drain(1024)\n" +
    "val after_drain_id = rt_host_gpu_queue_emit(2, 1, 8, 1)\n" +
    "print(\"accepted=\" + str(accepted))\n" +
    "print(\"last_id=\" + str(last_id))\n" +
    "print(\"overflow_id=\" + str(overflow_id))\n" +
    "print(\"queued=\" + str(queued))\n" +
    "print(\"drained=\" + str(drained))\n" +
    "print(\"after_drain_id=\" + str(after_drain_id))\n" +
    "print(\"status=\" + str(rt_host_gpu_queue_last_status()))\n"

val (stdout, stderr, code) = run_source_native("gpu_lane_native_queue_capacity", source)
val output = combined_output(stdout, stderr)

expect(code).to_equal(0)
expect(output).to_contain("accepted=1024")
expect(output).to_contain("last_id=1024")
expect(output).to_contain("overflow_id=0")
expect(output).to_contain("queued=1024")
expect(output).to_contain("drained=1024")
expect(output).to_contain("after_drain_id=1025")
expect(output).to_contain("status=1")
```

</details>

#### should record host to GPU to host callback marker sequence

- Run host, GPU, and host callbacks through target.later lane markers
- "extern fn rt host gpu lane reset
- "extern fn rt host gpu lane event count
- "extern fn rt host gpu lane begin count
- "extern fn rt host gpu lane end count
- "extern fn rt host gpu lane last lane
- "extern fn rt host gpu lane last phase
- "extern fn rt host gpu active backend handle set
- "extern fn rt host gpu queue packet count
- "extern fn rt host gpu queue submitted count
- "extern fn rt host gpu queue completed count
- "extern fn rt host gpu queue in flight count
- "extern fn rt host gpu queue last backend handle
- "    fn later
- "        pass do nothing
- "rt host gpu lane reset
- "rt host gpu active backend handle set
- "val target = Target
- "target later
- "target later
- "target later
- "print
- "print
- "print
- "print
- "print
- "print
- "print
- "print
- "print
- "print
- "print
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 54 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run host, GPU, and host callbacks through target.later lane markers")
val source =
    "extern fn rt_host_gpu_lane_reset()\n" +
    "extern fn rt_host_gpu_lane_event_count() -> i64\n" +
    "extern fn rt_host_gpu_lane_begin_count() -> i64\n" +
    "extern fn rt_host_gpu_lane_end_count() -> i64\n" +
    "extern fn rt_host_gpu_lane_last_lane() -> i64\n" +
    "extern fn rt_host_gpu_lane_last_phase() -> i64\n" +
    "extern fn rt_host_gpu_active_backend_handle_set(backend_handle: i64) -> i64\n" +
    "extern fn rt_host_gpu_queue_packet_count() -> i64\n" +
    "extern fn rt_host_gpu_queue_submitted_count() -> i64\n" +
    "extern fn rt_host_gpu_queue_completed_count() -> i64\n" +
    "extern fn rt_host_gpu_queue_in_flight_count() -> i64\n" +
    "extern fn rt_host_gpu_queue_last_backend_handle() -> i64\n\n" +
    "class Target:\n" +
    "    fn later():\n" +
    "        pass_do_nothing(\"lane callback sequence\")\n\n" +
    "rt_host_gpu_lane_reset()\n" +
    "rt_host_gpu_active_backend_handle_set(9)\n" +
    "val target = Target()\n" +
    "var callbacks = 0\n" +
    "target.later() host \\:\n" +
    "    callbacks = callbacks + 1\n" +
    "target.later() gpu \\:\n" +
    "    callbacks = callbacks + 1\n" +
    "target.later() host \\:\n" +
    "    callbacks = callbacks + 1\n" +
    "print(\"callbacks=\" + str(callbacks))\n" +
    "print(\"events=\" + str(rt_host_gpu_lane_event_count()))\n" +
    "print(\"begin=\" + str(rt_host_gpu_lane_begin_count()))\n" +
    "print(\"end=\" + str(rt_host_gpu_lane_end_count()))\n" +
    "print(\"lane=\" + str(rt_host_gpu_lane_last_lane()))\n" +
    "print(\"phase=\" + str(rt_host_gpu_lane_last_phase()))\n" +
    "print(\"queue=\" + str(rt_host_gpu_queue_packet_count()))\n" +
    "print(\"submitted=\" + str(rt_host_gpu_queue_submitted_count()))\n" +
    "print(\"completed=\" + str(rt_host_gpu_queue_completed_count()))\n" +
    "print(\"in_flight=\" + str(rt_host_gpu_queue_in_flight_count()))\n" +
    "print(\"backend=\" + str(rt_host_gpu_queue_last_backend_handle()))\n"

val (stdout, stderr, code) = run_source("host_gpu_host_runtime_markers", source)
val output = combined_output(stdout, stderr)

expect(code).to_equal(0)
expect(output).to_contain("callbacks=3")
expect(output).to_contain("events=6")
expect(output).to_contain("begin=3")
expect(output).to_contain("end=3")
expect(output).to_contain("lane=1")
expect(output).to_contain("phase=2")
expect(output).to_contain("queue=1")
expect(output).to_contain("submitted=1")
expect(output).to_contain("completed=1")
expect(output).to_contain("in_flight=0")
expect(output).to_contain("backend=9")
```

</details>

#### should accept host-owned semantic mutation in a host lane

- Check that semantic state mutation remains legal on the host lane
- "    fn is checked
- "var state = WidgetState
- "target later
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check that semantic state mutation remains legal on the host lane")
val source = host_gpu_fixture(
    "class WidgetState:\n" +
    "    checked: bool\n" +
    "    fn is_checked() -> bool: self.checked\n\n" +
    "var state = WidgetState(checked: false)\n" +
    "target.later() host \\:\n" +
    "    state.checked = true\n"
)

val (stdout, stderr, code) = check_source("host_semantic_mutation", source)

expect(code).to_equal(0)
expect(combined_output(stdout, stderr)).to_contain("All checks passed")
```

</details>

#### should accept GPU render and effect batching with packet bounds

- Check that GPU lane work is expressed as a coarse render/effect batch
- "packet target later
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check that GPU lane work is expressed as a coarse render/effect batch")
val source = host_gpu_fixture(
    "packet_target.later(max_packet: 4096) gpu \\:\n" +
    "    val render_batch = \"DrawIR:rect, glyph, image\"\n" +
    "    val effect_batch = \"blur, opacity, composite\"\n" +
    "    val batch_kind = render_batch + \" | \" + effect_batch\n"
)

val (stdout, stderr, code) = check_source("gpu_render_effect_batch", source)

expect(code).to_equal(0)
expect(combined_output(stdout, stderr)).to_contain("All checks passed")
```

</details>

#### should reject GPU semantic mutation with a diagnostic

- Validate that a GPU lane cannot commit host-owned semantic state
   - Expected: result.ok is false
   - Expected: result.estimated_ms equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate that a GPU lane cannot commit host-owned semantic state")
val result = engine2d_host_gpu_lane_schedule(
    ENGINE2D_HOST_GPU_LANE_HOST,
    ENGINE2D_HOST_GPU_LANE_GPU,
    "draw_ir_delta",
    128,
    512,
    true,
    false,
    true,
    8
)

expect(result.ok).to_equal(false)
expect(result.diagnostic).to_contain("GPU lane cannot mutate host semantic state")
expect(result.estimated_ms).to_equal(8)
```

</details>

<details>
<summary>Advanced: should warn for per-widget GPU dispatch inside a loop</summary>

#### should warn for per-widget GPU dispatch inside a loop

- Validate that repeated widget-level GPU later calls are diagnosed
   - Expected: result.ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate that repeated widget-level GPU later calls are diagnosed")
val result = engine2d_host_gpu_lane_schedule(
    ENGINE2D_HOST_GPU_LANE_HOST,
    ENGINE2D_HOST_GPU_LANE_GPU,
    "draw_ir_delta",
    128,
    512,
    false,
    true,
    true,
    8
)

expect(result.ok).to_equal(false)
expect(result.diagnostic).to_contain("per-widget GPU dispatch")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/host_gpu_lane.md](doc/02_requirements/feature/host_gpu_lane.md)
- **Plan:** [doc/03_plan/sys_test/host_gpu_lane.md](doc/03_plan/sys_test/host_gpu_lane.md)
- **Design:** [doc/05_design/host_gpu_lane.md](doc/05_design/host_gpu_lane.md)
- **Research:** [doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md](doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md)


</details>
