# Dap Specification

> <details>

<!-- sdn-diagram:id=dap_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dap_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dap_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dap_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dap Specification

## Scenarios

### DAP

#### defines core DAP protocol response and event types

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val protocol = rt_file_read_text("src/lib/nogc_sync_mut/dap/protocol.spl")

expect(protocol).to_contain("class Source:")
expect(protocol).to_contain("class Breakpoint:")
expect(protocol).to_contain("class SourceBreakpoint:")
expect(protocol).to_contain("class StackFrame:")
expect(protocol).to_contain("class Thread:")
expect(protocol).to_contain("class Scope:")
expect(protocol).to_contain("class Variable:")
expect(protocol).to_contain("class DapResponse:")
expect(protocol).to_contain("class DapEvent:")
```

</details>

#### defines transport and breakpoint manager contracts

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val transport = rt_file_read_text("src/lib/nogc_sync_mut/dap/transport.spl")
val breakpoints = rt_file_read_text("src/lib/nogc_sync_mut/dap/breakpoints.spl")

expect(transport).to_contain("fn write_response(request_seq: Int, success: Bool, command: String, body: Option<Dict>)")
expect(transport).to_contain("fn write_event(event: String, body: Dict)")
expect(breakpoints).to_contain("class BreakpointEntry:")
expect(breakpoints).to_contain("class BreakpointManager:")
expect(breakpoints).to_contain("static fn new() -> BreakpointManager:")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/dap/dap_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DAP

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
