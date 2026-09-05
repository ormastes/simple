# Server Hooks Integration Specification

> <details>

<!-- sdn-diagram:id=server_hooks_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=server_hooks_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

server_hooks_integration_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=server_hooks_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Server Hooks Integration Specification

## Scenarios

### DAP Server Hooks Integration

#### wires DAP server state to adapter and protocol handlers

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = rt_file_read_text("src/lib/nogc_sync_mut/dap/server.spl")

expect(server).to_contain("class DapServer:")
expect(server).to_contain("adapter: DebugAdapter")
expect(server).to_contain("static fn _create_with_adapter(adapter: DebugAdapter) -> DapServer:")
expect(server).to_contain("static fn with_adapter(adapter: DebugAdapter) -> DapServer:")
expect(server).to_contain("fn handle_initialize(request_seq: Int, command: String, arguments: Option<Dict>)")
expect(server).to_contain("fn handle_launch(request_seq: Int, command: String, arguments: Option<Dict>)")
expect(server).to_contain("fn handle_configuration_done(request_seq: Int, command: String)")
```

</details>

#### integrates breakpoints, stack, variables, and stepping handlers

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = rt_file_read_text("src/lib/nogc_sync_mut/dap/server.spl")
val handlers = rt_file_read_text("src/lib/nogc_sync_mut/dap/dap_handlers.spl")

expect(server).to_contain("fn handle_stack_trace(request_seq: Int, command: String, arguments: Option<Dict>)")
expect(server).to_contain("fn handle_scopes(request_seq: Int, command: String, arguments: Option<Dict>)")
expect(server).to_contain("fn handle_continue(request_seq: Int, command: String, arguments: Option<Dict>)")
expect(handlers).to_contain("fn handle_set_breakpoints(request_seq: Int, command: String, arguments: Option<Dict>)")
expect(handlers).to_contain("self.adapter.set_breakpoint_rich(")
expect(handlers).to_contain("fn handle_variables(request_seq: Int, command: String, arguments: Option<Dict>)")
expect(handlers).to_contain("fn handle_evaluate(request_seq: Int, command: String, arguments: Option<Dict>)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/dap/server_hooks_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DAP Server Hooks Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
