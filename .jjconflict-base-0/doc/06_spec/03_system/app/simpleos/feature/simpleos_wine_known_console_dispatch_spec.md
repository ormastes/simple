# Simpleos Wine Known Console Dispatch Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_known_console_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_known_console_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_known_console_dispatch_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_known_console_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Known Console Dispatch Specification

## Scenarios

### SimpleOS Wine known-console dispatch

### REQ-018: bounded known-console process dispatch plan

#### should decode a known console dispatch plan after CPU preflight

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val dispatch = wine_process_plan_known_console_dispatch(plan, wine_known_hello_exe_fixture_bytes(), 8, wine_cpu_execution_evidence_text(wine_cpu_execution_evidence_all_ready()))
expect(dispatch.ok).to_equal(true)
expect(dispatch.instruction_count).to_equal(6)
expect(dispatch.call_sequence).to_equal("GetStdHandle WriteFile ExitProcess")
expect(dispatch.call_count).to_equal(3)
expect(dispatch.status).to_equal("dispatch-planned")
```

</details>

#### should require PEB/TEB VM byte-write readback before known-console dispatch planning

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val dispatch = wine_process_plan_known_console_dispatch_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 8, wine_cpu_execution_evidence_text(wine_cpu_execution_evidence_all_ready()), vm_writes)

expect(dispatch.ok).to_equal(true)
expect(dispatch.instruction_count).to_equal(6)
expect(dispatch.call_sequence).to_equal("GetStdHandle WriteFile ExitProcess")
expect(dispatch.call_count).to_equal(3)
expect(dispatch.status).to_equal("dispatch-planned")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_known_console_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS Wine known-console dispatch
- REQ-018: bounded known-console process dispatch plan

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
