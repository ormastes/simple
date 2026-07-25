# Simpleos Wine Known Console Execution Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_known_console_execution_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_known_console_execution_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_known_console_execution_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_known_console_execution_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Known Console Execution Specification

## Scenarios

### SimpleOS Wine known-console execution

### REQ-019: bounded known-console process execution

#### should execute a decoded known-console process session

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val execution = wine_process_execute_known_console(plan, wine_known_hello_exe_fixture_bytes(), 8, wine_cpu_execution_evidence_text(wine_cpu_execution_evidence_all_ready()))
expect(execution.ok).to_equal(true)
expect(execution.stdout).to_equal("Hello from SimpleOS Wine\n")
expect(execution.exit_code).to_equal(0)
expect(execution.status).to_equal("known-console-executed")
```

</details>

#### should block known-console process execution before CPU preflight

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val execution = wine_process_execute_known_console(plan, wine_known_hello_exe_fixture_bytes(), 8, "")
expect(execution.ok).to_equal(false)
expect(execution.error).to_equal("missing-thread-context")
```

</details>

#### should require PEB/TEB VM byte-write readback before known-console execution

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val execution = wine_process_execute_known_console_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 8, wine_cpu_execution_evidence_text(wine_cpu_execution_evidence_all_ready()), vm_writes)
expect(execution.ok).to_equal(true)
expect(execution.stdout).to_equal("Hello from SimpleOS Wine\n")
expect(execution.exit_code).to_equal(0)
expect(execution.status).to_equal("known-console-executed")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_known_console_execution_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS Wine known-console execution
- REQ-019: bounded known-console process execution

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
