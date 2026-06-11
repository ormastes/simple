# Wine Gui Hello Specification

> <details>

<!-- sdn-diagram:id=wine_gui_hello_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_gui_hello_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_gui_hello_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_gui_hello_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Gui Hello Specification

## Scenarios

### Wine GUI hello milestone

#### blocks before the executable has an OS-backed VM process

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val space = wine_vm_process_space_new(0, 0, "")
val result = wine_gui_hello_probe_vm(wine_known_hello_exe_fixture_bytes(), wine_hello_fixture_precondition_manifest(), wine_hello_fixture_execution_evidence_struct(), space, 0x400000, 0x700000, 0x2000, 0x1000)
expect(result.status).to_equal("blocked")
expect(result.error).to_contain("missing-os-process")
```

</details>

#### executes the controlled hello path through SimpleOS-backed X11 evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val space = wine_vm_process_space_new(2, 1002, "pid fs ipc net capability")
val result = wine_gui_hello_probe_vm(wine_known_hello_exe_fixture_bytes(), wine_hello_fixture_precondition_manifest(), wine_hello_fixture_execution_evidence_struct(), space, 0x400000, 0x700000, 0x2000, 0x1000)
expect(result.status).to_equal("executed")
expect(result.stdout).to_equal("Hello from SimpleOS Wine\n")
expect(result.window_title).to_equal("SimpleOS Wine GUI Hello")
expect(result.window_text).to_equal("Hello from SimpleOS Wine\n")
expect(result.window_id).to_equal("wine-gui-hello")
expect(result.framebuffer_checksum).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_gui_hello_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine GUI hello milestone

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
