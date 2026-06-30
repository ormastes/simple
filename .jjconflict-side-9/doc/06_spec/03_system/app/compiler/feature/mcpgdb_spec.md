# Mcpgdb Specification

> <details>

<!-- sdn-diagram:id=mcpgdb_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcpgdb_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcpgdb_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcpgdb_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcpgdb Specification

## Scenarios

### mcpgdb feature spec

#### exposes both debug and clangd tool families

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_tools_list("1")
expect(response).to_contain("\"debug_session_create\"")
expect(response).to_contain("\"clangd_open\"")
expect(response).to_contain("\"clangd_definition\"")
expect(response).to_contain("\"debug_disconnect\"")
expect(response).to_contain("\"debug_restart\"")
expect(response).to_contain("\"register_write\"")
expect(response).to_contain("\"memory_write\"")
```

</details>

#### blocks dangerous raw commands by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decision = evaluate_command_rule("gdb", "set $pc=0x1000", false, false)
expect(decision.allowed).to_equal(false)
```

</details>

#### allows explicit dangerous writes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decision = evaluate_command_rule("gdb", "set $pc=0x1000", true, false)
expect(decision.allowed).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/compiler/feature/mcpgdb_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- mcpgdb feature spec

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
