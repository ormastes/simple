# Svim Specification

> <details>

<!-- sdn-diagram:id=svim_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=svim_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

svim_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=svim_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Svim Specification

## Scenarios

### svim feature spec

#### keeps one shared core for shell-facing editor behavior

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = "shared session buffer window tabpage command rpc"
expect(contract).to_contain("shared")
expect(contract).to_contain("session")
expect(contract).to_contain("rpc")
```

</details>

#### ships a host-side TUI shell first

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shell_contract = "host tui snapshot shell first integration target"
expect(shell_contract).to_contain("host")
expect(shell_contract).to_contain("tui")
expect(shell_contract).to_contain("first")
```

</details>

#### tracks diagnostics and overlays through stable anchors

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val anchor_contract = "anchor extmark diagnostics overlay survives edits"
expect(anchor_contract).to_contain("anchor")
expect(anchor_contract).to_contain("diagnostics")
expect(anchor_contract).to_contain("survives edits")
```

</details>

#### supports buffers windows and tabpages as separate concepts

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val workspace_contract = "buffer window tabpage separate reusable session"
expect(workspace_contract).to_contain("buffer")
expect(workspace_contract).to_contain("window")
expect(workspace_contract).to_contain("tabpage")
```

</details>

#### exposes a message-based rpc control path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rpc_contract = "message based rpc request response control api"
expect(rpc_contract).to_contain("rpc")
expect(rpc_contract).to_contain("request")
expect(rpc_contract).to_contain("response")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/native_build/feature/svim_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- svim feature spec

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
