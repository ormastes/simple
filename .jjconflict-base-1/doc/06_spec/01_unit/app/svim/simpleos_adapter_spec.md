# Simpleos Adapter Specification

> 1. var session = SvimSession new

<!-- sdn-diagram:id=simpleos_adapter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_adapter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_adapter_spec -> std
simpleos_adapter_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_adapter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Adapter Specification

## Scenarios

### svim simpleos adapter

#### dispatches host-style aliases through the shared session

1. var session = SvimSession new
2. session execute named
3. session execute named
4. expect session current cursor


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = SvimSession.new()
session.execute_named("set-mode", "insert", 1, "")
val insert = svim_simpleos_dispatch(session, "hello")
expect insert.ok to_equal true
session.execute_named("set-mode", "normal", 1, "")
val search = svim_simpleos_dispatch(session, "search hello")
expect search.ok to_equal true
expect session.current_cursor().col to_equal 0
```

</details>

#### returns the shared session snapshot for rendering surfaces

1. var session = SvimSession new
2. session execute named
3. session execute named


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = SvimSession.new()
session.execute_named("set-mode", "insert", 1, "")
session.execute_named("insert-text", "hello", 1, "")
val snapshot = svim_simpleos_snapshot(session)
expect snapshot to_contain "svim INSERT"
expect snapshot to_contain "hello"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/svim/simpleos_adapter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- svim simpleos adapter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
