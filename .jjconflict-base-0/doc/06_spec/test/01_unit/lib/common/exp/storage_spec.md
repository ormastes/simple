# Storage Specification

> <details>

<!-- sdn-diagram:id=storage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=storage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

storage_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=storage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Storage Specification

## Scenarios

### Event

#### keeps common experiment storage event and blob APIs available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = exp_source("storage")

expect(source).to_contain("struct Event")
expect(source).to_contain("pub fn append_event(run_id: text, event: Event)")
expect(source).to_contain("pub fn read_events(run_id: text) -> [Event]")
expect(source).to_contain("pub fn store_blob(data: text) -> text")
expect(source).to_contain("pub fn read_blob(hash: text) -> text?")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/exp/storage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Event

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
