# Session Adapter Nullable Lookup Specification

> Tests covering Adapter registry nullable lookup contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Session Adapter Nullable Lookup Specification

## Scenarios

### Adapter registry nullable lookup contract

#### returns nil when no adapter kind is registered

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = adapter_registry_new()
expect(registry.find_by_kind(SESSION_KIND_LOCAL)).to_be_nil()
```

</details>

#### returns nil when no adapter handles the requested metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val registry = adapter_registry_new()
val meta = test_session_meta_default("test/missing_adapter_spec.spl")
expect(registry.find_for_meta(meta)).to_be_nil()
```

</details>

#### preserves the selected adapter kind and name

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var registry = adapter_registry_new()
registry.register(session_adapter_new(SESSION_KIND_LOCAL, "local"))
registry.register(session_adapter_new(SESSION_KIND_CONTAINER, "container"))
val adapter = registry.find_by_kind(SESSION_KIND_CONTAINER)
expect(adapter.?).to_equal(true)
if adapter.?:
    expect(adapter.kind).to_equal(SESSION_KIND_CONTAINER)
    expect(adapter.name).to_equal("container")
```

</details>

#### returns nil for a missing kind in a populated registry

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var registry = adapter_registry_new()
registry.register(session_adapter_new(SESSION_KIND_CONTAINER, "container"))
expect(registry.find_by_kind(SESSION_KIND_LOCAL)).to_be_nil()
```

</details>

#### selects an adapter through the existing metadata predicate

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var registry = adapter_registry_new()
registry.register(session_adapter_new(SESSION_KIND_CONTAINER, "container"))
registry.register(session_adapter_new(SESSION_KIND_LOCAL, "local"))
val meta = test_session_meta_default("test/local_adapter_spec.spl")
val adapter = registry.find_for_meta(meta)
expect(adapter.?).to_equal(true)
if adapter.?:
    expect(adapter.kind).to_equal(SESSION_KIND_LOCAL)
    expect(adapter.name).to_equal("local")
```

</details>

#### rejects unsupported metadata in a populated registry

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var registry = adapter_registry_new()
registry.register(session_adapter_new(SESSION_KIND_CONTAINER, "container"))
val meta = test_session_meta_default("test/local_adapter_spec.spl")
expect(registry.find_for_meta(meta)).to_be_nil()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_daemon/session_adapter_nullable_lookup_spec.spl` |
| Updated | 2026-10-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Adapter registry nullable lookup contract.
- Adapter registry nullable lookup contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
