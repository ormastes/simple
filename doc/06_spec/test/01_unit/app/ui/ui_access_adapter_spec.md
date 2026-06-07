# Ui Access Adapter Specification

> <details>

<!-- sdn-diagram:id=ui_access_adapter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ui_access_adapter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ui_access_adapter_spec -> std
ui_access_adapter_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ui_access_adapter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ui Access Adapter Specification

## Scenarios

### UiAccess adapter contracts

#### constructs additive source metadata, issues, and envelopes

<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = _source()
expect(source.source_kind).to_equal("session")
expect(source.source_id).to_equal("main")
expect(source.source_name).to_equal("Main Session")
expect(source.source_uri).to_equal("session://main")
expect(source.source_version).to_equal("1")

val issue = ui_access_issue_error("missing_surface", "surface not found", "main", "snapshot", "no active surface")
expect(ui_access_issue_is_error(issue)).to_equal(true)
expect(ui_access_issue_is_warning(issue)).to_equal(false)
expect(issue.code).to_equal("missing_surface")
expect(issue.subject).to_equal("snapshot")
expect(issue.detail).to_equal("no active surface")

val warning = ui_access_issue_warning("adapter.disabled", "adapter disabled", "main", "snapshot", "registry entry disabled")
expect(ui_access_issue_is_warning(warning)).to_equal(true)

val snapshot = ui_access_empty_snapshot("NORMAL", "main", [])
val target = _target()
val envelope = ui_access_snapshot_envelope(source, target, snapshot, [issue, warning])
expect(envelope.source.source_id).to_equal("main")
expect(envelope.target.operation).to_equal("snapshot")
expect(envelope.snapshot.mode).to_equal("NORMAL")
expect(envelope.snapshot.active_surface).to_equal("main")
expect(envelope.issues.len()).to_equal(2)
```

</details>

#### creates an empty envelope from a target without modifying the snapshot contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = ui_access_source_meta_empty("session", "main")
val target = ui_access_adapter_target_for_snapshot(source, "NORMAL", "main")
val envelope = ui_access_snapshot_envelope_empty(target)
expect(envelope.source.source_id).to_equal("main")
expect(envelope.snapshot.protocol_version).to_equal(1)
expect(envelope.snapshot.mode).to_equal("NORMAL")
expect(envelope.snapshot.active_surface).to_equal("main")
expect(envelope.snapshot.surfaces.len()).to_equal(0)
expect(envelope.snapshot.nodes.len()).to_equal(0)
expect(envelope.issues.len()).to_equal(0)
```

</details>

#### returns an empty snapshot envelope from the null adapter

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ui_access_null_adapter_new()
expect(adapter.name()).to_equal("ui_access_null_adapter")
expect(adapter.adapter_kind()).to_equal("null")
val target = ui_access_adapter_target(_source(), "snapshot", "NORMAL", "main", "", "", "", "", false, 0)
expect(adapter.supports(target)).to_equal(true)
expect(adapter.describe_target(target)).to_equal("snapshot:session/main")
val envelope = adapter.adapt(target)
expect(envelope.snapshot.protocol_version).to_equal(1)
expect(envelope.snapshot.mode).to_equal("NORMAL")
expect(envelope.snapshot.active_surface).to_equal("main")
expect(envelope.snapshot.surfaces.len()).to_equal(0)
expect(envelope.snapshot.nodes.len()).to_equal(0)
expect(envelope.issues.len()).to_equal(0)
```

</details>

#### registers and resolves adapter targets in the registry

1. var registry = ui access adapter registry new
   - Expected: registry.entry_count() equals `0`
   - Expected: registry.has_target(target) is false
2. registry register target
   - Expected: registry.entry_count() equals `1`
   - Expected: registry.has_target(target) is true
   - Expected: registry.adapter_name_for(target) equals `ui_access_null_adapter`
   - Expected: registry.adapter_kind_for(target) equals `null`
   - Expected: resolved != nil is true
   - Expected: resolved.target.source.source_id equals `main`
   - Expected: resolved.adapter_name equals `ui_access_null_adapter`
   - Expected: resolved.enabled is true
   - Expected: envelope.snapshot.protocol_version equals `1`
   - Expected: envelope.issues.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var registry = ui_access_adapter_registry_new()
val target = ui_access_adapter_target(_source(), "snapshot", "NORMAL", "main", "", "", "", "", false, 0)
expect(registry.entry_count()).to_equal(0)
expect(registry.has_target(target)).to_equal(false)

registry.register_target(target, "null", "ui_access_null_adapter", true)
expect(registry.entry_count()).to_equal(1)
expect(registry.has_target(target)).to_equal(true)
expect(registry.adapter_name_for(target)).to_equal("ui_access_null_adapter")
expect(registry.adapter_kind_for(target)).to_equal("null")

val resolved = registry.resolve_target(target)
expect(resolved != nil).to_equal(true)
expect(resolved.target.source.source_id).to_equal("main")
expect(resolved.adapter_name).to_equal("ui_access_null_adapter")
expect(resolved.enabled).to_equal(true)

val envelope = registry.adapt(target)
expect(envelope.snapshot.protocol_version).to_equal(1)
expect(envelope.issues.len()).to_equal(0)
```

</details>

#### replaces an existing registry entry for the same source and operation

1. var registry = UiAccessAdapterRegistry new
2. registry register target
3. registry register target
   - Expected: registry.entry_count() equals `1`
   - Expected: registry.adapter_name_for(target) equals `ui_access_null_adapter_v2`
   - Expected: registry.adapter_kind_for(target) equals `null`
   - Expected: envelope.snapshot.mode equals `NORMAL`
   - Expected: envelope.issues.len() equals `1`
   - Expected: envelope.issues[0].code equals `adapter.disabled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var registry = UiAccessAdapterRegistry.new()
val target = ui_access_adapter_target(_source(), "snapshot", "NORMAL", "main", "", "", "", "", false, 0)
registry.register_target(target, "null", "ui_access_null_adapter", true)
registry.register_target(target, "null", "ui_access_null_adapter_v2", false)
expect(registry.entry_count()).to_equal(1)
expect(registry.adapter_name_for(target)).to_equal("ui_access_null_adapter_v2")
expect(registry.adapter_kind_for(target)).to_equal("null")
val envelope = registry.adapt(target)
expect(envelope.snapshot.mode).to_equal("NORMAL")
expect(envelope.issues.len()).to_equal(1)
expect(envelope.issues[0].code).to_equal("adapter.disabled")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/ui_access_adapter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- UiAccess adapter contracts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
