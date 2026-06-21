# Ide Plugin Manifest Harden Specification

> <details>

<!-- sdn-diagram:id=ide_plugin_manifest_harden_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ide_plugin_manifest_harden_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ide_plugin_manifest_harden_spec -> std
ide_plugin_manifest_harden_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ide_plugin_manifest_harden_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ide Plugin Manifest Harden Specification

## Scenarios

### plugin_manifest: validation catches empty name and duplicate entries

#### standard IDE plugin entries are all valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ide_plugin_manifest_is_valid()).to_equal(true)
```

</details>

#### manifest validate returns empty string for valid entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entries = ide_plugin_entries()
expect(ide_plugin_manifest_validate(entries)).to_equal("")
```

</details>

#### roundtrip count matches entry count

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = ide_plugin_manifest_probe()
expect(probe.roundtrip_count).to_equal(probe.entry_count)
```

</details>

#### all manifest names are non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = ide_plugin_manifest_probe()
var all_nonempty = true
for name in probe.names:
    if name == "":
        all_nonempty = false
expect(all_nonempty).to_equal(true)
```

</details>

#### entry count is positive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = ide_plugin_manifest_probe()
expect(probe.entry_count > 0).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ide/ide_plugin_manifest_harden_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- plugin_manifest: validation catches empty name and duplicate entries

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
