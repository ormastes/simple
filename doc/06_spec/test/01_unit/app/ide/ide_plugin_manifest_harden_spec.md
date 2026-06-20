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
| 10 | 10 | 0 | 0 |

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

#### manifest entry count follows the capability registry

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = ide_plugin_manifest_probe()
expect(probe.entry_count).to_equal(ide_capability_count())
```

</details>

#### manifest records first-seen contribution kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = ide_plugin_manifest_probe()
expect(probe.contribution_kind_count).to_equal(4)
expect(probe.contribution_kinds.join(",")).to_equal("office-app,document-renderer,dashboard,database")
expect(ide_plugin_contribution_kinds().len()).to_equal(probe.contribution_kind_count)
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

#### standard IDE plugin entries advertise two well-formed function symbols

- functions = functions + entry functions join


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var functions = ""
for entry in ide_plugin_entries():
    expect(entry.functions.len()).to_equal(2)
    val raw_suffix = entry.name.slice(4, entry.name.len())
    val suffix = raw_suffix.replace("-", "_")
    functions = functions + entry.functions.join(",") + "\n"
    expect(functions).to_contain("ide_capability_" + suffix)
    expect(functions).to_contain("ide_feature_check_" + suffix)
```

</details>

#### manifest validation rejects malformed function symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val malformed = plugin_entry_new("ide.markdown", "builtin:std.editor.render.md_renderer", "0.1.0", ["ide_capability_markdown", ""])
expect(ide_plugin_manifest_validate([malformed])).to_equal("manifest error: entry 'ide.markdown' has empty function")
```

</details>

#### manifest validation rejects empty plugin libraries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val malformed = plugin_entry_new("ide.markdown", "", "0.1.0", ["ide_capability_markdown", "ide_feature_check_markdown"])
expect(ide_plugin_manifest_validate([malformed])).to_equal("manifest error: entry 'ide.markdown' has empty library")
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
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
