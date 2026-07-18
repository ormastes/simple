# Plugins Specification

> _Word, PPT, and Excel are registered as distinct plugin entries._

<!-- sdn-diagram:id=plugins_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=plugins_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

plugins_spec -> std
plugins_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=plugins_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Plugins Specification

## Scenarios

### office plugins: three separate plugins on the shared module
_Word, PPT, and Excel are registered as distinct plugin entries._

#### registers exactly three office plugins

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(office_plugin_names().len()).to_equal(3)
```

</details>

#### names the word, ppt, and excel plugins

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = office_plugin_names()
expect(names).to_contain("office-word")
expect(names).to_contain("office-ppt")
expect(names).to_contain("office-excel")
```

</details>

### office plugins: manifest round-trips and validates

#### round-trips through the registry manifest format

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# plugin_count is the number of entries parsed back out of the manifest;
# equalling the 3 input entries proves the manifest round-trips.
val probe = office_plugin_manifest_probe()
expect(probe.plugin_count).to_equal(3)
```

</details>

#### is a well-formed manifest (validation returns no error)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = office_plugin_validate(office_plugin_entries())
expect(err).to_equal("")
```

</details>

#### the serialized manifest names each plugin

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = office_plugin_manifest_probe()
val manifest = probe.manifest_text
expect(manifest).to_contain("office-word")
expect(manifest).to_contain("office-ppt")
expect(manifest).to_contain("office-excel")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/plugins_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- office plugins: three separate plugins on the shared module
- office plugins: manifest round-trips and validates

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
