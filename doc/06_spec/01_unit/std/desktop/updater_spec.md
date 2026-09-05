# Updater Specification

> <details>

<!-- sdn-diagram:id=updater_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=updater_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

updater_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=updater_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Updater Specification

## Scenarios

### Desktop Auto-Updater API

#### creates UpdateInfo struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = UpdateInfo(version: "1.0.1", url: "https://example.com/update", release_notes: "Bug fixes", mandatory: false)
expect info.version == "1.0.1"
expect info.mandatory == false
```

</details>

#### creates UpdateConfig struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = UpdateConfig(feed_url: "https://example.com/feed", current_version: "1.0.0", auto_download: true)
expect config.auto_download == true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/desktop/updater_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Desktop Auto-Updater API

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
