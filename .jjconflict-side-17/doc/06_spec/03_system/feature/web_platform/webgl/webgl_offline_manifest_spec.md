# Webgl Offline Manifest Specification

> <details>

<!-- sdn-diagram:id=webgl_offline_manifest_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=webgl_offline_manifest_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

webgl_offline_manifest_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=webgl_offline_manifest_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Webgl Offline Manifest Specification

## Scenarios

### WebGL offline conformance manifest

#### fixture exists and declares a non-empty offline slice

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = _read(MANIFEST_PATH)
expect(rt_file_exists(MANIFEST_PATH)).to_equal(true)
expect(manifest.contains("(webgl_offline_conformance_manifest")).to_equal(true)
expect(_entry_count(manifest)).to_equal(5)
```

</details>

#### keeps every manifest entry offline deterministic and inline

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = _read(MANIFEST_PATH)
expect(_all_entries_have_offline_contract(manifest)).to_equal(true)
```

</details>

#### contains no external URL references anywhere in the fixture

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = _read(MANIFEST_PATH)
expect(_has_external_url(manifest)).to_equal(false)
```

</details>

#### uses unique deterministic ids for each entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manifest = _read(MANIFEST_PATH)
expect(_all_entry_ids_are_unique(manifest)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/web_platform/webgl/webgl_offline_manifest_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WebGL offline conformance manifest

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
