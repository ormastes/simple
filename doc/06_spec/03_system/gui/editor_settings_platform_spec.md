# Editor Settings Platform Specification

> <details>

<!-- sdn-diagram:id=editor_settings_platform_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_settings_platform_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_settings_platform_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_settings_platform_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Settings Platform Specification

## Scenarios

### platform_config_get_by_key

#### exists in platform.spl

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/platform.spl")
expect(src.contains("fn platform_config_get_by_key")).to_equal(true)
```

</details>

#### accepts PlatformConfig and key text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/platform.spl")
expect(src.contains("platform_config_get_by_key(config: PlatformConfig, key: text)")).to_equal(true)
```

</details>

### platform_config_set_by_key

#### exists in platform.spl

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/platform.spl")
expect(src.contains("fn platform_config_set_by_key")).to_equal(true)
```

</details>

#### returns PlatformConfig

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/platform.spl")
expect(src.contains("platform_config_set_by_key(config: PlatformConfig, key: text, value: text) -> PlatformConfig")).to_equal(true)
```

</details>

### simpleos_settings_schema

#### exists in simpleos_adapter.spl

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/simpleos_adapter.spl")
expect(src.contains("fn simpleos_settings_schema")).to_equal(true)
```

</details>

#### returns filtered schema for simpleos platform

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/editor/simpleos_adapter.spl")
expect(src.contains("settings_filter_by_platform(full_settings_schema(), \"simpleos\")")).to_equal(true)
```

</details>

### Platform category in full_settings_schema

#### settings_schema.spl contains Platform category descriptor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("category: \"Platform\"")).to_equal(true)
```

</details>

#### max_open_files setting exists in schema

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("key: \"max_open_files\"")).to_equal(true)
```

</details>

#### file_watcher_enabled is desktop-only in schema

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("key: \"file_watcher_enabled\"")).to_equal(true)
expect(src.contains("key: \"file_watcher_debounce_ms\"")).to_equal(true)
expect(src.contains("key: \"file_watcher_ignore_globs\"")).to_equal(true)
expect(src.contains("platform: \"desktop\"")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_settings_platform_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- platform_config_get_by_key
- platform_config_set_by_key
- simpleos_settings_schema
- Platform category in full_settings_schema

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
