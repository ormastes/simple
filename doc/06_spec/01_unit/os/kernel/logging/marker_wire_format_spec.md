# Marker Wire Format Specification

> <details>

<!-- sdn-diagram:id=marker_wire_format_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=marker_wire_format_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

marker_wire_format_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=marker_wire_format_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Marker Wire Format Specification

## Scenarios

### markers.find_spec strict prefix matching

#### matches a bare '[boot] entry' marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "[boot] entry"
val spec = find_spec(raw)
expect(spec.is_nil()).to_equal(false)
```

</details>

#### does NOT match '[INFO] [boot] entry' (the regression shape)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw_with_level = "[INFO] [boot] entry"
val spec = find_spec(raw_with_level)
expect(spec.is_nil()).to_equal(true)
```

</details>

#### rejects unknown namespace prefixes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "[nonsense] event"
val spec = find_spec(raw)
expect(spec.is_nil()).to_equal(true)
```

</details>

### validate() rejects level-prefixed markers

#### validates a bare marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = validate("[boot] entry")
expect(result.is_ok()).to_equal(true)
```

</details>

#### rejects the same marker with an [INFO] prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = validate("[INFO] [boot] entry")
expect(result.is_ok()).to_equal(false)
```

</details>

### log_level_name composition (log_info wire format)

#### INFO prefix is exactly '[INFO]'

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val level_token = "[" + log_level_name(LOG_INFO) + "]"
expect(level_token).to_equal("[INFO]")
```

</details>

### namespace_prefix / marker_string round-trip

#### marker_string for boot namespace produces '[boot] event'

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = marker_string(NAMESPACE_BOOT, "entry")
expect(s.starts_with("[boot] ")).to_equal(true)
```

</details>

#### the produced marker is accepted by find_spec

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = marker_string(NAMESPACE_BOOT, "entry")
val spec = find_spec(s)
expect(spec.is_nil()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/logging/marker_wire_format_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- markers.find_spec strict prefix matching
- validate() rejects level-prefixed markers
- log_level_name composition (log_info wire format)
- namespace_prefix / marker_string round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
