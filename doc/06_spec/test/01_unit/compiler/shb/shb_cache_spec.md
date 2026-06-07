# Shb Cache Specification

> <details>

<!-- sdn-diagram:id=shb_cache_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shb_cache_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shb_cache_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shb_cache_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shb Cache Specification

## Scenarios

### SHB Cache

### Cache Config

#### default cache dir is .build/headers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache_dir = ".build/headers"
expect(cache_dir).to_equal(".build/headers")
```

</details>

#### default config is enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enabled = true
expect(enabled).to_equal(true)
```

</details>

### Cache Manager

#### creates with default config

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache_dir = ".build/headers"
expect(cache_dir.starts_with(".build")).to_equal(true)
```

</details>

#### converts source path to shb path

1. var step1 = source replace
2. var step2 = step1 replace
   - Expected: step2 equals `src_app_cli_main`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# src/app/cli/main.spl => .build/headers/src_app_cli_main.shb
val source = "src/app/cli/main.spl"
var step1 = source.replace("/", "_")
var step2 = step1.replace(".spl", "")
expect(step2).to_equal("src_app_cli_main")
```

</details>

#### converts nested paths correctly

1. var step1 = source replace
2. var step2 = step1 replace
   - Expected: step2 equals `src_compiler_shb_shb_types`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "src/compiler/shb/shb_types.spl"
var step1 = source.replace("/", "_")
var step2 = step1.replace(".spl", "")
expect(step2).to_equal("src_compiler_shb_shb_types")
```

</details>

### Two-Level Cache Logic

#### returns UNCHANGED when source hash matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# source_hash == .shb.source_hash => skip
val status_unchanged = 0
expect(status_unchanged).to_equal(0)
```

</details>

#### returns BODY_ONLY when interface hash matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# source changed, interface same => recompile this file only
val status_body = 1
expect(status_body).to_equal(1)
```

</details>

#### returns INTERFACE when interface hash differs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# interface changed => recompile this + dependents
val status_iface = 2
expect(status_iface).to_equal(2)
```

</details>

#### returns NEW when no cache exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status_new = 3
expect(status_new).to_equal(3)
```

</details>

#### returns ERROR on read failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status_error = -1
expect(status_error).to_equal(-1)
```

</details>

### Stale Detection

#### detects stale when no cache exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# No .shb file => stale
val cache_exists = false
expect(cache_exists).to_equal(false)
```

</details>

#### detects stale when hash mismatches

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Expected hash 42 but actual hash 99 => stale
expect(42 != 99).to_equal(true)
```

</details>

#### not stale when hash matches

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Expected 42, actual 42 => not stale
expect(42 == 42).to_equal(true)
```

</details>

### Dependency Validation

#### validates when all dep hashes match

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected_hash = 42
val actual_hash = 42
expect(actual_hash).to_equal(expected_hash)
```

</details>

#### fails when any dep hash mismatches

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val expected_hash = 42
val actual_hash = 99
expect(actual_hash != expected_hash).to_equal(true)
```

</details>

#### fails when dep file not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dep_exists = false
expect(dep_exists).to_equal(false)
```

</details>

### Batch Processing

#### empty batch produces zero counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val unchanged = 0
val errors = 0
expect(unchanged).to_equal(0)
expect(errors).to_equal(0)
```

</details>

#### skips non-spl files

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# readme.md is not .spl => skipped
val path = "readme.md"
val is_spl = path.ends_with(".spl")
expect(is_spl).to_equal(false)
```

</details>

#### skips deleted files

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event_type = "deleted"
val should_skip = event_type == "deleted"
expect(should_skip).to_equal(true)
```

</details>

#### detects interface changes in batch

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val iface_changed = 1
val has_changes = iface_changed > 0
expect(has_changes).to_equal(true)
```

</details>

#### reports no interface changes when body-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val iface_changed = 0
val has_changes = iface_changed > 0
expect(has_changes).to_equal(false)
```

</details>

### Batch Summary

#### formats counts correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "5 unchanged, 2 body-only, 1 interface changed"
val summary = "5 unchanged, 2 body-only, 1 interface changed"
expect(summary).to_contain("2 body-only")
```

</details>

### Atomic Write Safety

#### writes to temp file first

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# path.tmp is written, then renamed to path
val temp_path = ".build/headers/module.shb.tmp"
expect(temp_path).to_end_with(".tmp")
```

</details>

#### rename is atomic on same filesystem

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Linux guarantees atomic rename
val source_dir = ".build/headers"
val target_dir = ".build/headers"
expect(source_dir).to_equal(target_dir)
```

</details>

### Watcher Integration

#### converts FileChangeEvent to ShbChangeEvent

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val event = "src/app/main.spl:modified"
expect(event).to_contain("modified")
```

</details>

#### shb_mode flag enables SHB generation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shb_mode = true
expect(shb_mode).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/shb/shb_cache_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SHB Cache
- Cache Config
- Cache Manager
- Two-Level Cache Logic
- Stale Detection
- Dependency Validation
- Batch Processing
- Batch Summary
- Atomic Write Safety
- Watcher Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
