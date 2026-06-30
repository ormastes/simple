# Test Daemon Cache Module Specification

> 1. dir create all

<!-- sdn-diagram:id=test_daemon_cache_module_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_daemon_cache_module_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_daemon_cache_module_spec -> std
test_daemon_cache_module_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_daemon_cache_module_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Daemon Cache Module Specification

## Scenarios

### TestDaemon cache module

#### persists cached output across save and load

1. dir create all
2. file write
3. cache record result
4. cache save
   - Expected: entry.result_status equals `2`
   - Expected: entry.result_output equals `line one\nline two`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dir_create_all(daemon_cache_spec_root)
val cache_path = daemon_cache_test_path("daemon_cache.sdn")
val test_path = daemon_cache_test_path("sample_spec.spl")
val dep_path = daemon_cache_test_path("dep_a.spl")

file_write(test_path, "describe \"sample\":\n    it \"runs\":\n        expect(1).to_equal(1)\n")
file_write(dep_path, "dep-a")

val cache = test_result_cache_new(cache_path)
cache.record_result(test_path, [dep_path], 2, 1, 0, 0, 15, "line one\nline two")
cache.save()

val reloaded = test_result_cache_load(cache_path)
val entry = reloaded.check_freshness(test_path, [dep_path])

expect(entry.result_status).to_equal(2)
expect(entry.result_output).to_equal("line one\nline two")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_daemon/test_daemon_cache_module_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TestDaemon cache module

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
