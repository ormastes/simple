# Test Result Cache Specification

> 1. dir create all

<!-- sdn-diagram:id=test_result_cache_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_result_cache_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_result_cache_spec -> std
test_result_cache_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_result_cache_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Result Cache Specification

## Scenarios

### TestResultCache

#### invalidates cache when dependency content changes without changing size

1. dir create all
2. file write
3. cache record result
4. cache save
5. file write
   - Expected: entry.result_status equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dir_create_all(runner_cache_spec_root)
val cache_path = runner_cache_test_path("runner_cache.sdn")
val test_path = runner_cache_test_path("sample_spec.spl")
val dep_path = runner_cache_test_path("dep_a.spl")

file_write(test_path, "describe \"sample\":\n    it \"runs\":\n        expect(1).to_equal(1)\n")
file_write(dep_path, "alpha")

val cache = test_result_cache_new(cache_path)
cache.record_result(test_path, [dep_path], 1, 0, 0, 12)
cache.save()

file_write(dep_path, "omega")

val reloaded = test_result_cache_load(cache_path)
val entry = reloaded.check_freshness(test_path, [dep_path])

expect(entry.result_status).to_equal(-1)
```

</details>

#### invalidates cache when dependency set no longer matches recorded dependencies

1. dir create all
2. file write
3. file write
4. cache record result
   - Expected: entry.result_status equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dir_create_all(runner_cache_spec_root)
val test_path = runner_cache_test_path("sample_spec.spl")
val dep_a = runner_cache_test_path("dep_a.spl")
val dep_b = runner_cache_test_path("dep_b.spl")

file_write(test_path, "describe \"sample\":\n    it \"runs\":\n        expect(1).to_equal(1)\n")
file_write(dep_a, "dep-a")
file_write(dep_b, "dep-b")

val cache = test_result_cache_new(runner_cache_test_path("runner_cache.sdn"))
cache.record_result(test_path, [dep_a, dep_b], 1, 0, 0, 12)

val entry = cache.check_freshness(test_path, [dep_a])

expect(entry.result_status).to_equal(-1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner_new/test_result_cache_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TestResultCache

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
