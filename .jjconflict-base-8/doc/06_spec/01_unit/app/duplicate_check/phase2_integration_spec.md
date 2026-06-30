# Phase2 Integration Specification

> <details>

<!-- sdn-diagram:id=phase2_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=phase2_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

phase2_integration_spec -> compiler
phase2_integration_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=phase2_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Phase2 Integration Specification

## Scenarios

### Phase 2: Parallel configuration

#### creates default parallel config

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_parallel_config()

expect(config.num_workers).to_equal(0)  # Auto-detect
expect(config.batch_size).to_equal(10)
expect(config.enabled).to_equal(true)
```

</details>

#### creates single-threaded config

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = single_threaded_config()

expect(config.num_workers).to_equal(1)
expect(config.enabled).to_equal(false)
```

</details>

#### detects CPU count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cpu_count = detect_cpu_count()

expect(cpu_count).to_be_greater_than(0)
```

</details>

### Phase 2: Incremental cache loading

#### creates empty cache when file missing

1. cleanup test files
2. var config = minimal test config
   - Expected: cache.entries.keys().len() equals `0`
   - Expected: cache.cache_path equals `cache_path`
3. cleanup test files


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache_path = "/tmp/test_duplicate_phase2/cache_empty.sdn"
cleanup_test_files()

var config = minimal_test_config()
config.min_tokens = 30
config.min_lines = 5
config.use_incremental = true
config.incremental_cache_path = cache_path

val cache = load_incremental_cache(cache_path, config)

expect(cache.entries.keys().len()).to_equal(0)
expect(cache.cache_path).to_equal(cache_path)

cleanup_test_files()
```

</details>

#### saves and loads incremental cache

1. cleanup test files
2. var config = minimal test config
3. var cache = load incremental cache
4. create test file
5. code: "fn test
6. cache = update cache entry
7. save incremental cache
   - Expected: reloaded.entries.keys().len() equals `1`
   - Expected: total_cached_block_count(reloaded) equals `1`
8. cleanup test files


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache_path = "/tmp/test_duplicate_phase2/cache_save.sdn"
cleanup_test_files()

var config = minimal_test_config()
config.min_tokens = 30
config.min_lines = 5
config.use_incremental = true
config.incremental_cache_path = cache_path

var cache = load_incremental_cache(cache_path, config)

# Add a test block
val test_file = "/tmp/test_duplicate_phase2/test.spl"
create_test_file(test_file, "fn test(): 42")

val blocks = [DuplicateBlock(
    file: test_file,
    line_start: 1,
    line_end: 1,
    token_count: 5,
    hash_value: 12345,
    snippet_start_offset: 0,
    snippet_end_offset: 13,
    code: "fn test(): 42"
)]

cache = update_cache_entry(cache, test_file, blocks)
save_incremental_cache(cache)

# Reload cache
val reloaded = load_incremental_cache(cache_path, config)

expect(reloaded.entries.keys().len()).to_equal(1)
expect(total_cached_block_count(reloaded)).to_equal(1)

cleanup_test_files()
```

</details>

### Phase 2: Incremental cache invalidation

#### detects file changes

1. cleanup test files
2. var config = minimal test config
3. var cache = load incremental cache
4. create test file
5. code: "fn test1
6. cache = update cache entry
7. save incremental cache
8. var needs update = needs reprocessing
   - Expected: needs_update is false
9. file write
10. needs update = needs reprocessing
   - Expected: needs_update is true
11. cleanup test files


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache_path = "/tmp/test_duplicate_phase2/cache_invalidate.sdn"
cleanup_test_files()

var config = minimal_test_config()
config.min_tokens = 30
config.min_lines = 5
config.use_incremental = true
config.incremental_cache_path = cache_path

var cache = load_incremental_cache(cache_path, config)

val test_file = "/tmp/test_duplicate_phase2/test_change.spl"
create_test_file(test_file, "fn test1(): 1")

val blocks = [DuplicateBlock(
    file: test_file,
    line_start: 1,
    line_end: 1,
    token_count: 5,
    hash_value: 111,
    snippet_start_offset: 0,
    snippet_end_offset: 13,
    code: "fn test1(): 1"
)]

cache = update_cache_entry(cache, test_file, blocks)
save_incremental_cache(cache)

# File should not need reprocessing (unchanged)
var needs_update = needs_reprocessing(test_file, cache)
expect(needs_update).to_equal(false)

# Change file content
file_write(test_file, "fn test2(): 2")

# Now should need reprocessing
needs_update = needs_reprocessing(test_file, cache)
expect(needs_update).to_equal(true)

cleanup_test_files()
```

</details>

### Phase 2: Incremental statistics

#### computes cache hit rate

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = compute_incremental_stats(100, 70)

expect(stats.total_files).to_equal(100)
expect(stats.cached_files).to_equal(70)
expect(stats.reprocessed_files).to_equal(30)
expect(stats.cache_hit_rate).to_equal(70)
```

</details>

#### formats incremental stats

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = compute_incremental_stats(50, 40)
val formatted = format_incremental_stats(stats)

expect(formatted).to_contain("10 changed")
expect(formatted).to_contain("40 cached")
expect(formatted).to_contain("80% hit rate")
```

</details>

### Phase 2: End-to-end incremental detection

#### uses cached results for unchanged files

1. cleanup test files
2. create test file
3. create test file
4. var config = minimal test config
5. var cache = load incremental cache
6. cache = load incremental cache
   - Expected: cached1.len() equals `0`
7. cleanup test files


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cache_path = "/tmp/test_duplicate_phase2/cache_e2e.sdn"
cleanup_test_files()

val test_file1 = "/tmp/test_duplicate_phase2/e2e_test1.spl"
val test_file2 = "/tmp/test_duplicate_phase2/e2e_test2.spl"
create_test_file(test_file1, duplicate_e2e_body("test1"))
create_test_file(test_file2, duplicate_e2e_body("test2"))

var config = minimal_test_config()
config.use_incremental = true
config.incremental_cache_path = cache_path

# First run - build cache
var cache = load_incremental_cache(cache_path, config)
val cache_manager = new_token_cache_manager()
val files = [test_file1, test_file2]
val groups1 = find_duplicates(files, config, cache_manager)

expect(groups1.len()).to_be_greater_than(0)

# Second run - should use cache
cache = load_incremental_cache(cache_path, config)
val cached1 = get_cached_blocks(test_file1, cache)

# Cache should be empty (we didn't update it manually)
expect(cached1.len()).to_equal(0)

cleanup_test_files()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/duplicate_check/phase2_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Phase 2: Parallel configuration
- Phase 2: Incremental cache loading
- Phase 2: Incremental cache invalidation
- Phase 2: Incremental statistics
- Phase 2: End-to-end incremental detection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
