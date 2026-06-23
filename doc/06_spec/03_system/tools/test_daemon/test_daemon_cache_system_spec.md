# test_daemon_cache_system_spec

> @cover src/app/test_daemon/cache.spl 80%

<!-- sdn-diagram:id=test_daemon_cache_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_daemon_cache_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_daemon_cache_system_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_daemon_cache_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_daemon_cache_system_spec

@cover src/app/test_daemon/cache.spl 80%

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TDMN-SYS-021 to #TDMN-SYS-030 |
| Category | Infrastructure / System Test |
| Status | Active |
| Source | `test/03_system/tools/test_daemon/test_daemon_cache_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

@cover src/app/test_daemon/cache.spl 80%
Test Daemon Cache System Test

Tests real file-based change detection and caching.
Creates actual test files, hashes them, records results,
modifies files, and verifies cache invalidation.

NOTE: Each test is wrapped in a standalone function to work around
the nested closure capture bug (it blocks can't see module var mutations).

## Scenarios

### TestDaemon Cache System

### real file hashing

#### detects unchanged file as fresh

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_unchanged_file_fresh()).to_equal(true)
```

</details>

#### detects modified file as stale

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_modified_file_stale()).to_equal(true)
```

</details>

#### detects new file as not cached

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_new_file_not_cached()).to_equal(true)
```

</details>

### multi-file change detection

#### tracks 5 test files independently

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_track_5_files()).to_equal("ok")
```

</details>

#### re-records after modification

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_rerecord_after_modification()).to_equal("ok")
```

</details>

### invalidation

#### invalidates all cached results

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_invalidation()).to_equal("ok")
```

</details>

### persistence

#### saves cache to file

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_persistence()).to_equal("ok")
```

</details>

### edge cases

#### handles empty file

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_empty_file()).to_equal(true)
```

</details>

#### handles very large content

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_large_content()).to_equal("ok")
```

</details>

#### handles special characters in file path

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_special_chars_path()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
