# test_daemon_cache_spec

> Test Daemon Cache Specification

<!-- sdn-diagram:id=test_daemon_cache_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_daemon_cache_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_daemon_cache_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_daemon_cache_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_daemon_cache_spec

Test Daemon Cache Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TDMN-011 to #TDMN-020 |
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/app/test_daemon/test_daemon_cache_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Test Daemon Cache Specification

Tests change detection and result caching: freshness checks,
recording results, invalidation, and persistence.

## Scenarios

### TestResultCache

### recording results

#### stores test result

1. cache reset
2. cache record
   - Expected: cache_count() equals `1`
   - Expected: cache_get_status("test/foo_spec.spl") equals `2`
   - Expected: cache_get_passed("test/foo_spec.spl") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cache_reset()
cache_record("test/foo_spec.spl", 12345, 2, 10, 0, 500)
expect(cache_count()).to_equal(1)
expect(cache_get_status("test/foo_spec.spl")).to_equal(2)
expect(cache_get_passed("test/foo_spec.spl")).to_equal(10)
```

</details>

#### stores multiple results

1. cache reset
2. cache record
3. cache record
   - Expected: cache_count() equals `2`
   - Expected: cache_get_passed("test/a_spec.spl") equals `5`
   - Expected: cache_get_failed("test/b_spec.spl") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cache_reset()
cache_record("test/a_spec.spl", 111, 2, 5, 0, 200)
cache_record("test/b_spec.spl", 222, 3, 3, 2, 800)
expect(cache_count()).to_equal(2)
expect(cache_get_passed("test/a_spec.spl")).to_equal(5)
expect(cache_get_failed("test/b_spec.spl")).to_equal(2)
```

</details>

#### updates existing entry

1. cache reset
2. cache record
3. cache record
   - Expected: cache_count() equals `1`
   - Expected: cache_get_status("test/x_spec.spl") equals `2`
   - Expected: cache_get_passed("test/x_spec.spl") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cache_reset()
cache_record("test/x_spec.spl", 100, 3, 0, 1, 100)
cache_record("test/x_spec.spl", 200, 2, 5, 0, 300)
expect(cache_count()).to_equal(1)
expect(cache_get_status("test/x_spec.spl")).to_equal(2)
expect(cache_get_passed("test/x_spec.spl")).to_equal(5)
```

</details>

### freshness checking

#### returns fresh when hash matches

1. cache reset
2. src set hash
3. cache record
   - Expected: cache_check_freshness("test/foo_spec.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cache_reset()
src_set_hash("test/foo_spec.spl", 12345)
cache_record("test/foo_spec.spl", 12345, 2, 10, 0, 500)
expect(cache_check_freshness("test/foo_spec.spl")).to_equal(true)
```

</details>

#### returns stale when hash differs

1. cache reset
2. src set hash
3. cache record
   - Expected: cache_check_freshness("test/foo_spec.spl") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cache_reset()
src_set_hash("test/foo_spec.spl", 99999)
cache_record("test/foo_spec.spl", 12345, 2, 10, 0, 500)
expect(cache_check_freshness("test/foo_spec.spl")).to_equal(false)
```

</details>

#### returns stale for uncached test

1. cache reset
2. src set hash
   - Expected: cache_check_freshness("test/new_spec.spl") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cache_reset()
src_set_hash("test/new_spec.spl", 11111)
expect(cache_check_freshness("test/new_spec.spl")).to_equal(false)
```

</details>

#### returns stale when no source hash

1. cache reset
2. cache record
   - Expected: cache_check_freshness("test/foo_spec.spl") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cache_reset()
cache_record("test/foo_spec.spl", 12345, 2, 10, 0, 500)
expect(cache_check_freshness("test/foo_spec.spl")).to_equal(false)
```

</details>

### invalidation

#### clears all entries

1. cache reset
2. cache record
3. cache record
   - Expected: cache_count() equals `2`
4. cache invalidate all
   - Expected: cache_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cache_reset()
cache_record("test/a_spec.spl", 111, 2, 5, 0, 200)
cache_record("test/b_spec.spl", 222, 2, 3, 0, 100)
expect(cache_count()).to_equal(2)
cache_invalidate_all()
expect(cache_count()).to_equal(0)
```

</details>

#### freshness returns stale after invalidation

1. cache reset
2. src set hash
3. cache record
4. cache invalidate all
   - Expected: cache_check_freshness("test/foo_spec.spl") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cache_reset()
src_set_hash("test/foo_spec.spl", 12345)
cache_record("test/foo_spec.spl", 12345, 2, 10, 0, 500)
cache_invalidate_all()
expect(cache_check_freshness("test/foo_spec.spl")).to_equal(false)
```

</details>

### duration tracking

#### records test duration

1. cache reset
2. cache record
   - Expected: cache_get_duration("test/slow_spec.spl") equals `5000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cache_reset()
cache_record("test/slow_spec.spl", 100, 2, 1, 0, 5000)
expect(cache_get_duration("test/slow_spec.spl")).to_equal(5000)
```

</details>

#### returns 0 for unknown test

1. cache reset
   - Expected: cache_get_duration("test/unknown_spec.spl") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
cache_reset()
expect(cache_get_duration("test/unknown_spec.spl")).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
