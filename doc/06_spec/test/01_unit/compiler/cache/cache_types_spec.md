# cache_types_spec

> Cache Types Specification

<!-- sdn-diagram:id=cache_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cache_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cache_types_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cache_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cache_types_spec

Cache Types Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CACHE-001 to #CACHE-010 |
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/compiler/cache/cache_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Cache Types Specification

Tests the shared cache result/policy types used across
SHB and SMF validation.

## Scenarios

### CacheCheckResult

### factory functions

#### creates fresh result with matching hashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cache_check_result_fresh(12345)
expect(result.status).to_equal(0)
expect(result.source_hash).to_equal(12345)
expect(result.cached_source_hash).to_equal(12345)
expect(result.detail).to_equal("fresh")
```

</details>

#### creates stale result with reason

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cache_check_result_stale(100, 200, "source changed")
expect(result.status).to_equal(2)
expect(result.source_hash).to_equal(100)
expect(result.cached_source_hash).to_equal(200)
expect(result.detail).to_equal("source changed")
```

</details>

#### creates missing result

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cache_check_result_missing(999)
expect(result.status).to_equal(3)
expect(result.source_hash).to_equal(999)
expect(result.cached_source_hash).to_equal(0)
```

</details>

#### creates error result

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cache_check_result_error("disk failure")
expect(result.status).to_equal(-1)
expect(result.detail).to_equal("disk failure")
```

</details>

### status predicates

#### is_fresh returns true for CACHE_FRESH

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cache_check_result_fresh(0)
expect(result.is_fresh()).to_equal(true)
expect(result.is_stale()).to_equal(false)
```

</details>

#### is_stale returns true for CACHE_STALE

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cache_check_result_stale(1, 2, "changed")
expect(result.is_stale()).to_equal(true)
expect(result.is_fresh()).to_equal(false)
```

</details>

#### is_missing returns true for CACHE_MISSING

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cache_check_result_missing(0)
expect(result.is_missing()).to_equal(true)
```

</details>

#### is_error returns true for CACHE_ERROR

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cache_check_result_error("oops")
expect(result.is_error()).to_equal(true)
```

</details>

### is_usable

#### fresh is usable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cache_check_result_fresh(0)
expect(result.is_usable()).to_equal(true)
```

</details>

#### stale is not usable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = cache_check_result_stale(1, 2, "changed")
expect(result.is_usable()).to_equal(false)
```

</details>

### status_text

#### returns correct text for each status

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cache_check_result_fresh(0).status_text()).to_equal("fresh")
expect(cache_check_result_stale(0, 0, "").status_text()).to_equal("stale")
expect(cache_check_result_missing(0).status_text()).to_equal("missing")
expect(cache_check_result_error("").status_text()).to_equal("error")
```

</details>

### CachePolicy

#### default policy checks all levels

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = cache_policy_default()
expect(policy.check_source_hash).to_equal(true)
expect(policy.check_interface_hash).to_equal(true)
expect(policy.check_options_hash).to_equal(true)
expect(policy.max_staleness_ms).to_equal(0)
```

</details>

#### relaxed policy skips interface and options

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = cache_policy_relaxed()
expect(policy.check_source_hash).to_equal(true)
expect(policy.check_interface_hash).to_equal(false)
expect(policy.check_options_hash).to_equal(false)
expect(policy.max_staleness_ms).to_equal(30000)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
