# cache_validator_spec

> Cache Validator Specification

<!-- sdn-diagram:id=cache_validator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cache_validator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cache_validator_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cache_validator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cache_validator_spec

Cache Validator Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CACHE-021 to #CACHE-030 |
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/compiler/cache/cache_validator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Cache Validator Specification

Tests the unified validation logic for SHB and SMF cache artifacts.
Uses mock file system to avoid real I/O.

## Scenarios

### validate_source_hash

#### returns FRESH when hash matches

1. mock reset
2. mock add file
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_reset()
mock_add_file("src/main.spl", 12345)
val result = validate_source_hash_mock("src/main.spl", 12345)
expect(result).to_equal(0)
```

</details>

#### returns STALE when hash differs

1. mock reset
2. mock add file
   - Expected: result equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_reset()
mock_add_file("src/main.spl", 99999)
val result = validate_source_hash_mock("src/main.spl", 12345)
expect(result).to_equal(2)
```

</details>

#### returns ERROR when file missing

1. mock reset
   - Expected: result equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
mock_reset()
val result = validate_source_hash_mock("nonexistent.spl", 12345)
expect(result).to_equal(-1)
```

</details>

### validate_dependencies

#### returns FRESH when all deps match

1. dep reset
2. dep add
3. dep add
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dep_reset()
dep_add("dep1.spl", 100, 100)
dep_add("dep2.spl", 200, 200)
val result = validate_deps_mock()
expect(result).to_equal(0)
```

</details>

#### returns STALE when dependency changed

1. dep reset
2. dep add
   - Expected: result equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dep_reset()
dep_add("dep1.spl", 100, 999)
val result = validate_deps_mock()
expect(result).to_equal(2)
```

</details>

#### returns STALE when dependency missing

1. dep reset
2. dep add
   - Expected: result equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dep_reset()
dep_add("dep1.spl", 100, 0)
val result = validate_deps_mock()
expect(result).to_equal(2)
```

</details>

#### returns FRESH for empty dependency list

1. dep reset
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dep_reset()
val result = validate_deps_mock()
expect(result).to_equal(0)
```

</details>

### source_to_cache_path

#### converts source path to SHB path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = source_to_cache_path_mock("src/app/main.spl", ".build/headers", ".shb")
expect(result).to_equal(".build/headers/src_app_main.shb")
```

</details>

#### converts source path to SMF path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = source_to_cache_path_mock("src/lib/math.spl", "build/smf", ".smf")
expect(result).to_equal("build/smf/src_lib_math.smf")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
