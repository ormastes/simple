# smf_deps_validation_spec

> SMF Dependency Validation Specification

<!-- sdn-diagram:id=smf_deps_validation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=smf_deps_validation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

smf_deps_validation_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=smf_deps_validation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# smf_deps_validation_spec

SMF Dependency Validation Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CACHE-DEP-001 to #CACHE-DEP-010 |
| Category | Cache |
| Status | Active |
| Source | `test/01_unit/compiler/cache/smf_deps_validation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

SMF Dependency Validation Specification

Tests serialization/deserialization of dependency hashes
and staleness validation with dependency interface checking.

## Scenarios

### SMF dependency serialization

#### serializes empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = mock_serialize([])
expect(data.len()).to_equal(4)
expect(mock_read_u32_le(data, 0)).to_equal(0)
```

</details>

#### round-trips single dependency

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deps = [MockDep(module_path: "src/lib.spl", interface_hash: 42)]
val data = mock_serialize(deps)
val parsed = mock_deserialize(data)
expect(parsed.len()).to_equal(1)
expect(parsed[0].module_path).to_equal("src/lib.spl")
expect(parsed[0].interface_hash).to_equal(42)
```

</details>

#### round-trips multiple dependencies

1. MockDep
2. MockDep
3. MockDep
   - Expected: parsed.len() equals `3`
   - Expected: parsed[0].module_path equals `src/a.spl`
   - Expected: parsed[0].interface_hash equals `100`
   - Expected: parsed[2].module_path equals `src/c.spl`
   - Expected: parsed[2].interface_hash equals `300`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deps = [
    MockDep(module_path: "src/a.spl", interface_hash: 100),
    MockDep(module_path: "src/b.spl", interface_hash: 200),
    MockDep(module_path: "src/c.spl", interface_hash: 300)
]
val data = mock_serialize(deps)
val parsed = mock_deserialize(data)
expect(parsed.len()).to_equal(3)
expect(parsed[0].module_path).to_equal("src/a.spl")
expect(parsed[0].interface_hash).to_equal(100)
expect(parsed[2].module_path).to_equal("src/c.spl")
expect(parsed[2].interface_hash).to_equal(300)
```

</details>

#### handles long module paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val long_path = "src/compiler/70.backend/backend/common/expression_evaluator_bootstrap.spl"
val deps = [MockDep(module_path: long_path, interface_hash: 999)]
val data = mock_serialize(deps)
val parsed = mock_deserialize(data)
expect(parsed.len()).to_equal(1)
expect(parsed[0].module_path).to_equal(long_path)
```

</details>

#### deserializes truncated data gracefully

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [u8] = [1, 0, 0]  # Less than 4 bytes
val parsed = mock_deserialize(data)
expect(parsed.len()).to_equal(0)
```

</details>

### SMF dependency validation

#### returns FRESH when all hashes match

1. MockDep
2. MockDep
   - Expected: result equals `MOCK_CACHE_FRESH`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deps = [
    MockDep(module_path: "src/a.spl", interface_hash: 100),
    MockDep(module_path: "src/b.spl", interface_hash: 200)
]
val result = mock_validate_deps(deps, ["src/a.spl", "src/b.spl"], [100, 200])
expect(result).to_equal(MOCK_CACHE_FRESH)
```

</details>

#### returns STALE when dependency interface changed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deps = [MockDep(module_path: "src/a.spl", interface_hash: 100)]
val result = mock_validate_deps(deps, ["src/a.spl"], [999])
expect(result).to_equal(MOCK_CACHE_STALE)
```

</details>

#### returns STALE when dependency is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deps = [MockDep(module_path: "src/missing.spl", interface_hash: 100)]
val result = mock_validate_deps(deps, [], [])
expect(result).to_equal(MOCK_CACHE_STALE)
```

</details>

#### returns FRESH for empty dependency list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deps: [MockDep] = []
val result = mock_validate_deps(deps, [], [])
expect(result).to_equal(MOCK_CACHE_FRESH)
```

</details>

#### detects single stale dep among many fresh

1. MockDep
2. MockDep
3. MockDep
   - Expected: result equals `MOCK_CACHE_STALE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deps = [
    MockDep(module_path: "src/a.spl", interface_hash: 100),
    MockDep(module_path: "src/b.spl", interface_hash: 200),
    MockDep(module_path: "src/c.spl", interface_hash: 300)
]
val result = mock_validate_deps(deps, ["src/a.spl", "src/b.spl", "src/c.spl"], [100, 999, 300])
expect(result).to_equal(MOCK_CACHE_STALE)
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
