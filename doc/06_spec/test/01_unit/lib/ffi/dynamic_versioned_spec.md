# Dynamic Versioned Specification

> <details>

<!-- sdn-diagram:id=dynamic_versioned_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dynamic_versioned_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dynamic_versioned_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dynamic_versioned_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dynamic Versioned Specification

## Scenarios

### LibVersion

#### formats any version

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = lib_version_any()
expect(lib_version_string(v)).to_equal("any")
```

</details>

#### formats major only

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = lib_version(1, 0, 0)
expect(lib_version_string(v)).to_equal("1")
```

</details>

#### formats major.minor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = lib_version(2, 3, 0)
expect(lib_version_string(v)).to_equal("2.3")
```

</details>

#### formats major.minor.patch

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = lib_version(1, 2, 3)
expect(lib_version_string(v)).to_equal("1.2.3")
```

</details>

### build_candidate_paths

#### generates candidates for unversioned library

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val paths = build_candidate_paths("t32api64", lib_version_any())
# Should contain at least bare name fallback
expect(paths.len() > 0).to_equal(true)
# Should contain lib prefix variant
var has_lib_prefix = false
var i = 0
while i < paths.len():
    if paths[i].contains("libt32api64"):
        has_lib_prefix = true
    i = i + 1
expect(has_lib_prefix).to_equal(true)
```

</details>

#### generates versioned candidates

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val paths = build_candidate_paths("mylib", lib_version(2, 1, 0))
# Should contain versioned .so.2 or .2.dylib variants
var has_major_version = false
var i = 0
while i < paths.len():
    if paths[i].contains(".2") or paths[i].contains("so.2"):
        has_major_version = true
    i = i + 1
expect(has_major_version).to_equal(true)
```

</details>

#### generates full version candidates

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val paths = build_candidate_paths("mylib", lib_version(1, 2, 3))
var has_full_version = false
var i = 0
while i < paths.len():
    if paths[i].contains("1.2.3"):
        has_full_version = true
    i = i + 1
expect(has_full_version).to_equal(true)
```

</details>

### library_search_paths

#### returns at least one search path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val paths = library_search_paths()
expect(paths.len() > 0).to_equal(true)
```

</details>

#### includes T32 API path

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val paths = library_search_paths()
var has_t32 = false
var i = 0
while i < paths.len():
    if paths[i].contains("t32"):
        has_t32 = true
    i = i + 1
expect(has_t32).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/ffi/dynamic_versioned_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LibVersion
- build_candidate_paths
- library_search_paths

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
