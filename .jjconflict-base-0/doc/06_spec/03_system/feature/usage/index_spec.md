# Registry Index Specification

> Tests for the sparse package index: parsing SDN entries, computing index paths, and searching.

<!-- sdn-diagram:id=index_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=index_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

index_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=index_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Registry Index Specification

Tests for the sparse package index: parsing SDN entries, computing index paths, and searching.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #956-958 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | In Progress |
| Source | `test/03_system/feature/usage/index_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Tests for the sparse package index: parsing SDN entries,
computing index paths, and searching.

## Key Concepts
- SDN index entry parsing
- Sparse directory path computation
- Package listing and search

## Scenarios

### Index Path Computation

#### computes path for 4+ char names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = index_path_for("http")
expect(path).to_equal("ht/tp/http.sdn")
```

</details>

#### computes path for long names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = index_path_for("collections")
expect(path).to_equal("co/ll/collections.sdn")
```

</details>

#### computes path for 3 char names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = index_path_for("url")
expect(path).to_equal("ur/l/url.sdn")
```

</details>

#### computes path for 2 char names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = index_path_for("io")
expect(path).to_equal("i/o/io.sdn")
```

</details>

#### computes path for 1 char names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = index_path_for("x")
expect(path).to_equal("_/x/x.sdn")
```

</details>

### Index Entry Parsing

#### parses package name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = parse_index_entry(sample_entry())
expect(entry.package.name).to_equal("http")
```

</details>

#### parses package description

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = parse_index_entry(sample_entry())
expect(entry.package.description).to_equal("HTTP client library")
```

</details>

#### parses version entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = parse_index_entry(sample_entry())
expect(entry.versions.len()).to_equal(2)
```

</details>

#### parses version checksum

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = parse_index_entry(sample_entry())
expect(entry.versions[0].checksum).to_equal("sha256:abc123")
```

</details>

#### parses yanked flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = parse_index_entry(sample_entry())
expect(entry.versions[0].yanked).to_equal(false)
```

</details>

#### parses dependencies

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = parse_index_entry(sample_entry())
expect(entry.dependencies.len()).to_equal(2)
```

</details>

#### parses dependency constraint

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = parse_index_entry(sample_entry())
expect(entry.dependencies[0].constraint).to_equal("^1.0")
```

</details>

### Index Queries

#### finds latest non-yanked version

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = parse_index_entry(sample_entry())
val latest = latest_version(entry)
expect(latest).to_equal("1.1.0")
```

</details>

#### finds dependencies for a version

1. var deps = deps for version
   - Expected: deps.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = parse_index_entry(sample_entry())
var deps = deps_for_version(entry, "1.1.0")
expect(deps.len()).to_equal(1)
```

</details>

#### finds specific version entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = parse_index_entry(sample_entry())
val ver = find_version(entry, "1.0.0")
expect(ver.version).to_equal("1.0.0")
```

</details>

#### returns empty for missing version

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = parse_index_entry(sample_entry())
val ver = find_version(entry, "9.9.9")
expect(ver.version).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
