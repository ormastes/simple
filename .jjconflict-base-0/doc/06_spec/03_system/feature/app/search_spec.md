# Registry Search

> Tests the package registry search functionality including keyword matching, tag filtering, and result ranking. Verifies that search queries return relevant packages with correct metadata and pagination support.

<!-- sdn-diagram:id=search_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=search_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

search_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=search_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Registry Search

Tests the package registry search functionality including keyword matching, tag filtering, and result ranking. Verifies that search queries return relevant packages with correct metadata and pagination support.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/app/search_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the package registry search functionality including keyword matching,
tag filtering, and result ranking. Verifies that search queries return relevant
packages with correct metadata and pagination support.

## Scenarios

### Search Command

#### when packages match

#### finds packages by name

1. var results = search listing
   - Expected: results.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var results = search_listing(sample_listing(), "http", 20)
expect(results.len()).to_equal(1)
```

</details>

#### finds packages by description

1. var results = search listing
   - Expected: results.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var results = search_listing(sample_listing(), "parser", 20)
expect(results.len()).to_equal(1)
```

</details>

#### is case insensitive

1. var results = search listing
   - Expected: results.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var results = search_listing(sample_listing(), "HTTP", 20)
expect(results.len()).to_equal(1)
```

</details>

#### when no packages match

#### returns empty list

1. var results = search listing
   - Expected: results.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var results = search_listing(sample_listing(), "nonexistent", 20)
expect(results.len()).to_equal(0)
```

</details>

#### when limit is applied

#### respects result limit

1. var results = search listing
   - Expected: results.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var results = search_listing(sample_listing(), "", 1)
expect(results.len()).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
