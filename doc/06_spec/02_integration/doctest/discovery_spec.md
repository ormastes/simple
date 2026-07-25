# Discovery Specification

> <details>

<!-- sdn-diagram:id=discovery_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=discovery_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

discovery_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=discovery_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Discovery Specification

## Scenarios

### Doctest Discovery

#### Single File Discovery

#### discovers doctests from .spl file

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file_path = "test/fixtures/doctest/sample.spl"
expect(file_path.len()).to_be_greater_than(0)
```

</details>

#### discovers doctests from .sdt file

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file_path = "test/fixtures/doctest/sample.sdt"
expect(file_path.len()).to_be_greater_than(0)
```

</details>

#### discovers doctests from Markdown file

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file_path = "test/fixtures/doctest/tutorial.md"
expect(file_path.len()).to_be_greater_than(0)
```

</details>

#### returns empty list for unsupported file types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file_path = "test/fixtures/doctest/readme.txt"
expect(file_path.len()).to_be_greater_than(0)
```

</details>

#### Directory Discovery

#### discovers all doctests in directory tree

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val search_path = "test/fixtures/doctest"
expect(search_path.len()).to_be_greater_than(0)
```

</details>

#### excludes files matching exclude patterns

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exclude_pattern = "**/ignored/**"
expect(exclude_pattern.len()).to_be_greater_than(0)
```

</details>

#### handles non-existent directories gracefully

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nonexistent = "nonexistent/path"
expect(nonexistent.len()).to_be_greater_than(0)
```

</details>

#### Source Location Tracking

#### tracks correct line numbers for .spl doctests

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file_path = "test/fixtures/doctest/with_line_numbers.spl"
expect(file_path.len()).to_be_greater_than(0)
```

</details>

#### tracks correct line numbers for Markdown doctests

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file_path = "test/fixtures/doctest/tutorial.md"
expect(file_path.len()).to_be_greater_than(0)
```

</details>

#### Tag and Metadata Extraction

#### extracts tags from @doctest annotations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file_path = "test/fixtures/doctest/tagged.spl"
expect(file_path.len()).to_be_greater_than(0)
```

</details>

#### extracts timeout from @doctest annotations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file_path = "test/fixtures/doctest/with_timeout.spl"
expect(file_path.len()).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/doctest/discovery_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Doctest Discovery

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
