# Traits Wired Specification

> <details>

<!-- sdn-diagram:id=traits_wired_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=traits_wired_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

traits_wired_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=traits_wired_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Traits Wired Specification

## Scenarios

### Traits Wired

#### keeps example implementors wired to trait composition

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = io_traits_source()

expect(source).to_contain("class StringReader with Read:")
expect(source).to_contain("class FileStream with Read, Write, Close:")
expect(source).to_contain("use std.io.types.{IoError, SeekFrom}")
```

</details>

#### keeps seek and close contracts wired for stream resources

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = io_traits_source()

expect(source).to_contain("fn seek(pos: SeekFrom) -> Result<i64, IoError>")
expect(source).to_contain("fn position() -> Result<i64, IoError>")
expect(source).to_contain("fn rewind() -> Result<(), IoError>")
expect(source).to_contain("me close() -> Result<(), IoError>")
expect(source).to_contain("fn is_open() -> bool")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/traits_wired_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Traits Wired

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
