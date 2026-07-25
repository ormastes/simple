# Traits Specification

> <details>

<!-- sdn-diagram:id=traits_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=traits_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

traits_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=traits_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Traits Specification

## Scenarios

### Traits

#### keeps sync I/O trait surfaces available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = io_traits_source()

expect(source).to_contain("trait Read:")
expect(source).to_contain("trait Write:")
expect(source).to_contain("trait Seek:")
expect(source).to_contain("trait Close:")
```

</details>

#### keeps read and write trait method contracts available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = io_traits_source()

expect(source).to_contain("fn read(size: i64) -> Result<[u8], IoError>")
expect(source).to_contain("fn read_text() -> Result<text, IoError>")
expect(source).to_contain("fn write(data: [u8]) -> Result<i64, IoError>")
expect(source).to_contain("fn flush() -> Result<(), IoError>")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/traits_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Traits

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
