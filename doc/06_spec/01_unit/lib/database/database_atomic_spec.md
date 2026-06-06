# Database Atomic Specification

> <details>

<!-- sdn-diagram:id=database_atomic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=database_atomic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

database_atomic_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=database_atomic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Database Atomic Specification

## Scenarios

### Database Atomic

#### keeps file lock acquisition and stale lock handling available

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = atomic_source()

expect(source).to_contain("class FileLock:")
expect(source).to_contain("static fn for_file(path: text) -> FileLock")
expect(source).to_contain("me acquire() -> bool")
expect(source).to_contain("me try_acquire(timeout_ms: i64) -> bool")
expect(source).to_contain("fn is_stale_lock() -> bool")
expect(source).to_contain("me release()")
```

</details>

#### keeps atomic read write append and batch operations available

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = atomic_source()

expect(source).to_contain("fn atomic_read(path: text) -> text?")
expect(source).to_contain("fn atomic_write(path: text, content: text) -> bool")
expect(source).to_contain("fn atomic_write_batch(paths: [text], contents: [text]) -> bool")
expect(source).to_contain("fn atomic_append(path: text, content: text) -> bool")
expect(source).to_contain("rt_file_sync(temp_path)")
expect(source).to_contain("rt_file_rename(temp_path, path)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/database/database_atomic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Database Atomic

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
