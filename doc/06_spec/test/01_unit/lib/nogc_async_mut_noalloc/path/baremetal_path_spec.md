# Baremetal Path Specification

> <details>

<!-- sdn-diagram:id=baremetal_path_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=baremetal_path_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

baremetal_path_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=baremetal_path_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Baremetal Path Specification

## Scenarios

### Baremetal Path

#### defines baremetal path constants and component helpers

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = rt_file_read_text("src/lib/nogc_async_mut_noalloc/path/baremetal_path.spl")
val init = rt_file_read_text("src/lib/nogc_async_mut_noalloc/__init__.spl")

expect(path).to_contain("val PATH_SEP: text = \"/\"")
expect(path).to_contain("val MAX_PATH_LEN: i32 = 256")
expect(path).to_contain("fn bm_path_basename(path: text) -> text:")
expect(path).to_contain("fn bm_path_dirname(path: text) -> text:")
expect(path).to_contain("fn bm_path_extension(path: text) -> text:")
expect(path).to_contain("fn bm_replace_backslash(path: text) -> text:")
expect(init).to_contain("export PATH_SEP, MAX_PATH_LEN")
```

</details>

#### defines join, normalize, and semihost file contracts

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = rt_file_read_text("src/lib/nogc_async_mut_noalloc/path/baremetal_path.spl")
val init = rt_file_read_text("src/lib/nogc_async_mut_noalloc/__init__.spl")

expect(path).to_contain("fn bm_path_join(base: text, child: text) -> text:")
expect(path).to_contain("fn bm_path_normalize(path: text) -> text:")
expect(path).to_contain("val is_abs = clean.starts_with(\"/\")")
expect(path).to_contain("elif part == \"..\":")
expect(path).to_contain("fn bm_file_open(path: text, mode: i32) -> i32:")
expect(path).to_contain("fn bm_file_write(handle: i32, data: text) -> i32:")
expect(path).to_contain("fn bm_file_close(handle: i32):")
expect(init).to_contain("export bm_path_normalize, bm_path_join, bm_path_basename")
expect(init).to_contain("export bm_file_open, bm_file_write, bm_file_close")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut_noalloc/path/baremetal_path_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Baremetal Path

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
