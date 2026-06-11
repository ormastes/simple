# Linker Wrapper Lib Support Specification

> <details>

<!-- sdn-diagram:id=linker_wrapper_lib_support_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=linker_wrapper_lib_support_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

linker_wrapper_lib_support_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=linker_wrapper_lib_support_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Linker Wrapper Lib Support Specification

## Scenarios

### Linker Wrapper Lib Support

#### extracts library basenames

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(extract_basename("/usr/lib/simple/libstd.lsm")).to_equal("libstd")
expect(extract_basename("libmath.lsm")).to_equal("libmath")
expect(extract_basename("/a/b/c/d/mylib.lsm")).to_equal("mylib")
```

</details>

#### returns empty library lists for missing search paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = scan_libraries(["/nonexistent/path"], false)
expect(result.is_ok()).to_equal(true)
expect(result.unwrap().len()).to_equal(0)
```

</details>

#### returns empty undefined symbol lists for empty or missing object files

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_result = extract_undefined_symbols([], false)
expect(empty_result.is_ok()).to_equal(true)
expect(empty_result.unwrap().len()).to_equal(0)

val missing_result = extract_undefined_symbols(["/nonexistent/file.o"], false)
expect(missing_result.is_ok()).to_equal(true)
expect(missing_result.unwrap().len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/linker_wrapper_lib_support_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Linker Wrapper Lib Support

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
