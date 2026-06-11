# Layer Ci Specification

> <details>

<!-- sdn-diagram:id=layer_ci_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=layer_ci_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

layer_ci_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=layer_ci_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Layer Ci Specification

## Scenarios

### _extract_layer_dir

#### extracts layer dir from compiler source path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _extract_layer_dir("src/compiler/10.frontend/core/lexer.spl")
expect(result).to_equal("10.frontend")
```

</details>

#### extracts layer dir from nested path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _extract_layer_dir("src/compiler/85.mdsoc/adapters/in/profiler.spl")
expect(result).to_equal("85.mdsoc")
```

</details>

#### returns empty for non-compiler paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _extract_layer_dir("src/app/cli/main.spl")
expect(result).to_equal("")
```

</details>

#### returns empty for path without numbered dir

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _extract_layer_dir("src/compiler/common/config.spl")
expect(result).to_equal("")
```

</details>

#### extracts two-digit layer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _extract_layer_dir("src/compiler/00.common/config.spl")
expect(result).to_equal("00.common")
```

</details>

### _resolve_import_to_layer_dir

#### resolves frontend import to numbered dir

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dirs: [text] = ["00.common", "10.frontend", "20.hir", "50.mir", "80.driver"]
val result = _resolve_import_to_layer_dir("compiler.frontend.core.lexer", dirs)
expect(result).to_equal("10.frontend")
```

</details>

#### resolves hir import

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dirs: [text] = ["00.common", "10.frontend", "20.hir", "50.mir"]
val result = _resolve_import_to_layer_dir("compiler.hir.hir_types", dirs)
expect(result).to_equal("20.hir")
```

</details>

#### returns empty for non-compiler import

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dirs: [text] = ["10.frontend", "20.hir"]
val result = _resolve_import_to_layer_dir("std.text.utils", dirs)
expect(result).to_equal("")
```

</details>

#### returns empty for unknown layer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dirs: [text] = ["10.frontend", "20.hir"]
val result = _resolve_import_to_layer_dir("compiler.unknown.module", dirs)
expect(result).to_equal("")
```

</details>

### _scan_file_imports

#### finds cross-layer imports

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "use compiler.frontend.core.lexer.*\nuse compiler.hir.hir.*\n"
val dirs = ["00.common", "10.frontend", "20.hir", "80.driver"]
val path = "src/compiler/80.driver/driver.spl"
val (froms, tos) = _scan_file_imports(path, content, dirs)
expect(froms.len()).to_be_greater_than(0)
```

</details>

#### ignores same-layer imports

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "use compiler.driver.driver_types.*\n"
val dirs = ["00.common", "10.frontend", "80.driver"]
val path = "src/compiler/80.driver/driver.spl"
val (froms, tos) = _scan_file_imports(path, content, dirs)
expect(froms.len()).to_equal(0)
```

</details>

#### ignores non-compiler imports

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "use std.text.utils.*\nuse app.io.mod.*\n"
val dirs = ["10.frontend", "80.driver"]
val path = "src/compiler/80.driver/driver.spl"
val (froms, tos) = _scan_file_imports(path, content, dirs)
expect(froms.len()).to_equal(0)
```

</details>

#### handles empty content

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dirs = ["10.frontend", "80.driver"]
val path = "src/compiler/80.driver/driver.spl"
val (froms, tos) = _scan_file_imports(path, "", dirs)
expect(froms.len()).to_equal(0)
```

</details>

#### handles non-compiler path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "use compiler.frontend.core.lexer.*\n"
val dirs = ["10.frontend", "80.driver"]
val path = "src/app/cli/main.spl"
val (froms, tos) = _scan_file_imports(path, content, dirs)
expect(froms.len()).to_equal(0)
```

</details>

### layer_check module

#### has expected source file

1. extern fn rt file exists
   - Expected: rt_file_exists("src/compiler/80.driver/build/layer_check.spl") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
extern fn rt_file_exists(path: text) -> bool
expect(rt_file_exists("src/compiler/80.driver/build/layer_check.spl")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mdsoc/layer_ci_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- _extract_layer_dir
- _resolve_import_to_layer_dir
- _scan_file_imports
- layer_check module

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
