# Auto Defer Specification

> <details>

<!-- sdn-diagram:id=auto_defer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=auto_defer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

auto_defer_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=auto_defer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Auto Defer Specification

## Scenarios

### WI-5: Auto-defer pass file exists

#### auto_defer.spl exists in semantics directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.len()).to_be_greater_than(0)
```

</details>

### WI-5: Auto-defer data structures

#### AutoDeferCandidate struct defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("struct AutoDeferCandidate")).to_equal(true)
```

</details>

#### AutoDeferCandidate has var_name field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("var_name: text")).to_equal(true)
```

</details>

#### AutoDeferCandidate has type_name field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("type_name: text")).to_equal(true)
```

</details>

#### AutoDeferCandidate has has_manual_defer field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("has_manual_defer: bool")).to_equal(true)
```

</details>

#### AutoDeferCandidate has no_auto_defer annotation field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("has_no_auto_defer_annotation: bool")).to_equal(true)
```

</details>

#### AutoDeferResult struct defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("struct AutoDeferResult")).to_equal(true)
```

</details>

### WI-5: Resource trait detection

#### is_resource_type function defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("fn is_resource_type")).to_equal(true)
```

</details>

#### checks for Resource trait

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("\"Resource\"")).to_equal(true)
```

</details>

#### checks for Closeable trait

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("\"Closeable\"")).to_equal(true)
```

</details>

#### checks for AutoCloseable trait

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("\"AutoCloseable\"")).to_equal(true)
```

</details>

#### has_close_method function defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("fn has_close_method")).to_equal(true)
```

</details>

### WI-5: Scope analysis

#### find_deferred_vars function defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("fn find_deferred_vars")).to_equal(true)
```

</details>

#### parses defer x.close() pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("starts_with(\"defer \")")).to_equal(true)
```

</details>

#### has_no_auto_defer_annotation function defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("fn has_no_auto_defer_annotation")).to_equal(true)
```

</details>

### WI-5: Auto-defer analysis pass

#### auto_defer_analyze function defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("fn auto_defer_analyze")).to_equal(true)
```

</details>

#### auto_defer_generate_stmts function defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("fn auto_defer_generate_stmts")).to_equal(true)
```

</details>

#### generates defer var.close() statements

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
# Checks that the generated statement includes .close()
expect(content.contains(".var_name}.close()")).to_equal(true)
```

</details>

### WI-5: Exports

#### exports data structures

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("pub struct AutoDeferCandidate")).to_equal(true)
expect(content.contains("pub struct AutoDeferResult")).to_equal(true)
```

</details>

#### exports analysis functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("pub fn auto_defer_analyze")).to_equal(true)
expect(content.contains("pub fn auto_defer_generate_stmts")).to_equal(true)
```

</details>

#### exports detection functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("pub fn is_resource_type")).to_equal(true)
expect(content.contains("pub fn has_close_method")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/auto_defer_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WI-5: Auto-defer pass file exists
- WI-5: Auto-defer data structures
- WI-5: Resource trait detection
- WI-5: Scope analysis
- WI-5: Auto-defer analysis pass
- WI-5: Exports

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
