# Must Use Specification

> <details>

<!-- sdn-diagram:id=must_use_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=must_use_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

must_use_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=must_use_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Must Use Specification

## Scenarios

### Must Use

#### should expose must_use registry functions

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_tables.spl")
expect(src.contains("fn must_use_register(name: text, reason: text)")).to_equal(true)
expect(src.contains("fn must_use_is_registered(name: text) -> bool")).to_equal(true)
expect(src.contains("fn must_use_get_reason(name: text) -> text")).to_equal(true)
expect(src.contains("fn must_use_scan_source(source: text)")).to_equal(true)
```

</details>

#### should scan must_use annotations and optional reasons

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_tables.spl")
expect(src.contains("if trimmed.starts_with(\"# @must_use\")")).to_equal(true)
expect(src.contains("pending_must_use = true")).to_equal(true)
expect(src.contains("if trimmed.contains(\"(\\\"\")")).to_equal(true)
expect(src.contains("pending_reason = reason_chars.join(\"\")")).to_equal(true)
expect(src.contains("must_use_register(fname, pending_reason)")).to_equal(true)
```

</details>

#### should enable critical profile mode from source annotations

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tables_src = read_source("src/compiler/10.frontend/core/interpreter/eval_tables.spl")
val mod_src = read_source("src/compiler/10.frontend/core/interpreter/mod.spl")
expect(tables_src.contains("if trimmed.starts_with(\"# @profile(critical)\")")).to_equal(true)
expect(tables_src.contains("must_use_critical_mode = true")).to_equal(true)
expect(mod_src.contains("must_use_scan_source(source)")).to_equal(true)
```

</details>

#### should emit R9 errors and help for ignored must_use calls

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_stmts.spl")
expect(src.contains("if must_use_is_registered(fn_name)")).to_equal(true)
expect(src.contains("error[R9]: return value of function '")).to_equal(true)
expect(src.contains("must be used")).to_equal(true)
expect(src.contains("= help: assign to variable or use 'val _ = ...' to discard")).to_equal(true)
```

</details>

#### should emit R9 errors in critical profile mode

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_source("src/compiler/10.frontend/core/interpreter/eval_stmts.spl")
expect(src.contains("elif must_use_critical_mode")).to_equal(true)
expect(src.contains("discarded in @profile(critical)")).to_equal(true)
expect(src.contains("warning: return value of type '")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/must_use_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Must Use

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
