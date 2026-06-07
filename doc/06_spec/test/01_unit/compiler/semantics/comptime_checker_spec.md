# Comptime Checker Specification

> <details>

<!-- sdn-diagram:id=comptime_checker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=comptime_checker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

comptime_checker_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=comptime_checker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 37 | 37 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Comptime Checker Specification

## Scenarios

### Comptime Checker - Non-CT Prefix Detection

#### detects rt_ prefix as non-CT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_has_non_ct_prefix("rt_file_read")
expect(result).to_equal(true)
```

</details>

#### detects shell prefix as non-CT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_has_non_ct_prefix("shell")
expect(result).to_equal(true)
```

</details>

#### detects print prefix as non-CT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_has_non_ct_prefix("println")
expect(result).to_equal(true)
```

</details>

#### detects file_ prefix as non-CT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_has_non_ct_prefix("file_write")
expect(result).to_equal(true)
```

</details>

#### detects env_ prefix as non-CT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_has_non_ct_prefix("env_get")
expect(result).to_equal(true)
```

</details>

#### detects thread_ prefix as non-CT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_has_non_ct_prefix("thread_spawn")
expect(result).to_equal(true)
```

</details>

#### detects process_ prefix as non-CT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_has_non_ct_prefix("process_run")
expect(result).to_equal(true)
```

</details>

#### does not flag pure math function as non-CT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_has_non_ct_prefix("sqrt")
expect(result).to_equal(false)
```

</details>

#### does not flag user-defined function as non-CT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_has_non_ct_prefix("compute_checksum")
expect(result).to_equal(false)
```

</details>

### Comptime Checker - Non-CT Name Detection

#### detects input as non-CT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_is_non_ct_name("input")
expect(result).to_equal(true)
```

</details>

#### detects sleep as non-CT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_is_non_ct_name("sleep")
expect(result).to_equal(true)
```

</details>

#### detects rand as non-CT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_is_non_ct_name("rand")
expect(result).to_equal(true)
```

</details>

#### detects random as non-CT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_is_non_ct_name("random")
expect(result).to_equal(true)
```

</details>

#### detects now as non-CT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_is_non_ct_name("now")
expect(result).to_equal(true)
```

</details>

#### detects time as non-CT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_is_non_ct_name("time")
expect(result).to_equal(true)
```

</details>

#### detects date as non-CT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_is_non_ct_name("date")
expect(result).to_equal(true)
```

</details>

#### does not flag add as non-CT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_is_non_ct_name("add")
expect(result).to_equal(false)
```

</details>

#### does not flag max as non-CT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_is_non_ct_name("max")
expect(result).to_equal(false)
```

</details>

### Comptime Checker - Warning Message Format

#### warning contains WARN[comptime] prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = test_make_warning("my_fn", "rt_io()", "is a runtime-only call (non-CT prefix)")
val has_prefix = msg.contains("WARN[comptime]")
expect(has_prefix).to_equal(true)
```

</details>

#### warning contains function name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = test_make_warning("const_compute", "sleep()", "is a runtime-only function")
val has_fn = msg.contains("const_compute")
expect(has_fn).to_equal(true)
```

</details>

#### warning contains expression text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = test_make_warning("my_fn", "file_write()", "is an I/O operation (not allowed at compile time)")
val has_expr = msg.contains("file_write()")
expect(has_expr).to_equal(true)
```

</details>

#### warning contains reason

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = test_make_warning("my_fn", "sleep()", "is a runtime-only function")
val has_reason = msg.contains("is a runtime-only function")
expect(has_reason).to_equal(true)
```

</details>

#### warning uses em-dash separator

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = test_make_warning("my_fn", "rand()", "is a runtime-only function")
val has_sep = msg.contains("—")
expect(has_sep).to_equal(true)
```

</details>

### Comptime Checker - Batch Analysis

#### counts zero violations for all-safe calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val calls: [text] = ["add", "subtract", "clamp", "max_val"]
val count = test_check_calls_in_fn(calls)
expect(count).to_equal(0)
```

</details>

#### counts one violation for single non-CT call

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val calls: [text] = ["add", "rt_get_time", "clamp"]
val count = test_check_calls_in_fn(calls)
expect(count).to_equal(1)
```

</details>

#### counts multiple violations for multiple non-CT calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val calls: [text] = ["sleep", "rand", "add"]
val count = test_check_calls_in_fn(calls)
expect(count).to_equal(2)
```

</details>

#### counts all violations when all calls are non-CT

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val calls: [text] = ["rt_read", "env_get", "file_write"]
val count = test_check_calls_in_fn(calls)
expect(count).to_equal(3)
```

</details>

#### handles empty call list with zero violations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val calls: [text] = []
val count = test_check_calls_in_fn(calls)
expect(count).to_equal(0)
```

</details>

### Comptime Checker - Safe Expressions

#### pure arithmetic is comptime-safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_check_call("add")
expect(result).to_equal(false)
```

</details>

#### constant literal access is comptime-safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_check_call("PI")
expect(result).to_equal(false)
```

</details>

#### user-defined pure function is comptime-safe by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_check_call("fibonacci")
expect(result).to_equal(false)
```

</details>

#### string concat helper is comptime-safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_check_call("concat_strings")
expect(result).to_equal(false)
```

</details>

### Comptime Checker - Prefix Edge Cases

#### rt_ prefix matches at start only

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_non_ct = test_has_non_ct_prefix("get_rt_value")
expect(is_non_ct).to_equal(false)
```

</details>

#### file_ prefix matches file_read

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_has_non_ct_prefix("file_read")
expect(result).to_equal(true)
```

</details>

#### shell prefix matches shell_exec

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_has_non_ct_prefix("shell_exec")
expect(result).to_equal(true)
```

</details>

#### short name shorter than prefix is not flagged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_has_non_ct_prefix("rt")
expect(result).to_equal(false)
```

</details>

#### exact prefix match shell is non-CT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = test_has_non_ct_prefix("shell")
expect(result).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/comptime_checker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Comptime Checker - Non-CT Prefix Detection
- Comptime Checker - Non-CT Name Detection
- Comptime Checker - Warning Message Format
- Comptime Checker - Batch Analysis
- Comptime Checker - Safe Expressions
- Comptime Checker - Prefix Edge Cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 37 |
| Active scenarios | 37 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
