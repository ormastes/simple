# Process Ops Ext Specification

> <details>

<!-- sdn-diagram:id=process_ops_ext_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=process_ops_ext_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

process_ops_ext_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=process_ops_ext_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Process Ops Ext Specification

## Scenarios

### app.io.process_ops

### shell

#### returns ProcessResult with stdout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell("echo hello")
expect(result.stdout).to_contain("hello")
```

</details>

#### returns exit_code 0 on success

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell("true")
expect(result.exit_code).to_equal(0)
```

</details>

#### returns non-zero exit_code on failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell("false")
val code = result.exit_code
expect(code).to_be_greater_than(0)
```

</details>

#### captures stderr

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell("echo err_msg >&2")
expect(result.stderr).to_contain("err_msg")
```

</details>

### shell_bool

#### returns true for successful command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell_bool("true")
expect(result).to_equal(true)
```

</details>

#### returns false for failing command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell_bool("false")
expect(result == false).to_equal(true)
```

</details>

#### returns true for echo

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell_bool("echo test")
expect(result).to_equal(true)
```

</details>

### shell_output

#### returns stdout on success

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell_output("echo hello_world", "fallback")
expect(result).to_contain("hello_world")
```

</details>

#### returns default on failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell_output("false", "my_default")
expect(result).to_equal("my_default")
```

</details>

### shell_output_trimmed

#### returns trimmed stdout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell_output_trimmed("echo '  spaces  '", "default")
expect(result).to_equal("spaces")
```

</details>

#### returns default on failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell_output_trimmed("false", "my_fallback")
expect(result).to_equal("my_fallback")
```

</details>

### shell_lines

#### returns empty list on failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = shell_lines("false")
val count = lines.len()
expect(count).to_equal(0)
```

</details>

#### returns empty list for empty output command

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = shell_lines("true")
val count = lines.len()
expect(count).to_equal(0)
```

</details>

### shell_int

#### parses integer output

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell_int("echo 42", 0)
expect(result).to_equal(42)
```

</details>

#### returns default on failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell_int("false", -1)
expect(result).to_equal(-1)
```

</details>

#### returns default on empty output

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell_int("echo ''", 99)
expect(result).to_equal(99)
```

</details>

#### returns default on malformed output

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell_int("echo nope", 77)
expect(result).to_equal(77)
```

</details>

### process_run

#### runs a command and returns tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = process_run("echo", ["hello"])
val stdout = result.0
val code = result.2
expect(stdout).to_contain("hello")
expect(code).to_equal(0)
```

</details>

#### returns non-zero for bad command args

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = process_run("ls", ["/no_such_path_999"])
val code = result.2
expect(code).to_be_greater_than(0)
```

</details>

### process_output

#### returns stdout from command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = process_output("echo", ["hello_output"])
expect(output).to_contain("hello_output")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/io/process_ops_ext_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- app.io.process_ops
- shell
- shell_bool
- shell_output
- shell_output_trimmed
- shell_lines
- shell_int
- process_run
- process_output

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
