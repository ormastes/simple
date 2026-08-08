# File Shell Exec Specification

> <details>

<!-- sdn-diagram:id=file_shell_exec_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=file_shell_exec_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

file_shell_exec_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=file_shell_exec_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# File Shell Exec Specification

## Scenarios

### File Shell Ext

#### executes shell commands and returns stdout with exit code

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell("printf hello")
val stdout = result.0
val exit_code = result.2

expect(exit_code).to_equal(0)
expect(stdout).to_equal("hello")
```

</details>

#### returns non-zero exit code for failing commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell("false")
expect(result.2).to_equal(1)
```

</details>

#### captures stderr from shell commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell("printf errmsg >&2")
expect(result.1).to_contain("errmsg")
```

</details>

#### returns trimmed stdout from shell_output

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = shell_output("printf '  trimmed  '")
expect(out).to_equal("trimmed")
```

</details>

#### writes overwrites sizes and deletes temporary files

1. file delete
   - Expected: shell("test -f /tmp/simple_test_file_shell_exec_spec.txt").2 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/simple_test_file_shell_exec_spec.txt"

expect(file_write(path, "first")).to_equal(true)
expect(shell_output("cat /tmp/simple_test_file_shell_exec_spec.txt")).to_equal("first")

expect(file_write(path, "second")).to_equal(true)
expect(shell_output("cat /tmp/simple_test_file_shell_exec_spec.txt")).to_equal("second")
expect(file_size(path)).to_be_greater_than(0)

file_delete(path)
expect(shell("test -f /tmp/simple_test_file_shell_exec_spec.txt").2).to_equal(1)
```

</details>

#### returns zero size for missing files

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val size = file_size("/tmp/simple_test_file_shell_nonexistent_size.txt")
expect(size).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/io/file_shell_exec_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- File Shell Ext

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
