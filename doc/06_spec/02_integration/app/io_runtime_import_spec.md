# Io Runtime Import Specification

> <details>

<!-- sdn-diagram:id=io_runtime_import_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=io_runtime_import_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

io_runtime_import_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=io_runtime_import_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Io Runtime Import Specification

## Scenarios

### std.io_runtime imports

<details>
<summary>Advanced: shell returns ShellResult</summary>

#### shell returns ShellResult _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = shell("echo hello")
expect(result.exit_code).to_equal(0)
expect(result.stdout.trim()).to_equal("hello")
```

</details>


</details>

<details>
<summary>Advanced: shell_output returns trimmed stdout</summary>

#### shell_output returns trimmed stdout _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val out = shell_output("echo world")
expect(out).to_equal("world")
```

</details>


</details>

<details>
<summary>Advanced: shell_bool returns bool</summary>

#### shell_bool returns bool _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(shell_bool("true")).to_equal(true)
expect(shell_bool("false")).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: file_write and file_read round-trip</summary>

#### file_write and file_read round-trip _(slow)_

1. file write
   - Expected: content.trim() equals `hello io_runtime`
2. file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/io_runtime_test_{cwd().len()}.txt"
file_write(path, "hello io_runtime")
val content = file_read(path)
expect(content.trim()).to_equal("hello io_runtime")
file_delete(path)
```

</details>


</details>

<details>
<summary>Advanced: file_exists works</summary>

#### file_exists works _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("/tmp")).to_equal(true)
expect(file_exists("/tmp/nonexistent_io_runtime_test_xyz")).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: env_get and env_set work</summary>

#### env_get and env_set work _(slow)_

1. env set
   - Expected: v equals `test_value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
env_set("IO_RUNTIME_TEST_VAR", "test_value")
val v = env_get("IO_RUNTIME_TEST_VAR")
expect(v).to_equal("test_value")
```

</details>


</details>

<details>
<summary>Advanced: cwd returns non-empty</summary>

#### cwd returns non-empty _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = cwd()
val has_content = dir.len() > 0
expect(has_content).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: host_os returns known value</summary>

#### host_os returns known value _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val os = host_os()
val is_known = os == "linux" or os == "macos" or os == "freebsd"
expect(is_known).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: host_arch returns known value</summary>

#### host_arch returns known value _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arch = host_arch()
val is_known = arch == "x86_64" or arch == "aarch64"
expect(is_known).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/io_runtime_import_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- std.io_runtime imports

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 9 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
