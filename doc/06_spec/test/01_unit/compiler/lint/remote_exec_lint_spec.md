# remote_exec_lint_spec

> Catches lines starting with '+' or '-' followed by 4+ spaces,

<!-- sdn-diagram:id=remote_exec_lint_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=remote_exec_lint_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

remote_exec_lint_spec -> std
remote_exec_lint_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=remote_exec_lint_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# remote_exec_lint_spec

Catches lines starting with '+' or '-' followed by 4+ spaces,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lint/remote_exec_lint_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Diff Marker Detection

    Catches lines starting with '+' or '-' followed by 4+ spaces,
    which look like accidentally pasted diff hunks.

## Scenarios

### RJIT001: Diff markers in source

#### when source contains diff-like lines

#### detects plus-marker diff hunk

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn main():\n+    val x = 1\n    val y = 2\n"
val warnings = lint_diff_markers(source, "test.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].code).to_equal("RJIT001")
expect(warnings[0].line_num).to_equal(2)
```

</details>

#### detects minus-marker diff hunk

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn main():\n-    val x = 1\n    val y = 2\n"
val warnings = lint_diff_markers(source, "test.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].code).to_equal("RJIT001")
```

</details>

#### when source is clean

#### ignores comment lines with dash

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "# - this is a comment\nfn main():\n    pass\n"
val warnings = lint_diff_markers(source, "test.spl")
expect(warnings.len()).to_equal(0)
```

</details>

#### ignores normal indented code

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn main():\n    val x = 1\n    val y = 2\n"
val warnings = lint_diff_markers(source, "test.spl")
expect(warnings.len()).to_equal(0)
```

</details>

#### ignores short plus/minus lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "+x\n-y\n"
val warnings = lint_diff_markers(source, "test.spl")
expect(warnings.len()).to_equal(0)
```

</details>

#### ignores diff markers inside docstrings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn main():\n    \"\"\"\n+    added line\n    \"\"\"\n    pass\n"
val warnings = lint_diff_markers(source, "test.spl")
expect(warnings.len()).to_equal(0)
```

</details>

### RJIT002: Leading space corruption

#### when file has leading-space corruption

#### detects space before fn keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = " fn main():\n     val x = 1\n"
val warnings = lint_leading_space_corruption(source, "test.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].code).to_equal("RJIT002")
```

</details>

#### detects space before class keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = " class Foo:\n     x: i64\n"
val warnings = lint_leading_space_corruption(source, "test.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].code).to_equal("RJIT002")
```

</details>

#### detects space before use keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = " use std.io_runtime\n"
val warnings = lint_leading_space_corruption(source, "test.spl")
expect(warnings.len()).to_be_greater_than(0)
```

</details>

#### when file is clean

#### accepts normal fn declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn main():\n    val x = 1\n"
val warnings = lint_leading_space_corruption(source, "test.spl")
expect(warnings.len()).to_equal(0)
```

</details>

#### accepts file starting with comment

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "# Header comment\nfn main():\n    pass\n"
val warnings = lint_leading_space_corruption(source, "test.spl")
expect(warnings.len()).to_equal(0)
```

</details>

#### accepts file starting with blank lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "\n\nfn main():\n    pass\n"
val warnings = lint_leading_space_corruption(source, "test.spl")
expect(warnings.len()).to_equal(0)
```

</details>

### RJIT004: Wrong shell import in library code

#### when lib code uses app.io

#### detects use app.io in lib path

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "use app.io\n\nfn helper():\n    pass\n"
val warnings = lint_wrong_shell_import(source, "src/lib/common/helpers.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].code).to_equal("RJIT004")
```

</details>

#### detects import app.io in lib path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "import app.io\n\nfn helper():\n    pass\n"
val warnings = lint_wrong_shell_import(source, "src/lib/common/helpers.spl")
expect(warnings.len()).to_be_greater_than(0)
```

</details>

#### detects use app.io.println in lib path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "use app.io.println\n\nfn helper():\n    pass\n"
val warnings = lint_wrong_shell_import(source, "src/lib/nogc_sync_mut/util.spl")
expect(warnings.len()).to_be_greater_than(0)
```

</details>

#### when import is valid

#### ignores app.io in app code

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "use app.io\n\nfn main():\n    pass\n"
val warnings = lint_wrong_shell_import(source, "src/app/cli/main.spl")
expect(warnings.len()).to_equal(0)
```

</details>

#### ignores std.io_runtime in lib code

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "use std.io_runtime\n\nfn helper():\n    pass\n"
val warnings = lint_wrong_shell_import(source, "src/lib/common/helpers.spl")
expect(warnings.len()).to_equal(0)
```

</details>

#### ignores app.io in test code

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "use app.io\n\nfn test_helper():\n    pass\n"
val warnings = lint_wrong_shell_import(source, "test/unit/some_spec.spl")
expect(warnings.len()).to_equal(0)
```

</details>

#### ignores comment containing app.io

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "# use app.io is deprecated\nuse std.io_runtime\n"
val warnings = lint_wrong_shell_import(source, "src/lib/common/helpers.spl")
expect(warnings.len()).to_equal(0)
```

</details>

### RJIT005: Zero-capacity MemoryMap

#### when MemoryMap has zero capacity

#### detects zero data capacity with same identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "val mm = MemoryMap(data_start: base, data_end: base, code_start: 0, code_end: 4096)\n"
val warnings = lint_zero_capacity_memory_map(source, "test.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].code).to_equal("RJIT005")
expect(warnings[0].message).to_contain("data")
```

</details>

#### detects zero code capacity with same literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "val mm = MemoryMap(data_start: 0, data_end: 4096, code_start: 0, code_end: 0)\n"
val warnings = lint_zero_capacity_memory_map(source, "test.spl")
expect(warnings.len()).to_be_greater_than(0)
expect(warnings[0].code).to_equal("RJIT005")
expect(warnings[0].message).to_contain("code")
```

</details>

#### detects both zero data and code capacity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "val mm = MemoryMap(data_start: 0, data_end: 0, code_start: 0, code_end: 0)\n"
val warnings = lint_zero_capacity_memory_map(source, "test.spl")
expect(warnings.len()).to_equal(2)
```

</details>

#### when MemoryMap is valid

#### accepts different data start and end

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "val mm = MemoryMap(data_start: 0, data_end: 4096, code_start: 4096, code_end: 8192)\n"
val warnings = lint_zero_capacity_memory_map(source, "test.spl")
expect(warnings.len()).to_equal(0)
```

</details>

#### accepts multiline constructor with valid values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "val mm = MemoryMap(\n    data_start: 0,\n    data_end: 4096,\n    code_start: 4096,\n    code_end: 8192\n)\n"
val warnings = lint_zero_capacity_memory_map(source, "test.spl")
expect(warnings.len()).to_equal(0)
```

</details>

### RemoteExecLintWarning formatting

#### produces formatted output

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = RemoteExecLintWarning(
    code: "RJIT001",
    severity: "WARNING",
    message: "test message",
    hint: "test hint",
    line_num: 42,
    file_path: "foo.spl"
)
val output = w.fmt()
expect(output).to_contain("RJIT001")
expect(output).to_contain("WARNING")
expect(output).to_contain("foo.spl")
expect(output).to_contain("42")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
