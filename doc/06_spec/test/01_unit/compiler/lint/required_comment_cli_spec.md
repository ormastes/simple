# Required Comment CLI Lint Coverage

> 1. var linter = Linter new

<!-- sdn-diagram:id=required_comment_cli_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=required_comment_cli_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

required_comment_cli_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=required_comment_cli_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Required Comment CLI Lint Coverage

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lint/required_comment_cli_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### required comment lint source path

#### emits REQC001 through Linter.lint_source

1. var linter = Linter new
   - Expected: has_code(results, "REQC001") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var linter = Linter.new()
val results = linter.lint_source("sample.spl", "fn f():\n    pass_todo\n")
expect(has_code(results, "REQC001")).to_equal(true)
```

</details>

#### emits REQC003 through Linter.lint_source

1. var linter = Linter new
   - Expected: has_code(results, "REQC003") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var linter = Linter.new()
val results = linter.lint_source("sample.spl", "fn f():\n    todo(\"fix\")\n")
expect(has_code(results, "REQC003")).to_equal(true)
```

</details>

#### emits REQC004 through Linter.lint_source

1. var linter = Linter new
   - Expected: has_code(results, "REQC004") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var linter = Linter.new()
val results = linter.lint_source("sample.spl", "fn f():\n    match x:\n        case _: 0\n")
expect(has_code(results, "REQC004")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
