# Group Comment Detection Specification

> <details>

<!-- sdn-diagram:id=group_comment_detection_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=group_comment_detection_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

group_comment_detection_spec -> std
group_comment_detection_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=group_comment_detection_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Group Comment Detection Specification

## Scenarios

### Variable Group Detection

#### detects consecutive var declarations

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "var count = 0\nvar total = 0\nvar sum = 0"
val groups = detect_variable_groups("test.spl", source)

expect(groups.len()).to_equal(1)
val group = groups[0]
expect(group.var_count).to_equal(3)
expect(group.var_names[0]).to_equal("count")
expect(group.var_names[1]).to_equal("total")
expect(group.var_names[2]).to_equal("sum")
```

</details>

#### detects consecutive val declarations

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "val name = 'Alice'\nval age = 30\nval city = 'NYC'"
val groups = detect_variable_groups("test.spl", source)

expect(groups.len()).to_equal(1)
val group = groups[0]
expect(group.var_count).to_equal(3)
```

</details>

#### detects mixed var and val declarations

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "var x = 1\nval y = 2\nvar z = 3"
val groups = detect_variable_groups("test.spl", source)

expect(groups.len()).to_equal(1)
expect(groups[0].var_count).to_equal(3)
```

</details>

#### ignores single variable declarations

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "var count = 0\n\nfn foo(): pass\n\nvar total = 0"
val groups = detect_variable_groups("test.spl", source)

expect(groups.len()).to_equal(0)
```

</details>

#### handles empty lines within groups

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "var x = 1\n\nvar y = 2\n\nvar z = 3"
val groups = detect_variable_groups("test.spl", source)

expect(groups.len()).to_equal(1)
expect(groups[0].var_count).to_equal(3)
```

</details>

#### handles comments within groups

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "var x = 1\n# intermediate comment\nvar y = 2\nvar z = 3"
val groups = detect_variable_groups("test.spl", source)

expect(groups.len()).to_equal(1)
expect(groups[0].var_count).to_equal(3)
```

</details>

#### splits groups on non-empty, non-comment lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "var a = 1\nvar b = 2\nfn foo(): pass\nvar c = 3\nvar d = 4"
val groups = detect_variable_groups("test.spl", source)

expect(groups.len()).to_equal(2)
expect(groups[0].var_count).to_equal(2)
expect(groups[1].var_count).to_equal(2)
```

</details>

#### extracts variable names with type annotations

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "var count: i64 = 0\nvar total: i64 = 0"
val groups = detect_variable_groups("test.spl", source)

expect(groups.len()).to_equal(1)
val group = groups[0]
expect(group.var_names[0]).to_equal("count")
expect(group.var_names[1]).to_equal("total")
```

</details>

#### extracts variable names with array types

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "var items: [text] = []\nvar names: [text] = []"
val groups = detect_variable_groups("test.spl", source)

expect(groups.len()).to_equal(1)
val group = groups[0]
expect(group.var_names[0]).to_equal("items")
expect(group.var_names[1]).to_equal("names")
```

</details>

### Group Comment Detection

#### detects comment immediately before group

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "# Counter variables\nvar count = 0\nvar total = 0"
val groups = detect_variable_groups("test.spl", source)

expect(groups.len()).to_equal(1)
val group = groups[0]
assert_true(group.has_group_comment == true)
```

</details>

#### detects comment 2 lines before group

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "# Counter variables\n\nvar count = 0\nvar total = 0"
val groups = detect_variable_groups("test.spl", source)

expect(groups.len()).to_equal(1)
val group = groups[0]
assert_true(group.has_group_comment == true)
```

</details>

#### marks group without comment

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "var count = 0\nvar total = 0"
val groups = detect_variable_groups("test.spl", source)

expect(groups.len()).to_equal(1)
val group = groups[0]
assert_true(group.has_group_comment == false)
```

</details>

#### does not detect comment too far before

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "# Some comment\n\n\n\nvar count = 0\nvar total = 0"
val groups = detect_variable_groups("test.spl", source)

expect(groups.len()).to_equal(1)
val group = groups[0]
assert_true(group.has_group_comment == false)
```

</details>

### Comment Suggestion

#### suggests 'Constants' for UPPER_CASE variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val group = VariableGroup(
    file_path: "test.spl",
    start_line: 1,
    end_line: 3,
    var_names: ["MAX_SIZE", "MIN_SIZE", "DEFAULT_SIZE"],
    var_count: 3,
    has_group_comment: false,
    suggested_comment: ""
)
val suggestion = suggest_group_comment(group)

expect(suggestion).to_equal("# Constants")
```

</details>

#### suggests prefix pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val group = VariableGroup(
    file_path: "test.spl",
    start_line: 1,
    end_line: 3,
    var_names: ["config_name", "config_port", "config_host"],
    var_count: 3,
    has_group_comment: false,
    suggested_comment: ""
)
val suggestion = suggest_group_comment(group)

expect(suggestion).to_equal("# config_* variables")
```

</details>

#### suggests suffix pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val group = VariableGroup(
    file_path: "test.spl",
    start_line: 1,
    end_line: 3,
    var_names: ["item_count", "total_count", "error_count"],
    var_count: 3,
    has_group_comment: false,
    suggested_comment: ""
)
val suggestion = suggest_group_comment(group)

expect(suggestion).to_equal("# *_count variables")
```

</details>

#### suggests 'Configuration variables' for config pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val group = VariableGroup(
    file_path: "test.spl",
    start_line: 1,
    end_line: 2,
    var_names: ["server_config", "client_config"],
    var_count: 2,
    has_group_comment: false,
    suggested_comment: ""
)
val suggestion = suggest_group_comment(group)

expect(suggestion).to_equal("# Configuration variables")
```

</details>

#### suggests 'State variables' for state pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val group = VariableGroup(
    file_path: "test.spl",
    start_line: 1,
    end_line: 2,
    var_names: ["parser_state", "lexer_state"],
    var_count: 2,
    has_group_comment: false,
    suggested_comment: ""
)
val suggestion = suggest_group_comment(group)

expect(suggestion).to_equal("# State variables")
```

</details>

#### suggests 'Counter variables' for count pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val group = VariableGroup(
    file_path: "test.spl",
    start_line: 1,
    end_line: 2,
    var_names: ["test_count", "failure_count"],
    var_count: 2,
    has_group_comment: false,
    suggested_comment: ""
)
val suggestion = suggest_group_comment(group)

expect(suggestion).to_equal("# Counter variables")
```

</details>

#### suggests 'Flag variables' for flag pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val group = VariableGroup(
    file_path: "test.spl",
    start_line: 1,
    end_line: 2,
    var_names: ["is_valid", "has_error"],
    var_count: 2,
    has_group_comment: false,
    suggested_comment: ""
)
val suggestion = suggest_group_comment(group)

expect(suggestion).to_equal("# Flag variables")
```

</details>

#### suggests default message for generic groups

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val group = VariableGroup(
    file_path: "test.spl",
    start_line: 1,
    end_line: 2,
    var_names: ["x", "y"],
    var_count: 2,
    has_group_comment: false,
    suggested_comment: ""
)
val suggestion = suggest_group_comment(group)

expect(suggestion).to_equal("# Group of 2 related variables")
```

</details>

### Warning Generation

#### emits warnings for groups without comments

- assert true
- assert true
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val group = VariableGroup(
    file_path: "test.spl",
    start_line: 10,
    end_line: 12,
    var_names: ["count", "total", "sum"],
    var_count: 3,
    has_group_comment: false,
    suggested_comment: "# Counter variables"
)
val groups = [group]
val warnings = emit_group_comment_warnings(groups)

expect(warnings.len()).to_equal(2)
val first = warnings[0]
val second = warnings[1]
assert_true(first.contains("test.spl:10") == true)
assert_true(first.contains("Group of 3 variables") == true)
assert_true(second.contains("Suggestion:") == true)
assert_true(second.contains("Counter variables") == true)
```

</details>

#### does not emit warnings for groups with comments

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val group = VariableGroup(
    file_path: "test.spl",
    start_line: 10,
    end_line: 12,
    var_names: ["count", "total"],
    var_count: 2,
    has_group_comment: true,
    suggested_comment: ""
)
val groups = [group]
val warnings = emit_group_comment_warnings(groups)

expect(warnings.len()).to_equal(0)
```

</details>

#### formats variable names in warnings

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val group = VariableGroup(
    file_path: "test.spl",
    start_line: 1,
    end_line: 2,
    var_names: ["x", "y"],
    var_count: 2,
    has_group_comment: false,
    suggested_comment: "# Variables"
)
val groups = [group]
val warnings = emit_group_comment_warnings(groups)

val msg = warnings[0]
assert_true(msg.contains("x, y") == true)
```

</details>

### Tag Classification

#### tags group with comment as present

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val group = VariableGroup(
    file_path: "test.spl",
    start_line: 1,
    end_line: 2,
    var_names: ["x", "y"],
    var_count: 2,
    has_group_comment: true,
    suggested_comment: ""
)
val tags = classify_variable_group(group)

expect(tags[0]).to_equal("group_comment:present")
```

</details>

#### tags group without comment as missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val group = VariableGroup(
    file_path: "test.spl",
    start_line: 1,
    end_line: 2,
    var_names: ["x", "y"],
    var_count: 2,
    has_group_comment: false,
    suggested_comment: ""
)
val tags = classify_variable_group(group)

expect(tags[0]).to_equal("group_comment:missing")
```

</details>

#### tags config groups

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val group = VariableGroup(
    file_path: "test.spl",
    start_line: 1,
    end_line: 2,
    var_names: ["server_config", "client_config"],
    var_count: 2,
    has_group_comment: false,
    suggested_comment: "# Configuration variables"
)
val tags = classify_variable_group(group)

expect(tags[1]).to_equal("var_group:config")
```

</details>

#### tags state groups

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val group = VariableGroup(
    file_path: "test.spl",
    start_line: 1,
    end_line: 2,
    var_names: ["parser_state", "lexer_state"],
    var_count: 2,
    has_group_comment: false,
    suggested_comment: "# State variables"
)
val tags = classify_variable_group(group)

expect(tags[1]).to_equal("var_group:state")
```

</details>

#### tags constant groups

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val group = VariableGroup(
    file_path: "test.spl",
    start_line: 1,
    end_line: 2,
    var_names: ["MAX_SIZE", "MIN_SIZE"],
    var_count: 2,
    has_group_comment: false,
    suggested_comment: "# Constants"
)
val tags = classify_variable_group(group)

expect(tags[1]).to_equal("var_group:constants")
```

</details>

#### tags general groups

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val group = VariableGroup(
    file_path: "test.spl",
    start_line: 1,
    end_line: 2,
    var_names: ["x", "y"],
    var_count: 2,
    has_group_comment: false,
    suggested_comment: "# Group of 2 related variables"
)
val tags = classify_variable_group(group)

expect(tags[1]).to_equal("var_group:general")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/doc_coverage/group_comment_detection_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Variable Group Detection
- Group Comment Detection
- Comment Suggestion
- Warning Generation
- Tag Classification

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
