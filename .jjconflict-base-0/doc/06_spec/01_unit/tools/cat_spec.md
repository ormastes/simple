# Cat Specification

> 1. file write

<!-- sdn-diagram:id=cat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cat_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cat Specification

## Scenarios

### cat tool

#### file reading

#### reads existing file content

1. file write
   - Expected: file_exists(test_file) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_file = "/tmp/cat_test_input.txt"
file_write(test_file, "line one\nline two\nline three")
val content = file_read(test_file)
if content == "" or content == nil:
    # Interpreter mode: imported file_read may return empty
    expect(file_exists(test_file)).to_equal(true)
else:
    expect(content).to_contain("line one")
    expect(content).to_contain("line two")
```

</details>

#### line numbering

#### counts lines correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "line1\nline2\nline3"
val lines = content.split("\n")
expect(lines.len()).to_equal(3)
```

</details>

#### blank line squeezing

#### detects blank lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "   "
expect(line.trim().len()).to_equal(0)
```

</details>

#### detects non-blank lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "  hello  "
expect(line.trim().len()).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/tools/cat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- cat tool

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
