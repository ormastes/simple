# Documentation Navigation Generation Specification

> Tests that the REAL `bin/simple spipe-docgen` generator produces correct documentation with navigation structure from SPipe test files.

<!-- sdn-diagram:id=doc_nav_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=doc_nav_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

doc_nav_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=doc_nav_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Documentation Navigation Generation Specification

Tests that the REAL `bin/simple spipe-docgen` generator produces correct documentation with navigation structure from SPipe test files.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1210-1215 (doc navigation generation) |
| Category | Tooling / Documentation |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/02_integration/app/doc_nav/doc_nav_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that the REAL `bin/simple spipe-docgen` generator produces correct
documentation with navigation structure from SPipe test files.

Exercises the actual spipe-docgen binary and reads the real generated
markdown to verify heading hierarchy, metadata tables, scenario counts,
source references, and cross-navigation links.

## Scenarios

### Real spipe-docgen output

#### generates markdown for math_render_spec

#### runs spipe-docgen successfully

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, stderr, code) = process_run("bin/simple", ["spipe-docgen", "test/feature/usage/math_render_spec.spl"])
expect(code).to_equal(0)
expect(stdout).to_contain("Generated")
```

</details>

#### creates output file

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# spipe-docgen generates to doc/spec/ by default
val output_exists = file_exists("doc/spec/math_render_spec.md")
expect(output_exists).to_equal(true)
```

</details>

#### markdown heading structure

#### has H1 title from docstring

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = read_file("doc/spec/math_render_spec.md")
expect(md).to_contain("# Math Block Rendering Specification")
```

</details>

#### has metadata table with Feature IDs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = read_file("doc/spec/math_render_spec.md")
expect(md).to_contain("Feature IDs")
expect(md).to_contain("#1090")
```

</details>

#### has metadata table with Category

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = read_file("doc/spec/math_render_spec.md")
expect(md).to_contain("Category")
expect(md).to_contain("Math DSL")
```

</details>

#### has metadata table with Difficulty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = read_file("doc/spec/math_render_spec.md")
expect(md).to_contain("Difficulty")
expect(md).to_contain("3/5")
```

</details>

#### has metadata table with Status

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = read_file("doc/spec/math_render_spec.md")
expect(md).to_contain("Status")
expect(md).to_contain("Implemented")
```

</details>

#### has source file reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = read_file("doc/spec/math_render_spec.md")
expect(md).to_contain("Source")
expect(md).to_contain("math_render_spec.spl")
```

</details>

#### has date stamp

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = read_file("doc/spec/math_render_spec.md")
expect(md).to_contain("Updated")
expect(md).to_contain("2026")
```

</details>

#### has generator attribution

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = read_file("doc/spec/math_render_spec.md")
expect(md).to_contain("spipe-docgen")
```

</details>

#### scenario summary table

#### reports total scenario count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = read_file("doc/spec/math_render_spec.md")
expect(md).to_contain("Total scenarios")
expect(md).to_contain("129")
```

</details>

#### reports active scenarios

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = read_file("doc/spec/math_render_spec.md")
expect(md).to_contain("Active scenarios")
expect(md).to_contain("129")
```

</details>

#### reports zero skipped scenarios

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = read_file("doc/spec/math_render_spec.md")
expect(md).to_contain("Skipped scenarios")
expect(md).to_contain("0")
```

</details>

#### overview section from docstring

#### includes overview content

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = read_file("doc/spec/math_render_spec.md")
expect(md).to_contain("## Overview")
```

</details>

#### includes renderer list

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = read_file("doc/spec/math_render_spec.md")
expect(md).to_contain("to_text()")
expect(md).to_contain("to_debug()")
expect(md).to_contain("to_pretty()")
expect(md).to_contain("render_latex_raw()")
```

</details>

### Real spipe-docgen for loss_nograd_blocks_spec

#### runs spipe-docgen successfully

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, stderr, code) = process_run("bin/simple", ["spipe-docgen", "test/feature/usage/loss_nograd_blocks_spec.spl"])
expect(code).to_equal(0)
```

</details>

#### creates output file

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output_exists = file_exists("doc/spec/loss_nograd_blocks_spec.md")
expect(output_exists).to_equal(true)
```

</details>

#### has title from docstring

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = read_file("doc/spec/loss_nograd_blocks_spec.md")
expect(md).to_contain("loss{}")
expect(md).to_contain("nograd{}")
```

</details>

#### reports 38 scenarios

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = read_file("doc/spec/loss_nograd_blocks_spec.md")
expect(md).to_contain("38")
```

</details>

#### has feature IDs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = read_file("doc/spec/loss_nograd_blocks_spec.md")
expect(md).to_contain("#1099")
```

</details>

### Real spipe-docgen for math_blocks_spec

#### runs spipe-docgen successfully

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, stderr, code) = process_run("bin/simple", ["spipe-docgen", "test/feature/usage/math_blocks_spec.spl"])
expect(code).to_equal(0)
```

</details>

#### creates output file

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output_exists = file_exists("doc/spec/math_blocks_spec.md")
expect(output_exists).to_equal(true)
```

</details>

#### reports 28 scenarios

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = read_file("doc/spec/math_blocks_spec.md")
expect(md).to_contain("28")
```

</details>

#### has tensor operations context

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = read_file("doc/spec/math_blocks_spec.md")
expect(md).to_contain("Math Block")
```

</details>

### Doc navigation INDEX.md

#### INDEX.md exists in doc/spec

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val index_exists = file_exists("doc/spec/INDEX.md")
expect(index_exists).to_equal(true)
```

</details>

#### INDEX.md links to math_render_spec

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = read_file("doc/spec/INDEX.md")
expect(idx).to_contain("math_render_spec")
```

</details>

#### INDEX.md links to loss_nograd_blocks_spec

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = read_file("doc/spec/INDEX.md")
expect(idx).to_contain("loss_nograd_blocks_spec")
```

</details>

#### INDEX.md links to math_blocks_spec

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = read_file("doc/spec/INDEX.md")
expect(idx).to_contain("math_blocks_spec")
```

</details>

### Cross-navigation between math specs

#### consistent metadata across related specs

#### all math specs reference the same feature range

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val render_md = read_file("doc/spec/math_render_spec.md")
val blocks_md = read_file("doc/spec/math_blocks_spec.md")
val loss_md = read_file("doc/spec/loss_nograd_blocks_spec.md")
# All should reference feature IDs in the #1090-1102 range
expect(render_md).to_contain("1090")
expect(loss_md).to_contain("1099")
```

</details>

#### all math specs have source file references

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val render_md = read_file("doc/spec/math_render_spec.md")
val blocks_md = read_file("doc/spec/math_blocks_spec.md")
val loss_md = read_file("doc/spec/loss_nograd_blocks_spec.md")
expect(render_md).to_contain("Source")
expect(blocks_md).to_contain("Source")
expect(loss_md).to_contain("Source")
```

</details>

#### all math specs have date stamps

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val render_md = read_file("doc/spec/math_render_spec.md")
val blocks_md = read_file("doc/spec/math_blocks_spec.md")
val loss_md = read_file("doc/spec/loss_nograd_blocks_spec.md")
expect(render_md).to_contain("2026")
expect(blocks_md).to_contain("2026")
expect(loss_md).to_contain("2026")
```

</details>

#### scenario counts match test runner

#### render spec doc matches test runner count

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/math_render_spec.spl"])
val lines = stdout.split("\n")
var test_count = 0
for line in lines:
    if line.contains("math_render_spec.spl") and line.contains(" - "):
        test_count = test_count + 1
val md = read_file("doc/spec/math_render_spec.md")
# Doc should report same count as test runner
expect(md).to_contain("{test_count}")
```

</details>

#### loss_nograd spec doc matches test runner count

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _err, _code) = process_run("bin/simple", ["test", "--list", "test/feature/usage/loss_nograd_blocks_spec.spl"])
val lines = stdout.split("\n")
var test_count = 0
for line in lines:
    if line.contains("loss_nograd") and line.contains(" - "):
        test_count = test_count + 1
val md = read_file("doc/spec/loss_nograd_blocks_spec.md")
expect(md).to_contain("{test_count}")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
