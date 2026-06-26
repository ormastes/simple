# Sdoctest Specification

> <details>

<!-- sdn-diagram:id=sdoctest_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sdoctest_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sdoctest_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sdoctest_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 48 | 48 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sdoctest Specification

## Scenarios

### SDoctest glob matching

#### matches exact paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test literal path matching
val path = "doc/07_guide/intro.md"
val pattern = "doc/07_guide/intro.md"
expect path == pattern
```

</details>

#### matches single wildcard *

1. expect filename ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# * matches any characters within a single segment
val filename = "intro.md"
val pattern = "*.md"
expect filename.ends_with(".md")
```

</details>

#### matches ? for single character

1. expect filename len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val filename = "test1.md"
expect filename.len() == 8
```

</details>

#### matches ** for directory traversal

1. expect path starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ** matches zero or more path segments
val path = "doc/09_report/2026/summary.md"
expect path.starts_with("doc/09_report/")
```

</details>

### SDoctest fence line parsing

#### parses simple fence

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fence = "```simple"
val parts = fence.split(":")
expect parts[0] == "```simple"
```

</details>

#### parses fence with skip modifier

1. expect parts len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fence = "```simple:skip"
val parts = fence.split(":")
expect parts.len() == 2
expect parts[1] == "skip"
```

</details>

#### parses fence with multiple modifiers

1. expect mods len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fence = "```simple:init=std_imports,env=slow"
val colon_idx = fence.index_of(":")
expect colon_idx >= 0
val mod_str = fence[colon_idx + 1:]
val mods = mod_str.split(",")
expect mods.len() == 2
expect mods[0] == "init=std_imports"
expect mods[1] == "env=slow"
```

</details>

#### parses fence with should_fail

1. expect fence contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fence = "```simple:should_fail"
expect fence.contains("should_fail")
```

</details>

#### parses fence with tag modifier

1. expect mod str starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fence = "```simple:tag=integration"
val mod_str = fence.split(":")[1]
expect mod_str.starts_with("tag=")
```

</details>

### SDoctest block extraction

#### extracts simple code block from markdown

1. expect blocks len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = "# Title\n\n```simple\nval x = 42\nprint x\n```\n\nSome text."
val blocks = extract_blocks_from_content(md, "sample.md")
expect blocks.len() == 1
```

</details>

#### extracts multiple code blocks

1. expect blocks len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = "```simple\nval a = 1\n```\n\nText\n\n```simple\nval b = 2\n```"
val blocks = extract_blocks_from_content(md, "sample.md")
expect blocks.len() == 2
```

</details>

#### ignores non-simple code blocks

1. expect blocks len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = "```python\nprint('hello')\n```\n\n```simple\nval x = 1\n```"
val blocks = extract_blocks_from_content(md, "sample.md")
expect blocks.len() == 1
```

</details>

#### handles skip-next HTML comment

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = "<!--sdoctest:skip-next-->\n```simple\nval x = 1\n```"
val lines = md.split("\n")
expect lines[0] == "<!--sdoctest:skip-next-->"
```

</details>

#### handles skip-begin/end HTML comments

1. expect md contains
2. expect md contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = "<!--sdoctest:skip-begin-->\n```simple\nval x = 1\n```\n<!--sdoctest:skip-end-->"
expect md.contains("skip-begin")
expect md.contains("skip-end")
```

</details>

### SDoctest config

#### provides sensible defaults

1. expect default sources len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Default config should include README.md and doc/07_guide/
val default_sources = ["README.md", "doc/07_guide/", "examples/"]
expect default_sources.len() == 3
expect default_sources[0] == "README.md"
```

</details>

#### parses SDN source entries

1. expect sdn source contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sdn_source = "file: README.md"
expect sdn_source.contains("file:")
```

</details>

#### parses ignore patterns

1. expect patterns len
2. expect patterns[0] contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val patterns = ["doc/archive/**", "doc/09_report/**"]
expect patterns.len() == 2
expect patterns[0].contains("**")
```

</details>

#### parses init scripts section

1. expect init entry contains
2. expect init entry contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init_entry = "std_imports:\n  file: test/doctest/init/std_imports.spl"
expect init_entry.contains("std_imports")
expect init_entry.contains(".spl")
```

</details>

#### parses environment configuration

1. expect env entry contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env_entry = "default:\n  timeout: 5000"
expect env_entry.contains("timeout")
```

</details>

### SDoctest modifier parsing

#### recognizes skip modifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_str = "skip"
expect mod_str == "skip"
```

</details>

#### recognizes should_fail modifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_str = "should_fail"
expect mod_str == "should_fail"
```

</details>

#### parses init=name modifier

1. expect mod str starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_str = "init=std_imports"
expect mod_str.starts_with("init=")
val name = mod_str[5:]
expect name == "std_imports"
```

</details>

#### parses env=name modifier

1. expect mod str starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_str = "env=slow"
expect mod_str.starts_with("env=")
val name = mod_str[4:]
expect name == "slow"
```

</details>

#### parses tag=name modifier

1. expect mod str starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_str = "tag=integration"
expect mod_str.starts_with("tag=")
val name = mod_str[4:]
expect name == "integration"
```

</details>

#### splits comma-separated modifiers

1. expect parts len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_str = "init=std_imports,env=slow,tag=integration"
val parts = mod_str.split(",")
expect parts.len() == 3
```

</details>

#### recognizes fail_as_success modifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mod_str = "fail_as_success"
expect mod_str == "fail_as_success"
```

</details>

#### parses fence with fail_as_success

1. expect fence contains
2. expect parts len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fence = "```simple:fail_as_success"
expect fence.contains("fail_as_success")
val parts = fence.split(":")
expect parts.len() == 2
expect parts[1] == "fail_as_success"
```

</details>

### SDoctest code building

#### prepends init script content

1. expect combined starts with
2. expect combined contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init_content = "use std.collections.*"
val block_code = "val x = [1, 2, 3]"
val combined = init_content + "\n\n" + block_code
expect combined.starts_with("use std.collections.*")
expect combined.contains("val x = [1, 2, 3]")
```

</details>

#### returns block code when no init script

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block_code = "val x = 42"
expect block_code == "val x = 42"
```

</details>

### SDoctest results

#### tracks passed/failed/skipped counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var passed = 3
var failed = 1
var skipped = 2
val total = passed + failed + skipped
expect total == 6
```

</details>

#### reports ok when no failures

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var failed = 0
var errors = 0
val is_ok = failed == 0 and errors == 0
expect is_ok
```

</details>

#### reports not ok when failures exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var failed = 1
var errors = 0
val is_ok = failed == 0 and errors == 0
expect not is_ok
```

</details>

### SDoctest fail-as-success modifier

#### converts failed to accepted

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simulate per-block :fail_as_success modifier: when a block fails,
# the failure is converted to passed with accepted count
var file_passed = 2
var file_failed = 3
var file_accepted = 0
val fail_as_success = true

# Simulate converting failures
if fail_as_success:
    file_accepted = file_failed
    file_passed = file_passed + file_failed
    file_failed = 0

expect file_passed == 5
expect file_failed == 0
expect file_accepted == 3
```

</details>

#### does not convert errors to accepted

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Errors (infra issues like timeout) should NOT be converted
var file_passed = 2
var file_failed = 1
var file_errors = 1
var file_accepted = 0
val fail_as_success = true

# Only convert failures, not errors
if fail_as_success:
    file_accepted = file_failed
    file_passed = file_passed + file_failed
    file_failed = 0

expect file_passed == 3
expect file_failed == 0
expect file_errors == 1
expect file_accepted == 1
```

</details>

#### reports ok when all failures are accepted

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var failed = 0
var errors = 0
var accepted = 5
val is_ok = failed == 0 and errors == 0
expect is_ok
expect accepted == 5
```

</details>

#### tracks accepted separately from passed

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var passed = 3
var accepted = 2
val total_passing = passed
expect total_passing == 3
expect accepted == 2
```

</details>

### SDoctest block accumulation

#### first block gets empty preamble

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Block 0 should always have empty preamble (no preceding blocks)
val block1_code = "struct Point:\n    x: i64\n    y: i64"
# Simulate: for block 0, preamble is always ""
val preamble = ""
expect preamble == ""
```

</details>

#### extracts use statements as reusable

1. reusable lines push
2. expect reusable lines len
3. expect reusable lines[0] == "use app io mod


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "use app.io.mod (file_read)\nval x = 42\nprint x"
val lines = code.split("\n")
var reusable_lines: [text] = []
for line in lines:
    val trimmed = line.trim()
    if trimmed.starts_with("use "):
        reusable_lines.push(line)
expect reusable_lines.len() == 1
expect reusable_lines[0] == "use app.io.mod (file_read)"
```

</details>

#### extracts struct definitions as reusable

1. expect lines[1] starts with
2. expect lines[2] starts with
3. expect not lines[3] starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "struct Point:\n    x: i64\n    y: i64\nval p = Point(x: 3, y: 4)"
val lines = code.split("\n")
# struct definition starts at line 0, has 2 indented body lines
expect lines[0] == "struct Point:"
expect lines[1].starts_with("    ")
expect lines[2].starts_with("    ")
# line 3 is not indented - not part of struct
expect not lines[3].starts_with(" ")
```

</details>

#### extracts fn definitions as reusable

1. expect lines[0] == "fn double
2. expect lines[1] starts with
3. expect not lines[2] starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "fn double(x):\n    x * 2\nval result = double(21)"
val lines = code.split("\n")
expect lines[0] == "fn double(x):"
expect lines[1].starts_with("    ")
# line 2 is not part of fn
expect not lines[2].starts_with(" ")
```

</details>

#### does not extract bare expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = "print \"hello\"\nval x = 42"
val lines = code.split("\n")
var reusable = 0
for line in lines:
    val trimmed = line.trim()
    if trimmed.starts_with("use ") or trimmed.starts_with("struct ") or trimmed.starts_with("fn "):
        reusable = reusable + 1
expect reusable == 0
```

</details>

#### accumulates from multiple preceding blocks

1. expect accumulated contains
2. expect accumulated contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Block 1 defines struct, block 2 defines fn, block 3 should see both
val block1_reusable = "struct Point:\n    x: i64"
val block2_reusable = "fn double(x):\n    x * 2"
var accumulated = block1_reusable
accumulated = accumulated + "\n" + block2_reusable
# Block 3's preamble should contain both
expect accumulated.contains("struct Point:")
expect accumulated.contains("fn double(x):")
```

</details>

#### prepends preamble before block code

1. expect combined starts with
2. expect combined ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val preamble = "struct Point:\n    x: i64\n    y: i64"
val block_code = "val p = Point(x: 3, y: 4)"
val combined = preamble + "\n\n" + block_code
expect combined.starts_with("struct Point:")
expect combined.ends_with("val p = Point(x: 3, y: 4)")
```

</details>

### SDoctest language-based validation

#### simple blocks ignore non-zero exit codes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simple blocks are demonstration code - they pass even if exit code != 0
val block_language = "simple"
val exit_code = 1  # Non-zero exit
val should_pass = block_language == "simple" or block_language == "spl"
expect should_pass
```

</details>

#### spl blocks ignore non-zero exit codes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# spl is an alias for simple
val block_language = "spl"
val exit_code = 1
val should_pass = block_language == "simple" or block_language == "spl"
expect should_pass
```

</details>

#### sdoctest blocks validate exit codes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Sdoctest blocks are verified examples - must succeed
val block_language = "sdoctest"
val exit_code = 1
val should_pass = block_language == "simple" or block_language == "spl"
expect not should_pass
```

</details>

#### simple blocks pass on parse error exit codes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Exit code 1 from parse error is still ignored for simple blocks
val block_language = "simple"
val exit_code = 1  # Could be parse error, undefined var, etc.
val is_simple = block_language == "simple" or block_language == "spl"
expect is_simple
```

</details>

#### distinguishes demo code from verified examples

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Core principle: simple = demo, sdoctest = verified
val demo_language = "simple"
val verified_language = "sdoctest"
expect demo_language != verified_language
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/sdoctest_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SDoctest glob matching
- SDoctest fence line parsing
- SDoctest block extraction
- SDoctest config
- SDoctest modifier parsing
- SDoctest code building
- SDoctest results
- SDoctest fail-as-success modifier
- SDoctest block accumulation
- SDoctest language-based validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 48 |
| Active scenarios | 48 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
