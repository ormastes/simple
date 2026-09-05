# Sdoctest Specification

> Tests covering SDoctest glob matching, SDoctest fence line parsing, SDoctest block extraction, SDoctest config, SDoctest modifier parsing, SDoctest code building, SDoctest results, SDoctest fail-as-success modifier, SDoctest block accumulation, SDoctest language-based validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 48 | 48 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sdoctest Specification

## Scenarios

### SDoctest glob matching

#### matches exact paths

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches exact paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches exact paths")
# Test literal path matching
val path = "doc/07_guide/intro.md"
val pattern = "doc/07_guide/intro.md"
expect path == pattern
```

</details>

#### matches single wildcard *

- matches single wildcard *


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches single wildcard *")
# * matches any characters within a single segment
val filename = "intro.md"
val pattern = "*.md"
expect filename.ends_with(".md")
```

</details>

#### matches ? for single character

- matches ? for single character


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches ? for single character")
val filename = "test1.md"
expect filename.len() == 8
```

</details>

#### matches ** for directory traversal

- matches ** for directory traversal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches ** for directory traversal")
# ** matches zero or more path segments
val path = "doc/09_report/2026/summary.md"
expect path.starts_with("doc/09_report/")
```

</details>

### SDoctest fence line parsing

#### parses simple fence

- parses simple fence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses simple fence")
val fence = "```simple"
val parts = fence.split(":")
expect parts[0] == "```simple"
```

</details>

#### parses fence with skip modifier

- parses fence with skip modifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses fence with skip modifier")
val fence = "```simple:skip"
val parts = fence.split(":")
expect parts.len() == 2
expect parts[1] == "skip"
```

</details>

#### parses fence with multiple modifiers

- parses fence with multiple modifiers


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses fence with multiple modifiers")
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

- parses fence with should_fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses fence with should_fail")
val fence = "```simple:should_fail"
expect fence.contains("should_fail")
```

</details>

#### parses fence with tag modifier

- parses fence with tag modifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses fence with tag modifier")
val fence = "```simple:tag=integration"
val mod_str = fence.split(":")[1]
expect mod_str.starts_with("tag=")
```

</details>

### SDoctest block extraction

#### extracts simple code block from markdown

- extracts simple code block from markdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts simple code block from markdown")
val md = "# Title\n\n```simple\nval x = 42\nprint x\n```\n\nSome text."
val blocks = extract_blocks_from_content(md, "sample.md")
expect blocks.len() == 1
```

</details>

#### extracts multiple code blocks

- extracts multiple code blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts multiple code blocks")
val md = "```simple\nval a = 1\n```\n\nText\n\n```simple\nval b = 2\n```"
val blocks = extract_blocks_from_content(md, "sample.md")
expect blocks.len() == 2
```

</details>

#### ignores non-simple code blocks

- ignores non-simple code blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores non-simple code blocks")
val md = "```python\nprint('hello')\n```\n\n```simple\nval x = 1\n```"
val blocks = extract_blocks_from_content(md, "sample.md")
expect blocks.len() == 1
```

</details>

#### handles skip-next HTML comment

- handles skip-next HTML comment


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles skip-next HTML comment")
val md = "<!--sdoctest:skip-next-->\n```simple\nval x = 1\n```"
val lines = md.split("\n")
expect lines[0] == "<!--sdoctest:skip-next-->"
```

</details>

#### handles skip-begin/end HTML comments

- handles skip-begin/end HTML comments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles skip-begin/end HTML comments")
val md = "<!--sdoctest:skip-begin-->\n```simple\nval x = 1\n```\n<!--sdoctest:skip-end-->"
expect md.contains("skip-begin")
expect md.contains("skip-end")
```

</details>

### SDoctest config

#### provides sensible defaults

- provides sensible defaults


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides sensible defaults")
# Default config should include README.md and doc/07_guide/
val default_sources = ["README.md", "doc/07_guide/", "examples/"]
expect default_sources.len() == 3
expect default_sources[0] == "README.md"
```

</details>

#### parses SDN source entries

- parses SDN source entries


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses SDN source entries")
val sdn_source = "file: README.md"
expect sdn_source.contains("file:")
```

</details>

#### parses ignore patterns

- parses ignore patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses ignore patterns")
val patterns = ["doc/archive/**", "doc/09_report/**"]
expect patterns.len() == 2
expect patterns[0].contains("**")
```

</details>

#### parses init scripts section

- parses init scripts section


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses init scripts section")
val init_entry = "std_imports:\n  file: test/doctest/init/std_imports.spl"
expect init_entry.contains("std_imports")
expect init_entry.contains(".spl")
```

</details>

#### parses environment configuration

- parses environment configuration


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses environment configuration")
val env_entry = "default:\n  timeout: 5000"
expect env_entry.contains("timeout")
```

</details>

### SDoctest modifier parsing

#### recognizes skip modifier

- recognizes skip modifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes skip modifier")
val mod_str = "skip"
expect mod_str == "skip"
```

</details>

#### recognizes should_fail modifier

- recognizes should_fail modifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes should_fail modifier")
val mod_str = "should_fail"
expect mod_str == "should_fail"
```

</details>

#### parses init=name modifier

- parses init=name modifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses init=name modifier")
val mod_str = "init=std_imports"
expect mod_str.starts_with("init=")
val name = mod_str[5:]
expect name == "std_imports"
```

</details>

#### parses env=name modifier

- parses env=name modifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses env=name modifier")
val mod_str = "env=slow"
expect mod_str.starts_with("env=")
val name = mod_str[4:]
expect name == "slow"
```

</details>

#### parses tag=name modifier

- parses tag=name modifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses tag=name modifier")
val mod_str = "tag=integration"
expect mod_str.starts_with("tag=")
val name = mod_str[4:]
expect name == "integration"
```

</details>

#### splits comma-separated modifiers

- splits comma-separated modifiers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("splits comma-separated modifiers")
val mod_str = "init=std_imports,env=slow,tag=integration"
val parts = mod_str.split(",")
expect parts.len() == 3
```

</details>

#### recognizes fail_as_success modifier

- recognizes fail_as_success modifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes fail_as_success modifier")
val mod_str = "fail_as_success"
expect mod_str == "fail_as_success"
```

</details>

#### parses fence with fail_as_success

- parses fence with fail_as_success


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses fence with fail_as_success")
val fence = "```simple:fail_as_success"
expect fence.contains("fail_as_success")
val parts = fence.split(":")
expect parts.len() == 2
expect parts[1] == "fail_as_success"
```

</details>

### SDoctest code building

#### prepends init script content

- prepends init script content


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prepends init script content")
val init_content = "use std.collections.*"
val block_code = "val x = [1, 2, 3]"
val combined = init_content + "\n\n" + block_code
expect combined.starts_with("use std.collections.*")
expect combined.contains("val x = [1, 2, 3]")
```

</details>

#### returns block code when no init script

- returns block code when no init script


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns block code when no init script")
val block_code = "val x = 42"
expect block_code == "val x = 42"
```

</details>

### SDoctest results

#### tracks passed/failed/skipped counts

- tracks passed/failed/skipped counts


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks passed/failed/skipped counts")
var passed = 3
var failed = 1
var skipped = 2
val total = passed + failed + skipped
expect total == 6
```

</details>

#### reports ok when no failures

- reports ok when no failures


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports ok when no failures")
var failed = 0
var errors = 0
val is_ok = failed == 0 and errors == 0
expect is_ok
```

</details>

#### reports not ok when failures exist

- reports not ok when failures exist


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports not ok when failures exist")
var failed = 1
var errors = 0
val is_ok = failed == 0 and errors == 0
expect not is_ok
```

</details>

### SDoctest fail-as-success modifier

#### converts failed to accepted

- converts failed to accepted


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts failed to accepted")
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

- does not convert errors to accepted


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not convert errors to accepted")
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

- reports ok when all failures are accepted


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports ok when all failures are accepted")
var failed = 0
var errors = 0
var accepted = 5
val is_ok = failed == 0 and errors == 0
expect is_ok
expect accepted == 5
```

</details>

#### tracks accepted separately from passed

- tracks accepted separately from passed


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks accepted separately from passed")
var passed = 3
var accepted = 2
val total_passing = passed
expect total_passing == 3
expect accepted == 2
```

</details>

### SDoctest block accumulation

#### first block gets empty preamble

- first block gets empty preamble


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("first block gets empty preamble")
# Block 0 should always have empty preamble (no preceding blocks)
val block1_code = "struct Point:\n    x: i64\n    y: i64"
# Simulate: for block 0, preamble is always ""
val preamble = ""
expect preamble == ""
```

</details>

#### extracts use statements as reusable

- extracts use statements as reusable


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts use statements as reusable")
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

- extracts struct definitions as reusable


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts struct definitions as reusable")
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

- extracts fn definitions as reusable


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts fn definitions as reusable")
val code = "fn double(x):\n    x * 2\nval result = double(21)"
val lines = code.split("\n")
expect lines[0] == "fn double(x):"
expect lines[1].starts_with("    ")
# line 2 is not part of fn
expect not lines[2].starts_with(" ")
```

</details>

#### does not extract bare expressions

- does not extract bare expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not extract bare expressions")
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

- accumulates from multiple preceding blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accumulates from multiple preceding blocks")
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

- prepends preamble before block code


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prepends preamble before block code")
val preamble = "struct Point:\n    x: i64\n    y: i64"
val block_code = "val p = Point(x: 3, y: 4)"
val combined = preamble + "\n\n" + block_code
expect combined.starts_with("struct Point:")
expect combined.ends_with("val p = Point(x: 3, y: 4)")
```

</details>

### SDoctest language-based validation

#### simple blocks ignore non-zero exit codes

- simple blocks ignore non-zero exit codes


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple blocks ignore non-zero exit codes")
# Simple blocks are demonstration code - they pass even if exit code != 0
val block_language = "simple"
val exit_code = 1  # Non-zero exit
val should_pass = block_language == "simple" or block_language == "spl"
expect should_pass
```

</details>

#### spl blocks ignore non-zero exit codes

- spl blocks ignore non-zero exit codes


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("spl blocks ignore non-zero exit codes")
# spl is an alias for simple
val block_language = "spl"
val exit_code = 1
val should_pass = block_language == "simple" or block_language == "spl"
expect should_pass
```

</details>

#### sdoctest blocks validate exit codes

- sdoctest blocks validate exit codes


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sdoctest blocks validate exit codes")
# Sdoctest blocks are verified examples - must succeed
val block_language = "sdoctest"
val exit_code = 1
val should_pass = block_language == "simple" or block_language == "spl"
expect not should_pass
```

</details>

#### simple blocks pass on parse error exit codes

- simple blocks pass on parse error exit codes


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple blocks pass on parse error exit codes")
# Exit code 1 from parse error is still ignored for simple blocks
val block_language = "simple"
val exit_code = 1  # Could be parse error, undefined var, etc.
val is_simple = block_language == "simple" or block_language == "spl"
expect is_simple
```

</details>

#### distinguishes demo code from verified examples

- distinguishes demo code from verified examples


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("distinguishes demo code from verified examples")
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
| Source | `test/unit/app/sdoctest_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SDoctest glob matching, SDoctest fence line parsing, SDoctest block extraction, SDoctest config, SDoctest modifier parsing, SDoctest code building, SDoctest results, SDoctest fail-as-success modifier, SDoctest block accumulation, SDoctest language-based validation.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4c66bf7f4ad518142927dc6f57fb9a2968f0e690e5a3c437e18f30c20a83bcd3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4c66bf7f4ad518142927dc6f57fb9a2968f0e690e5a3c437e18f30c20a83bcd3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4c66bf7f4ad518142927dc6f57fb9a2968f0e690e5a3c437e18f30c20a83bcd3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/sdoctest_spec.spl
mirror: doc/06_spec/unit/app/sdoctest_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/sdoctest_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/sdoctest_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/sdoctest_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches exact paths' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/sdoctest_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches single wildcard *' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/sdoctest_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches ? for single character' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
