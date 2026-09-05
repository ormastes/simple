# Sdoctest Extractor Specification

> Tests covering sdoctest extractor (hardening).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sdoctest Extractor Specification

## Scenarios

### sdoctest extractor (hardening)

#### fence + run-config marker extraction

#### extracts one block, strips >>> prompts, and drops the expected-output line for a sdoctest fence

- extracts one block, strips >>> prompts, and drops the expected-output line for a sdoctest fence
   - Expected: blocks.len() equals `1`
   - Expected: blocks[0].code equals `1 + 1`
   - Expected: blocks[0].get_run_config() equals `fast_env`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extracts one block, strips >>> prompts, and drops the expected-output line for a sdoctest fence")
val content = "<!--sdoctest:@fast_env-->\n```sdoctest\n>>> 1 + 1\n2\n```\n"
val blocks = extract_blocks_from_content(content: content, file_path: "doc/example.md")
expect(blocks.len()).to_equal(1)
expect(blocks[0].code).to_equal("1 + 1")
expect(blocks[0].get_run_config()).to_equal("fast_env")
```

</details>

#### extracts a plain ```simple fence verbatim (no prompt-stripping outside sdoctest fences)

- extracts a plain ```simple fence verbatim (no prompt-stripping outside sdoctest fences)
   - Expected: blocks.len() equals `1`
   - Expected: blocks[0].code equals `val x = 1 + 1`
   - Expected: blocks[0].language equals `simple`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extracts a plain ```simple fence verbatim (no prompt-stripping outside sdoctest fences)")
val content = "```simple\nval x = 1 + 1\n```\n"
val blocks = extract_blocks_from_content(content: content, file_path: "doc/example.md")
expect(blocks.len()).to_equal(1)
expect(blocks[0].code).to_equal("val x = 1 + 1")
expect(blocks[0].language).to_equal("simple")
```

</details>

#### skip-region marker

#### marks a block inside skip-begin/skip-end as skipped and leaves the next block untouched

- marks a block inside skip-begin/skip-end as skipped and leaves the next block untouched
   - Expected: blocks.len() equals `2`
   - Expected: blocks[0].has_modifier_skip() is true
   - Expected: blocks[1].has_modifier_skip() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("marks a block inside skip-begin/skip-end as skipped and leaves the next block untouched")
val content = "<!--sdoctest:skip-begin-->\n```simple\nval a = 1\n```\n<!--sdoctest:skip-end-->\n```simple\nval b = 2\n```\n"
val blocks = extract_blocks_from_content(content: content, file_path: "doc/example.md")
expect(blocks.len()).to_equal(2)
expect(blocks[0].has_modifier_skip()).to_equal(true)
expect(blocks[1].has_modifier_skip()).to_equal(false)
```

</details>

#### fence modifier parsing

#### parses init= and env= modifiers off the fence line

- parses init= and env= modifiers off the fence line
   - Expected: lang equals `simple`
   - Expected: block.get_init_name() equals `std_setup`
   - Expected: block.get_env_name() equals `slow`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses init= and env= modifiers off the fence line")
val (lang, mods) = parse_fence_line("```simple:init=std_setup,env=slow")
expect(lang).to_equal("simple")
val block = SdoctestBlock(source_file: "x", line_number: 0, code: "", language: lang, modifiers: mods)
expect(block.get_init_name()).to_equal("std_setup")
expect(block.get_env_name()).to_equal("slow")
```

</details>

#### deliberate-red: an unrecognized modifier token is silently dropped, not a crash

- deliberate-red: an unrecognized modifier token is silently dropped, not a crash
   - Expected: lang equals `simple`
   - Expected: mods.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("deliberate-red: an unrecognized modifier token is silently dropped, not a crash")
val (lang, mods) = parse_fence_line("```simple:unknown_totally_bogus_modifier")
expect(lang).to_equal("simple")
expect(mods.len()).to_equal(0)
```

</details>

#### extract_reusable_lines

#### keeps use-imports and fn definitions but drops bare expressions and prints

- keeps use-imports and fn definitions but drops bare expressions and prints
   - Expected: reusable does not contain `print(x)`
   - Expected: reusable does not contain `val x = 42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps use-imports and fn definitions but drops bare expressions and prints")
val code = "use std.io.{file_read}\n\nval x = 42\nprint(x)\n\nfn helper(n: i64) -> i64:\n    return n + 1\n"
val reusable = extract_reusable_lines(code)
expect(reusable).to_contain("use std.io.{file_read}")
expect(reusable).to_contain("fn helper(n: i64) -> i64:")
expect(reusable).to_contain("return n + 1")
expect(reusable.contains("print(x)")).to_equal(false)
expect(reusable.contains("val x = 42")).to_equal(false)
```

</details>

#### deliberate-red: fail-closed paths

#### returns zero blocks for markdown with no fences and no markers at all

- returns zero blocks for markdown with no fences and no markers at all
   - Expected: blocks.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns zero blocks for markdown with no fences and no markers at all")
val content = "# Heading\n\nJust prose, nothing to extract here.\n"
val blocks = extract_blocks_from_content(content: content, file_path: "doc/example.md")
expect(blocks.len()).to_equal(0)
```

</details>

#### returns zero blocks for an unclosed fence instead of crashing

- returns zero blocks for an unclosed fence instead of crashing
   - Expected: blocks.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns zero blocks for an unclosed fence instead of crashing")
val content = "```simple\nval x = 1\n"
val blocks = extract_blocks_from_content(content: content, file_path: "doc/example.md")
expect(blocks.len()).to_equal(0)
```

</details>

#### returns zero blocks (not a crash) when the source file does not exist on disk

- returns zero blocks (not a crash) when the source file does not exist on disk
   - Expected: blocks.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns zero blocks (not a crash) when the source file does not exist on disk")
val blocks = extract_sdoctest_blocks("/tmp/simple_extractor_missing_{time_now_unix_micros()}.md")
expect(blocks.len()).to_equal(0)
```

</details>

#### file-based extraction (disk round-trip)

#### extracts the same block set from a real file as from its in-memory content

- extracts the same block set from a real file as from its in-memory content
   - Expected: blocks.len() equals `1`
   - Expected: blocks[0].code equals `1 + 1`
   - Expected: blocks[0].get_run_config() equals `fast_env`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extracts the same block set from a real file as from its in-memory content")
val path = "/tmp/simple_extractor_roundtrip_{time_now_unix_micros()}.md"
val content = "<!--sdoctest:@fast_env-->\n```sdoctest\n>>> 1 + 1\n2\n```\n"
expect(file_write(path, content)).to_be(true)

val blocks = extract_sdoctest_blocks(path)
expect(blocks.len()).to_equal(1)
expect(blocks[0].code).to_equal("1 + 1")
expect(blocks[0].get_run_config()).to_equal("fast_env")

expect(file_delete(path)).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/test_runner/sdoctest_extractor_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering sdoctest extractor (hardening).
- sdoctest extractor (hardening)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `274f5bdf4bfc0aef0b3bee1a5a07eff4694c3249b79f173929786dfcb8c94c71`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `274f5bdf4bfc0aef0b3bee1a5a07eff4694c3249b79f173929786dfcb8c94c71`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `274f5bdf4bfc0aef0b3bee1a5a07eff4694c3249b79f173929786dfcb8c94c71`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/test_runner/sdoctest_extractor_spec.spl
mirror: doc/06_spec/01_unit/lib/test_runner/sdoctest_extractor_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/test_runner/sdoctest_extractor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/test_runner/sdoctest_extractor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/test_runner/sdoctest_extractor_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/test_runner/sdoctest_extractor_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts one block, strips >>> prompts, and drops the expected-output line for a sdoctest fence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/test_runner/sdoctest_extractor_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts a plain ```simple fence verbatim (no prompt-stripping outside sdoctest fences)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/test_runner/sdoctest_extractor_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'marks a block inside skip-begin/skip-end as skipped and leaves the next block untouched' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
