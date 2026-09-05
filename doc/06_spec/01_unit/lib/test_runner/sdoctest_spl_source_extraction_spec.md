# Sdoctest Spl Source Extraction Specification

> Tests covering sdoctest .spl source extraction.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sdoctest Spl Source Extraction Specification

## Scenarios

### sdoctest .spl source extraction

#### extracts a docstring sdoctest: block

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- extracts a docstring sdoctest: block


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts a docstring sdoctest: block")
val src = "fn f() -> bool:\n    \"\"\"Doc.\n\n    sdoctest:\n        expect(f()).to_equal(true)\n        expect(1).to_equal(1)\n    \"\"\"\n    true\n"
val blocks = extract_spl_blocks_from_content(content: src, file_path: "x.spl")
assert_equal(blocks.len(), 1)
assert_equal(blocks[0].code, "expect(f()).to_equal(true)\nexpect(1).to_equal(1)")
assert_equal(blocks[0].language, "simple")
```

</details>

#### extracts a comment-prefixed simple fence

- extracts a comment-prefixed simple fence


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts a comment-prefixed simple fence")
val src = "# ```simple\n# val x = 1\n# print x\n# ```\n"
val blocks = extract_spl_blocks_from_content(content: src, file_path: "x.spl")
assert_equal(blocks.len(), 1)
assert_equal(blocks[0].code, "val x = 1\nprint x")
assert_equal(blocks[0].language, "simple")
```

</details>

#### preserves nested comment markers inside a fence body

- preserves nested comment markers inside a fence body


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves nested comment markers inside a fence body")
val src = "# ```simple\n# val o = g()\n# # Expect: true\n# ```\n"
val blocks = extract_spl_blocks_from_content(content: src, file_path: "x.spl")
assert_equal(blocks.len(), 1)
assert_equal(blocks[0].code, "val o = g()\n# Expect: true")
```

</details>

#### does NOT match a struct field named sdoctest:

- does NOT match a struct field named sdoctest:


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does NOT match a struct field named sdoctest:")
val src = "struct Args:\n    sdoctest: bool\n    sdoctest_env: text\n"
val blocks = extract_spl_blocks_from_content(content: src, file_path: "x.spl")
assert_equal(blocks.len(), 0)
```

</details>

#### does NOT match a >>> ASCII banner in a comment

- does NOT match a >>> ASCII banner in a comment


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does NOT match a >>> ASCII banner in a comment")
val src = "# >>> RENDER LANE <<<\n# >>> phase 2 <<<\n"
val blocks = extract_spl_blocks_from_content(content: src, file_path: "x.spl")
assert_equal(blocks.len(), 0)
```

</details>

#### does NOT match an unclosed comment fence

- does NOT match an unclosed comment fence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does NOT match an unclosed comment fence")
val src = "# ```simple\n# val x = 1\n"
val blocks = extract_spl_blocks_from_content(content: src, file_path: "x.spl")
assert_equal(blocks.len(), 0)
```

</details>

#### does NOT emit an empty docstring sdoctest: block

- does NOT emit an empty docstring sdoctest: block


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does NOT emit an empty docstring sdoctest: block")
val src = "fn f():\n    \"\"\"Doc.\n\n    sdoctest:\n    \"\"\"\n    0\n"
val blocks = extract_spl_blocks_from_content(content: src, file_path: "x.spl")
assert_equal(blocks.len(), 0)
```

</details>

#### keeps markdown extraction unchanged

- keeps markdown extraction unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps markdown extraction unchanged")
val md = "text\n\n```simple\nval a = 1\n```\n\nmore\n\n```simple:skip\nval b = 2\n```\n"
val blocks = extract_blocks_from_content(content: md, file_path: "x.md")
assert_equal(blocks.len(), 2)
assert_equal(blocks[0].code, "val a = 1")
assert_equal(blocks[1].code, "val b = 2")
```

</details>

#### gates .spl discovery behind the opt-in flag

- gates .spl discovery behind the opt-in flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gates .spl discovery behind the opt-in flag")
assert_true(sdoctest_file_eligible("a/b.md", false))
assert_false(sdoctest_file_eligible("a/b.spl", false))
assert_true(sdoctest_file_eligible("a/b.spl", true))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/test_runner/sdoctest_spl_source_extraction_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering sdoctest .spl source extraction.
- sdoctest .spl source extraction

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `bef91be470625a42e6a184b00587b1f8194ec640b440986602fbf439b0cbbe76`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bef91be470625a42e6a184b00587b1f8194ec640b440986602fbf439b0cbbe76`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bef91be470625a42e6a184b00587b1f8194ec640b440986602fbf439b0cbbe76`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/test_runner/sdoctest_spl_source_extraction_spec.spl
mirror: doc/06_spec/01_unit/lib/test_runner/sdoctest_spl_source_extraction_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/test_runner/sdoctest_spl_source_extraction_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/test_runner/sdoctest_spl_source_extraction_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/test_runner/sdoctest_spl_source_extraction_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts a docstring sdoctest: block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/test_runner/sdoctest_spl_source_extraction_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts a comment-prefixed simple fence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/test_runner/sdoctest_spl_source_extraction_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves nested comment markers inside a fence body' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
