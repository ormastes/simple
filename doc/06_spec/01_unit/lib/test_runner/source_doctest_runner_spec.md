# Source Doctest Runner Specification

> Tests covering source doctest extraction.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Source Doctest Runner Specification

## Scenarios

### source doctest extraction

#### extracts ordinary comments and fenced docstrings but ignores malformed blocks

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- extracts ordinary comments and fenced docstrings but ignores malformed blocks
   - Expected: blocks.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extracts ordinary comments and fenced docstrings but ignores malformed blocks")
val path = "/tmp/simple_source_doctest_{time_now_unix_micros()}.spl"
val source = "# ```simple\n# val from_comment = 1\n# ```\n# ```simple\n# unclosed\n\nfn documented():\n    \"\"\"Example.\n    ```spl\n    val from_docstring = 2\n    ```\n    ```simple\n    ```\n    \"\"\"\n    nil\n"
expect(file_write(path, source)).to_be(true)

val blocks = extract_doctests(path)
expect(blocks.len()).to_equal(2)
expect(blocks[0].code).to_contain("from_comment")
expect(blocks[1].code).to_contain("from_docstring")

expect(file_delete(path)).to_be(true)
```

</details>

#### removes the generated source-doctest fixture after execution

- removes the generated source-doctest fixture after execution
   - Expected: blocks.len() equals `1`
   - Expected: result.passed + result.failed equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("removes the generated source-doctest fixture after execution")
val path = "/tmp/simple_source_doctest_cleanup_{time_now_unix_micros()}.spl"
val source = "# ```simple\n# val cleanup_probe = 1\n# ```\n"
expect(file_write(path, source)).to_be(true)

val blocks = extract_doctests(path)
expect(blocks.len()).to_equal(1)
val tmpdir = env_get("TMPDIR")
val temp_root = if tmpdir != "": tmpdir else: "/tmp"
val generated_path = "{temp_root}/simple_doctest_{blocks[0].line_number}.spl"
if file_exists(generated_path):
    file_delete(generated_path)

val result = run_doctests(path, 5000)
expect(result.passed + result.failed).to_equal(1)
expect(file_exists(generated_path)).to_be(false)
expect(file_delete(path)).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/test_runner/source_doctest_runner_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering source doctest extraction.
- source doctest extraction

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `eca184c99c52778f9746e177b83abdd235b0b4439788138a1bbfcbb861cd1e50`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eca184c99c52778f9746e177b83abdd235b0b4439788138a1bbfcbb861cd1e50`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eca184c99c52778f9746e177b83abdd235b0b4439788138a1bbfcbb861cd1e50`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/test_runner/source_doctest_runner_spec.spl
mirror: doc/06_spec/01_unit/lib/test_runner/source_doctest_runner_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/test_runner/source_doctest_runner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/test_runner/source_doctest_runner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/test_runner/source_doctest_runner_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/test_runner/source_doctest_runner_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts ordinary comments and fenced docstrings but ignores malformed blocks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/test_runner/source_doctest_runner_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'removes the generated source-doctest fixture after execution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
