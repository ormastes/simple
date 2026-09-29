# Interp Split Ws Specification

> Tests covering split(newline) whitespace stripping bug.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interp Split Ws Specification

## Scenarios

### split(newline) whitespace stripping bug

#### demonstrates the bug with split

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- demonstrates the bug with split
   - Expected: _len(lines) equals `3`
   - Expected: _get(lines, 0) equals `line1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("demonstrates the bug with split")
val text_with_indent = "line1\n  indented\n    deeply"
val lines = text_with_indent.split("\n")
# BUG: split("\n") strips leading whitespace
# lines[1] becomes "indented" instead of "  indented"
# We can only verify the content is present, not the indent
expect(_len(lines)).to_equal(3)
expect(_get(lines, 0)).to_equal("line1")
# lines[1] should be "  indented" but bug strips it
val line1 = _get(lines, 1)
expect(line1).to_contain("indented")
```

</details>

#### workaround preserves indentation

- workaround preserves indentation
   - Expected: _len(lines) equals `3`
   - Expected: _get(lines, 0) equals `line1`
   - Expected: _get(lines, 1) equals `  indented`
   - Expected: _get(lines, 2) equals `    deeply`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("workaround preserves indentation")
val text_with_indent = "line1\n  indented\n    deeply"
val lines = _parse_lines_preserving_indent(text_with_indent)
expect(_len(lines)).to_equal(3)
expect(_get(lines, 0)).to_equal("line1")
expect(_get(lines, 1)).to_equal("  indented")
expect(_get(lines, 2)).to_equal("    deeply")
```

</details>

#### workaround handles trailing newline

- workaround handles trailing newline
   - Expected: _len(lines) equals `2`
   - Expected: _get(lines, 0) equals `a`
   - Expected: _get(lines, 1) equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("workaround handles trailing newline")
val content = "a\nb\n"
val lines = _parse_lines_preserving_indent(content)
expect(_len(lines)).to_equal(2)
expect(_get(lines, 0)).to_equal("a")
expect(_get(lines, 1)).to_equal("b")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Bug Regression |
| Status | Active |
| Source | `test/unit/bugs/interp_split_ws_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering split(newline) whitespace stripping bug.
- split(newline) whitespace stripping bug

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `a98d79c1f4ef527844739e843bf2fdeef9cce52f704193dd3782a34392ec46bd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a98d79c1f4ef527844739e843bf2fdeef9cce52f704193dd3782a34392ec46bd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a98d79c1f4ef527844739e843bf2fdeef9cce52f704193dd3782a34392ec46bd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/bugs/interp_split_ws_spec.spl
mirror: doc/06_spec/unit/bugs/interp_split_ws_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/bugs/interp_split_ws_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/bugs/interp_split_ws_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/bugs/interp_split_ws_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/bugs/interp_split_ws_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'demonstrates the bug with split' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/bugs/interp_split_ws_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'workaround preserves indentation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/bugs/interp_split_ws_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'workaround handles trailing newline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
