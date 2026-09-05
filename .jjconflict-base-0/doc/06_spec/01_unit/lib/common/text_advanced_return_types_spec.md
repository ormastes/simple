# Text Advanced Return Types Specification

> Tests covering text_advanced value-returning functions are typed.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text Advanced Return Types Specification

## Scenarios

### text_advanced value-returning functions are typed

#### detect_indent returns the leading-space count

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detect_indent returns the leading-space count
   - Expected: detect_indent(["hello", "  world", "    foo"]) equals `2`
   - Expected: detect_indent(["hello", "world"]) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("detect_indent returns the leading-space count")
expect(detect_indent(["hello", "  world", "    foo"])).to_equal(2)
expect(detect_indent(["hello", "world"])).to_equal(0)
```

</details>

#### dedent_lines strips the common indent

- dedent_lines strips the common indent
   - Expected: out[0] equals `hello`
   - Expected: out[1] equals `  world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("dedent_lines strips the common indent")
val out = dedent_lines(["  hello", "    world"])
expect(out[0]).to_equal("hello")
expect(out[1]).to_equal("  world")
```

</details>

#### normalize_indent rescales the indent

- normalize_indent rescales the indent
   - Expected: out[0] equals `    hello`
   - Expected: out[1] equals `        world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("normalize_indent rescales the indent")
val out = normalize_indent(["  hello", "    world"], 4)
expect(out[0]).to_equal("    hello")
expect(out[1]).to_equal("        world")
```

</details>

#### hamming_distance counts differing positions and is optional

- hamming_distance counts differing positions and is optional
   - Expected: hamming_distance("karolin", "kathrin") equals `3`
   - Expected: hamming_distance("abc", "abcd") equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("hamming_distance counts differing positions and is optional")
expect(hamming_distance("karolin", "kathrin")).to_equal(3)
expect(hamming_distance("abc", "abcd")).to_equal(nil)
```

</details>

#### longest_word returns the longest word and its length

- longest_word returns the longest word and its length
   - Expected: got[0] equals `quick`
   - Expected: got[1] equals `5`
   - Expected: longest_word("") equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("longest_word returns the longest word and its length")
val got = longest_word("The quick brown fox") ?? ("", 0)
expect(got[0]).to_equal("quick")
expect(got[1]).to_equal(5)
expect(longest_word("")).to_equal(nil)
```

</details>

#### most_common_char returns the modal character and its count

- most_common_char returns the modal character and its count
   - Expected: got[0] equals `l`
   - Expected: got[1] equals `2`
   - Expected: most_common_char("") equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("most_common_char returns the modal character and its count")
val got = most_common_char("hello") ?? ("", 0)
expect(got[0]).to_equal("l")
expect(got[1]).to_equal(2)
expect(most_common_char("")).to_equal(nil)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/text_advanced_return_types_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering text_advanced value-returning functions are typed.
- text_advanced value-returning functions are typed

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `32cd6a24b72ad583d793c6307eaac61dea6947cadb16b853e30d42a63d47c488`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `32cd6a24b72ad583d793c6307eaac61dea6947cadb16b853e30d42a63d47c488`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `32cd6a24b72ad583d793c6307eaac61dea6947cadb16b853e30d42a63d47c488`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/text_advanced_return_types_spec.spl
mirror: doc/06_spec/01_unit/lib/common/text_advanced_return_types_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/text_advanced_return_types_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/text_advanced_return_types_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/text_advanced_return_types_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/text_advanced_return_types_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detect_indent returns the leading-space count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/text_advanced_return_types_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dedent_lines strips the common indent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/text_advanced_return_types_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normalize_indent rescales the indent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
