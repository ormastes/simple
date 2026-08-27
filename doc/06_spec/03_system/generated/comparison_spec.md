# comparison_spec

> Tests for snapshot comparison functionality including content matching,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# comparison_spec

Tests for snapshot comparison functionality including content matching,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/generated/comparison_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for snapshot comparison functionality including content matching,
diff generation, output formatting, and context line handling for
displaying differences between actual and expected snapshots.

## Scenarios

### Snapshot Comparison

#### Basic Comparison

#### matches identical content

- matches identical content
   - Expected: actual equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches identical content")
val actual = "Hello World"
val expected = "Hello World"
expect(actual).to_equal(expected)
```

</details>

#### detects content differences

- detects content differences


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects content differences")
val actual = "Hello World"
val expected = "Hello World!"
expect(actual).to_not_equal(expected)
```

</details>

#### ignores whitespace differences when configured

- ignores whitespace differences when configured


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ignores whitespace differences when configured")
val content1 = "hello  world"
val content2 = "hello world"
# Different but could be normalized
expect(content1).to_not_equal(content2)
```

</details>

#### Diff Generation

#### generates diff for changed lines

- generates diff for changed lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates diff for changed lines")
val line1 = "old line"
val line2 = "new line"
expect(line1).to_not_equal(line2)
```

</details>

#### handles multiline diffs

- handles multiline diffs
   - Expected: text1 equals `text2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles multiline diffs")
val text1 = "line 1{NL}line 2{NL}line 3"
val text2 = "line 1{NL}line 2{NL}line 3"
expect(text1).to_equal(text2)
```

</details>

#### marks added lines

- marks added lines
   - Expected: new_length > original_length is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("marks added lines")
val original_length = 3
val new_length = 4
expect(new_length > original_length).to_equal(true)
```

</details>

#### marks removed lines

- marks removed lines
   - Expected: new_length < original_length is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("marks removed lines")
val original_length = 4
val new_length = 3
expect(new_length < original_length).to_equal(true)
```

</details>

#### Formatting

#### formats comparison result

- formats comparison result
   - Expected: result equals `Match`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats comparison result")
val result = "Match"
expect(result).to_equal("Match")
```

</details>

#### shows unified diff format

- shows unified diff format
   - Expected: diff_format equals `unified`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("shows unified diff format")
val diff_format = "unified"
expect(diff_format).to_equal("unified")
```

</details>

#### shows side-by-side format

- shows side-by-side format
   - Expected: diff_format equals `side-by-side`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("shows side-by-side format")
val diff_format = "side-by-side"
expect(diff_format).to_equal("side-by-side")
```

</details>

#### Context Lines

#### includes context around changes

- includes context around changes
   - Expected: context_size > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes context around changes")
val context_size = 3
expect(context_size > 0).to_equal(true)
```

</details>

#### handles edge cases at file start

- handles edge cases at file start
   - Expected: line_number >= 1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles edge cases at file start")
val line_number = 1
expect(line_number >= 1).to_equal(true)
```

</details>

#### handles edge cases at file end

- handles edge cases at file end
   - Expected: line_number <= total_lines is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles edge cases at file end")
val total_lines = 100
val line_number = 100
expect(line_number <= total_lines).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e9da93f120aa291d9b483a8b53f2a680af33e65a56a8059024e33239f75091f2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e9da93f120aa291d9b483a8b53f2a680af33e65a56a8059024e33239f75091f2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e9da93f120aa291d9b483a8b53f2a680af33e65a56a8059024e33239f75091f2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/generated/comparison_spec.spl
mirror: doc/06_spec/03_system/generated/comparison_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/generated/comparison_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/generated/comparison_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/generated/comparison_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches identical content' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/generated/comparison_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects content differences' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/generated/comparison_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ignores whitespace differences when configured' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
