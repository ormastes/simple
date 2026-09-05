# Inline Helpers Example

> Tests inline helper functions demonstrating Phase 2 workaround patterns. Verifies that helper utilities correctly delegate to underlying implementations and that the workaround patterns produce expected results in the standard library.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Inline Helpers Example

Tests inline helper functions demonstrating Phase 2 workaround patterns. Verifies that helper utilities correctly delegate to underlying implementations and that the workaround patterns produce expected results in the standard library.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | In Progress |
| Source | `test/feature/lib/std/helpers_example_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests inline helper functions demonstrating Phase 2 workaround patterns. Verifies
that helper utilities correctly delegate to underlying implementations and that
the workaround patterns produce expected results in the standard library.

## Scenarios

### Inline Helpers - Phase 2 Workaround

#### String operations

#### trims whitespace from both ends

- trims whitespace from both ends
- trims whitespace from both ends
   - Expected: trimmed equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("trims whitespace from both ends")
step("trims whitespace from both ends")
# @req: REQ-FEAT-STD-HELPERS-EXAMPLE-SPEC-001
val input = "  hello world  "
val trimmed = string_trim_inline(input)
expect(trimmed).to_equal("hello world")
```

</details>

#### trims tabs and newlines

- trims tabs and newlines
- trims tabs and newlines
   - Expected: trimmed equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("trims tabs and newlines")
step("trims tabs and newlines")
val input = "\t\nhello\n\t"
val trimmed = string_trim_inline(input)
expect(trimmed).to_equal("hello")
```

</details>

#### handles empty string

- handles empty string
- handles empty string
   - Expected: empty equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles empty string")
step("handles empty string")
val empty = string_trim_inline("")
expect(empty).to_equal("")
```

</details>

#### splits string by delimiter

- splits string by delimiter
- splits string by delimiter
   - Expected: parts[0] equals `apple`
   - Expected: parts.len() equals `3`
   - Expected: parts[1] equals `banana`
   - Expected: parts[2] equals `cherry`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("splits string by delimiter")
step("splits string by delimiter")
val csv = "apple,banana,cherry"
var parts = string_split_inline(csv, ",")
expect(parts[0]).to_equal("apple")
expect(parts.len()).to_equal(3)
expect(parts[1]).to_equal("banana")
expect(parts[2]).to_equal("cherry")
```

</details>

#### splits with multi-character delimiter

- splits with multi-character delimiter
- splits with multi-character delimiter
   - Expected: parts[0] equals `foo`
   - Expected: parts.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("splits with multi-character delimiter")
step("splits with multi-character delimiter")
val text = "foo::bar::baz"
var parts = string_split_inline(text, "::")
expect(parts[0]).to_equal("foo")
expect(parts.len()).to_equal(3)
```

</details>

#### handles no delimiters found

- handles no delimiters found
- handles no delimiters found
   - Expected: parts[0] equals `no-delimiters-here`
   - Expected: parts.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles no delimiters found")
step("handles no delimiters found")
val text = "no-delimiters-here"
var parts = string_split_inline(text, ",")
expect(parts[0]).to_equal("no-delimiters-here")
expect(parts.len()).to_equal(1)
```

</details>

#### Array operations

#### appends two arrays

- appends two arrays
- appends two arrays
   - Expected: combined[0] equals `1`
   - Expected: combined.len() equals `6`
   - Expected: combined[5] equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("appends two arrays")
step("appends two arrays")
val arr1 = [1, 2, 3]
val arr2 = [4, 5, 6]
val combined = array_append_all_inline(arr1, arr2)
expect(combined[0]).to_equal(1)
expect(combined.len()).to_equal(6)
expect(combined[5]).to_equal(6)
```

</details>

#### partitions by predicate

- partitions by predicate
- partitions by predicate
   - Expected: evens.len() equals `3`
   - Expected: evens[0] equals `2`
   - Expected: odds.len() equals `3`
   - Expected: odds[0] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("partitions by predicate")
step("partitions by predicate")
val numbers = [1, 2, 3, 4, 5, 6]
val is_even = fn(x): x % 2 == 0
var result = array_partition_inline(numbers, is_even)
val evens = result.0
val odds = result.1
expect(evens.len()).to_equal(3)
expect(evens[0]).to_equal(2)
expect(odds.len()).to_equal(3)
expect(odds[0]).to_equal(1)
```

</details>

#### flattens nested arrays

- flattens nested arrays
- flattens nested arrays
   - Expected: flat_result[0] equals `1`
   - Expected: flat_result.len() equals `6`
   - Expected: flat_result[5] equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("flattens nested arrays")
step("flattens nested arrays")
val nested = [[1, 2], [3, 4], [5, 6]]
val flat_result = array_flatten_inline(nested)
expect(flat_result[0]).to_equal(1)
expect(flat_result.len()).to_equal(6)
expect(flat_result[5]).to_equal(6)
```

</details>

#### flattens arrays with different lengths

- flattens arrays with different lengths
- flattens arrays with different lengths
   - Expected: flat_result.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("flattens arrays with different lengths")
step("flattens arrays with different lengths")
val nested = [[1], [2, 3, 4], [5, 6]]
val flat_result = array_flatten_inline(nested)
expect(flat_result.len()).to_equal(6)
```

</details>

#### Real-world usage

#### processes CSV data

- processes CSV data
- processes CSV data
   - Expected: fields[0] equals `Alice`
   - Expected: fields.len() equals `3`
   - Expected: fields[1] equals `30`
   - Expected: fields[2] equals `Engineer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("processes CSV data")
step("processes CSV data")
# Simulate reading CSV lines
val csv_line = "Alice,30,Engineer"
val fields = string_split_inline(csv_line, ",")

expect(fields[0]).to_equal("Alice")
expect(fields.len()).to_equal(3)
expect(fields[1]).to_equal("30")
expect(fields[2]).to_equal("Engineer")
```

</details>

#### combines data from multiple sources

- combines data from multiple sources
- combines data from multiple sources
   - Expected: all_data.len() equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("combines data from multiple sources")
step("combines data from multiple sources")
val source1 = [1, 2, 3]
val source2 = [4, 5]
val source3 = [6, 7, 8, 9]

# Combine all sources
var all_data = array_append_all_inline(source1, source2)
all_data = array_append_all_inline(all_data, source3)

expect(all_data.len()).to_equal(9)
```

</details>

#### filters and processes text lines

- filters and processes text lines
- filters and processes text lines
   - Expected: trimmed_lines[0] equals `line 1`
   - Expected: trimmed_lines[1] equals `line 2`
   - Expected: trimmed_lines[2] equals `line 3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("filters and processes text lines")
step("filters and processes text lines")
# Simulate file lines with whitespace
val lines = ["  line 1  ", "  line 2  ", "  line 3  "]
var trimmed_lines = []
for line in lines:
    trimmed_lines.push(string_trim_inline(line))

expect(trimmed_lines[0]).to_equal("line 1")
expect(trimmed_lines[1]).to_equal("line 2")
expect(trimmed_lines[2]).to_equal("line 3")
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

- `REQ-SSPEC-FEATURE`
- `REQ-FEAT-STD-HELPERS-EXAMPLE-SPEC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `65a8424690fa8d225a32cf6ff538e4a0bf874a359d9793219825affabd20cce2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `65a8424690fa8d225a32cf6ff538e4a0bf874a359d9793219825affabd20cce2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `65a8424690fa8d225a32cf6ff538e4a0bf874a359d9793219825affabd20cce2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/lib/std/helpers_example_spec.spl
mirror: doc/06_spec/feature/lib/std/helpers_example_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/lib/std/helpers_example_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/lib/std/helpers_example_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/lib/std/helpers_example_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 16 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/lib/std/helpers_example_spec.spl:144:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'trims whitespace from both ends' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/lib/std/helpers_example_spec.spl:153:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'trims tabs and newlines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/lib/std/helpers_example_spec.spl:161:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles empty string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
