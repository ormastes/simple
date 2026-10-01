# visibility_spec

> Tests the core algorithm that converts filenames to expected type names.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# visibility_spec

Tests the core algorithm that converts filenames to expected type names.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/visibility_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Snake_case to PascalCase Conversion

    Tests the core algorithm that converts filenames to expected type names.

## Scenarios

### Filename to Type Name Conversion

#### converts simple snake_case to PascalCase

- converts simple snake_case to PascalCase


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts simple snake_case to PascalCase")
val result = filename_to_type_name("test_case")
expect result == "TestCase"
```

</details>

#### converts multi-word snake_case

- converts multi-word snake_case


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts multi-word snake_case")
val result = filename_to_type_name("string_interner")
expect result == "StringInterner"
```

</details>

#### handles .spl extension

- handles .spl extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles .spl extension")
val result = filename_to_type_name("test_case.spl")
expect result == "TestCase"
```

</details>

#### handles single word without underscores

- handles single word without underscores


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single word without underscores")
val result = filename_to_type_name("io")
expect result == "Io"
```

</details>

#### handles single word with extension

- handles single word with extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single word with extension")
val result = filename_to_type_name("io.spl")
expect result == "Io"
```

</details>

#### handles three-word names

- handles three-word names


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles three-word names")
val result = filename_to_type_name("http_client_pool")
expect result == "HttpClientPool"
```

</details>

#### preserves case for non-first letters

- preserves case for non-first letters


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves case for non-first letters")
# If original has mixed case (unusual), preserve it
val result = filename_to_type_name("http_api")
expect result == "HttpApi"
```

</details>

### Type Name Matching

#### matches exact conversion

- matches exact conversion


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches exact conversion")
val matches = type_matches_filename("TestCase", "test_case.spl")
expect matches
```

</details>

#### does not match different names

- does not match different names


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not match different names")
val matches = type_matches_filename("Helper", "test_case.spl")
expect not matches
```

</details>

#### matches without extension

- matches without extension


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches without extension")
val matches = type_matches_filename("StringInterner", "string_interner")
expect matches
```

</details>

#### matches single-word files

- matches single-word files


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches single-word files")
val matches = type_matches_filename("Io", "io.spl")
expect matches
```

</details>

#### handles case sensitivity correctly

- handles case sensitivity correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles case sensitivity correctly")
# TestCase vs testcase - should not match
val matches = type_matches_filename("testcase", "test_case.spl")
expect not matches
```

</details>

### Effective Visibility Calculation

#### explicit pub is always public

- explicit pub is always public


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("explicit pub is always public")
val is_public = effective_visibility("Helper", "test_case.spl", true)
expect is_public
```

</details>

#### filename match makes public

- filename match makes public


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filename match makes public")
val is_public = effective_visibility("TestCase", "test_case.spl", false)
expect is_public
```

</details>

#### non-matching name without pub is private

- non-matching name without pub is private


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-matching name without pub is private")
val is_public = effective_visibility("Helper", "test_case.spl", false)
expect not is_public
```

</details>

#### explicit pub overrides any filename

- explicit pub overrides any filename


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("explicit pub overrides any filename")
val is_public = effective_visibility("Anything", "other.spl", true)
expect is_public
```

</details>

#### filename match works for single-word files

- filename match works for single-word files


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filename match works for single-word files")
val is_public = effective_visibility("Io", "io.spl", false)
expect is_public
```

</details>

### Edge Cases

#### handles empty filename parts (double underscore)

- handles empty filename parts (double underscore)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty filename parts (double underscore)")
# test__case -> TestCase (empty part ignored)
val result = filename_to_type_name("test__case")
# Should handle gracefully - either "TestCase" or "Test_Case"
expect result.len() > 0
```

</details>

#### handles filename with no underscores

- handles filename with no underscores


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles filename with no underscores")
val result = filename_to_type_name("simple")
expect result == "Simple"
```

</details>

#### handles very long filenames

- handles very long filenames


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles very long filenames")
val result = filename_to_type_name("very_long_test_case_name_builder_factory")
expect result == "VeryLongTestCaseNameBuilderFactory"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
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

- Canonical SPipe generation for source `2ebc247343c6e8f7aaee47989b17471f44b682963e027fccf4769ea3ef6b8868`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2ebc247343c6e8f7aaee47989b17471f44b682963e027fccf4769ea3ef6b8868`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2ebc247343c6e8f7aaee47989b17471f44b682963e027fccf4769ea3ef6b8868`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/visibility_spec.spl
mirror: doc/06_spec/01_unit/compiler/visibility_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/visibility_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/visibility_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/visibility_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts simple snake_case to PascalCase' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/visibility_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts multi-word snake_case' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/visibility_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles .spl extension' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
