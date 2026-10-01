# Matcher Specification

> Tests covering DoctestMatcher.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Matcher Specification

## Scenarios

### DoctestMatcher

#### match_output

#### matches exact output

- matches exact output
   - Expected: result.is_pass() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches exact output")
val actual = "42"
val expected = Expected.Output("42")
val result = match_output(actual, expected)
expect(result.is_pass()).to_equal(true)
```

</details>

#### matches with trailing whitespace normalization

- matches with trailing whitespace normalization
   - Expected: result.is_pass() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches with trailing whitespace normalization")
val actual = "42  \n"
val expected = Expected.Output("42")
val result = match_output(actual, expected)
expect(result.is_pass()).to_equal(true)
```

</details>

#### fails on mismatch

- fails on mismatch
   - Expected: result.is_fail() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails on mismatch")
val actual = "42"
val expected = Expected.Output("43")
val result = match_output(actual, expected)
expect(result.is_fail()).to_equal(true)
expect(result.unwrap_failure()).to_contain("mismatch")
```

</details>

#### matches multi-line output

- matches multi-line output
   - Expected: result.is_pass() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches multi-line output")
val actual = "line1\nline2\nline3"
val expected = Expected.Output("line1\nline2\nline3")
val result = match_output(actual, expected)
expect(result.is_pass()).to_equal(true)
```

</details>

#### matches empty output

- matches empty output
   - Expected: result.is_pass() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches empty output")
val actual = ""
val expected = Expected.Empty
val result = match_output(actual, expected)
expect(result.is_pass()).to_equal(true)
```

</details>

#### fails when expecting empty but got output

- fails when expecting empty but got output
   - Expected: result.is_fail() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails when expecting empty but got output")
val actual = "unexpected"
val expected = Expected.Empty
val result = match_output(actual, expected)
expect(result.is_fail()).to_equal(true)
expect(result.unwrap_failure()).to_contain("Expected no output")
```

</details>

#### match_exception

#### matches exception type

- matches exception type
   - Expected: result.is_pass() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches exception type")
val result = match_exception("ValueError", "some message",
                        Expected.Exception("ValueError", nil))
expect(result.is_pass()).to_equal(true)
```

</details>

#### matches exception type and message

- matches exception type and message
   - Expected: result.is_pass() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches exception type and message")
val result = match_exception("ValueError", "invalid input",
                        Expected.Exception("ValueError", "invalid"))
expect(result.is_pass()).to_equal(true)
```

</details>

#### fails on wrong exception type

- fails on wrong exception type
   - Expected: result.is_fail() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails on wrong exception type")
val result = match_exception("TypeError", "msg",
                        Expected.Exception("ValueError", nil))
expect(result.is_fail()).to_equal(true)
expect(result.unwrap_failure()).to_contain("Expected ValueError")
```

</details>

#### fails on wrong message

- fails on wrong message
   - Expected: result.is_fail() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails on wrong message")
val result = match_exception("ValueError", "wrong message",
                        Expected.Exception("ValueError", "expected message"))
expect(result.is_fail()).to_equal(true)
expect(result.unwrap_failure()).to_contain("message mismatch")
```

</details>

#### fails when expected output but got exception

- fails when expected output but got exception
   - Expected: result.is_fail() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails when expected output but got exception")
val result = match_exception("ValueError", "msg", Expected.Output("42"))
expect(result.is_fail()).to_equal(true)
```

</details>

#### wildcard_match

#### matches with dot wildcard

- matches with dot wildcard
   - Expected: wildcard_match("abc", "a.c") is true
   - Expected: wildcard_match("a1c", "a.c") is true
   - Expected: wildcard_match("axc", "a.c") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches with dot wildcard")
expect(wildcard_match("abc", "a.c")).to_equal(true)
expect(wildcard_match("a1c", "a.c")).to_equal(true)
expect(wildcard_match("axc", "a.c")).to_equal(true)
```

</details>

#### matches with star wildcard

- matches with star wildcard
   - Expected: wildcard_match("hello world", "hello*") is true
   - Expected: wildcard_match("hello world", "*world") is true
   - Expected: wildcard_match("hello world", "hello*world") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches with star wildcard")
expect(wildcard_match("hello world", "hello*")).to_equal(true)
expect(wildcard_match("hello world", "*world")).to_equal(true)
expect(wildcard_match("hello world", "hello*world")).to_equal(true)
```

</details>

#### matches UUID pattern

- matches UUID pattern
   - Expected: wildcard_match(uuid, pattern) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches UUID pattern")
val uuid = "550e8400-e29b-41d4-a716-446655440000"
val pattern = "........-....-....-....-............"
expect(wildcard_match(uuid, pattern)).to_equal(true)
```

</details>

#### matches timestamp pattern

- matches timestamp pattern
   - Expected: wildcard_match(timestamp, pattern) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches timestamp pattern")
val timestamp = "1702345678"
val pattern = "1702*"
expect(wildcard_match(timestamp, pattern)).to_equal(true)
```

</details>

#### fails on non-matching pattern

- fails on non-matching pattern
   - Expected: wildcard_match("abc", "a.d") is false
   - Expected: wildcard_match("hello", "world") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails on non-matching pattern")
expect(wildcard_match("abc", "a.d")).to_equal(false)
expect(wildcard_match("hello", "world")).to_equal(false)
```

</details>

#### handles multiple wildcards

- handles multiple wildcards
   - Expected: wildcard_match("ab12cd34ef", "ab..cd..ef") is true
   - Expected: wildcard_match("prefix123suffix456", "prefix*suffix*") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple wildcards")
expect(wildcard_match("ab12cd34ef", "ab..cd..ef")).to_equal(true)
expect(wildcard_match("prefix123suffix456", "prefix*suffix*")).to_equal(true)
```

</details>

#### exact_match

#### matches identical strings

- matches identical strings
   - Expected: exact_match("hello", "hello") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("matches identical strings")
expect(exact_match("hello", "hello")).to_equal(true)
```

</details>

#### normalizes whitespace

- normalizes whitespace
   - Expected: exact_match("hello  ", "hello") is true
   - Expected: exact_match("hello\n", "hello") is true
   - Expected: exact_match(" hello ", " hello") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("normalizes whitespace")
expect(exact_match("hello  ", "hello")).to_equal(true)
expect(exact_match("hello\n", "hello")).to_equal(true)
expect(exact_match(" hello ", " hello")).to_equal(true)
```

</details>

#### fails on different strings

- fails on different strings
   - Expected: exact_match("hello", "world") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails on different strings")
expect(exact_match("hello", "world")).to_equal(false)
```

</details>

#### normalize

#### strips trailing whitespace

- strips trailing whitespace
   - Expected: normalize("hello  ") equals `hello`
   - Expected: normalize("hello\t\n") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips trailing whitespace")
expect(normalize("hello  ")).to_equal("hello")
expect(normalize("hello\t\n")).to_equal("hello")
```

</details>

#### strips trailing whitespace from each line

- strips trailing whitespace from each line
   - Expected: normalize("line1  \nline2  ") equals `line1\nline2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips trailing whitespace from each line")
expect(normalize("line1  \nline2  ")).to_equal("line1\nline2")
```

</details>

#### trims leading whitespace

- trims leading whitespace
   - Expected: normalize("  hello") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trims leading whitespace")
expect(normalize("  hello")).to_equal("hello")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/doctest/matcher_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DoctestMatcher.
- DoctestMatcher

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
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

- Canonical SPipe generation for source `c54f5f517de2287d49748cc9ea0d357a51d6903e046b8364e654b5bfcdefc9b0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c54f5f517de2287d49748cc9ea0d357a51d6903e046b8364e654b5bfcdefc9b0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c54f5f517de2287d49748cc9ea0d357a51d6903e046b8364e654b5bfcdefc9b0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/doctest/matcher_spec.spl
mirror: doc/06_spec/unit/doctest/matcher_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=80 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/doctest/matcher_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/doctest/matcher_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/doctest/matcher_spec.spl:1:1: advice SSDOC-COV-001 [coverage] (-20): the authored requirement defines adverse behavior but no adverse scenario is named
  why: Specifications should explain behavior outside the happy path.
  improve: Add adverse-path scenarios required by the source, or record a reasoned suppression.
test/unit/doctest/matcher_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches exact output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/doctest/matcher_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches with trailing whitespace normalization' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/doctest/matcher_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails on mismatch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
