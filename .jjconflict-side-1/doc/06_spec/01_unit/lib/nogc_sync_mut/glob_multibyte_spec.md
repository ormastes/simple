# Glob Multibyte Specification

> Tests covering glob_match multi-byte paths.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Glob Multibyte Specification

## Scenarios

### glob_match multi-byte paths

#### '?' matches one café-style accented character (2-byte UTF-8), not one byte

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- '?' matches one café-style accented character (2-byte UTF-8), not one byte


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("'?' matches one café-style accented character (2-byte UTF-8), not one byte")
expect(glob_match("café.txt", "caf?.txt")).to_be(true)
# Old behavior: false (cursor landed on é's continuation byte after
# consuming only its lead byte, then never matched '.').
```

</details>

#### '?' matches one CJK character (3-byte UTF-8)

- '?' matches one CJK character (3-byte UTF-8)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("'?' matches one CJK character (3-byte UTF-8)")
expect(glob_match("日report.txt", "?report.txt")).to_be(true)
```

</details>

#### '?' matches one em-dash character (3-byte UTF-8) between ASCII characters

- '?' matches one em-dash character (3-byte UTF-8) between ASCII characters


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("'?' matches one em-dash character (3-byte UTF-8) between ASCII characters")
expect(glob_match("a—b", "a?b")).to_be(true)
```

</details>

#### '?' still correctly rejects a genuinely-wrong-length multi-byte path

- '?' still correctly rejects a genuinely-wrong-length multi-byte path


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("'?' still correctly rejects a genuinely-wrong-length multi-byte path")
# caf???txt is 9 positions vs café.txt's 8 characters — a real
# length mismatch. The previous example here, caf??txt, is 8
# positions and actually MATCHES (?? legitimately covers "é." —
# `?` matches `.` in glob; Python fnmatch agrees, and so does this
# repo's default engine). Its `false` expectation only held while
# the test-lane interpreter char-indexed bracket slices and
# wrongly failed every multi-byte match
# (doc/08_tracking/bug/test_harness_execution_divergence_2026-07-29.md).
expect(glob_match("café.txt", "caf???txt")).to_be(false)
expect(glob_match("café.txt", "caf?txt")).to_be(false)
```

</details>

#### '?' matches '.' like standard glob (was masked by the interpreter bug)

- '?' matches '.' like standard glob (was masked by the interpreter bug)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("'?' matches '.' like standard glob (was masked by the interpreter bug)")
expect(glob_match("café.txt", "caf??txt")).to_be(true)
```

</details>

#### '*' still matches across a multi-byte character (regression guard, not a bug fix -- byte-stepping already found the same answer here, just wastefully)

- '*' still matches across a multi-byte character (regression guard, not a bug fix -- byte-stepping already found the same answer here, just wastefully)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("'*' still matches across a multi-byte character (regression guard, not a bug fix -- byte-stepping already found the same answer here, just wastefully)")
expect(glob_match("café_report.txt", "caf*.txt")).to_be(true)
expect(glob_match("日本語.log", "*.log")).to_be(true)
```

</details>

#### negated character class '[!...]' correctly matches (and fully consumes) a multi-byte character

- negated character class '[!...]' correctly matches (and fully consumes) a multi-byte character


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negated character class '[!...]' correctly matches (and fully consumes) a multi-byte character")
# '!' + '/' means "anything except a path separator" -- a common
# single-path-segment glob idiom. A CJK filename segment must match.
expect(glob_match("日", "[!/]")).to_be(true)
expect(glob_match("é/x", "[!/]/x")).to_be(true)
# Old behavior: [!/] matched (correctly decided é/日 aren't '/'), but
# then only consumed 1 of é's/日's 2-3 bytes, leaving a stray
# continuation byte that could never match the literal '/' that
# follows -- both examples above returned false before the fix.
```

</details>

#### positive ASCII character class still correctly rejects a multi-byte character

- positive ASCII character class still correctly rejects a multi-byte character


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("positive ASCII character class still correctly rejects a multi-byte character")
expect(glob_match("é", "[a-z]")).to_be(false)
```

</details>

#### literal multi-byte character match still works (regression guard, was already correct)

- literal multi-byte character match still works (regression guard, was already correct)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("literal multi-byte character match still works (regression guard, was already correct)")
expect(glob_match("café.txt", "café.txt")).to_be(true)
expect(glob_match("café.txt", "cafe.txt")).to_be(false)
```

</details>

#### pure ASCII patterns are unaffected (regression guard)

- pure ASCII patterns are unaffected (regression guard)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pure ASCII patterns are unaffected (regression guard)")
expect(glob_match("hello.txt", "*.txt")).to_be(true)
expect(glob_match("hello.txt", "h?llo.txt")).to_be(true)
expect(glob_match("hello.txt", "[hj]ello.txt")).to_be(true)
expect(glob_match("world.txt", "[hj]ello.txt")).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/glob_multibyte_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering glob_match multi-byte paths.
- glob_match multi-byte paths

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `10e13e29b93df4b33328180c8ec406bade44266f09d5b9db5e067041e1671dc5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `10e13e29b93df4b33328180c8ec406bade44266f09d5b9db5e067041e1671dc5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `10e13e29b93df4b33328180c8ec406bade44266f09d5b9db5e067041e1671dc5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_sync_mut/glob_multibyte_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/glob_multibyte_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/glob_multibyte_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/glob_multibyte_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/glob_multibyte_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario ''?' matches one café-style accented character (2-byte UTF-8), not one byte' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/glob_multibyte_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario ''?' matches one CJK character (3-byte UTF-8)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/glob_multibyte_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario ''?' matches one em-dash character (3-byte UTF-8) between ASCII characters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
