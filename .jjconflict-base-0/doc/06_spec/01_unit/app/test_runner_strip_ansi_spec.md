# Test Runner Strip Ansi Specification

> Tests covering strip_ansi.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Runner Strip Ansi Specification

## Scenarios

### strip_ansi

#### leaves plain text with no escape sequences unchanged

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- leaves plain text with no escape sequences unchanged
   - Expected: strip_ansi("plain test output, nothing fancy") equals `plain test output, nothing fancy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves plain text with no escape sequences unchanged")
expect(strip_ansi("plain test output, nothing fancy")).to_equal("plain test output, nothing fancy")
```

</details>

#### strips a simple SGR color sequence

- strips a simple SGR color sequence
   - Expected: strip_ansi("\x1b[32mPASS\x1b[0m") equals `PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips a simple SGR color sequence")
expect(strip_ansi("\x1b[32mPASS\x1b[0m")).to_equal("PASS")
```

</details>

#### strips multiple sequences within one line

- strips multiple sequences within one line
   - Expected: strip_ansi("\x1b[32mPASS\x1b[0m test/sample_spec.spl \x1b[2m(2 passed)\x1b[0m") equals `PASS test/sample_spec.spl (2 passed)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips multiple sequences within one line")
expect(strip_ansi("\x1b[32mPASS\x1b[0m test/sample_spec.spl \x1b[2m(2 passed)\x1b[0m")).to_equal("PASS test/sample_spec.spl (2 passed)")
```

</details>

#### strips a cursor/attribute sequence using the '?' parameter byte

- strips a cursor/attribute sequence using the '?' parameter byte
   - Expected: strip_ansi("before\x1b[?25lafter") equals `beforeafter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips a cursor/attribute sequence using the '?' parameter byte")
expect(strip_ansi("before\x1b[?25lafter")).to_equal("beforeafter")
```

</details>

#### strips a sequence with multiple numeric parameters

- strips a sequence with multiple numeric parameters
   - Expected: strip_ansi("\x1b[1;32;40mBOLD GREEN ON BLACK\x1b[0m") equals `BOLD GREEN ON BLACK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips a sequence with multiple numeric parameters")
expect(strip_ansi("\x1b[1;32;40mBOLD GREEN ON BLACK\x1b[0m")).to_equal("BOLD GREEN ON BLACK")
```

</details>

#### passes through an OSC-style sequence unchanged (only CSI 'ESC[' is recognized)

- passes through an OSC-style sequence unchanged (only CSI 'ESC[' is recognized)
   - Expected: strip_ansi(osc) equals `osc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes through an OSC-style sequence unchanged (only CSI 'ESC[' is recognized)")
# strip_ansi only recognizes CSI sequences (ESC '[' ... letter). An
# OSC sequence (ESC ']' ...) does not match `next == "["`, so the
# ESC byte and the sequence body fall through as ordinary
# characters. Documenting this as current, intentional-scope
# behavior -- not a bug fixed here.
val osc = "before\x1b]0;title\x07after"
expect(strip_ansi(osc)).to_equal(osc)
```

</details>

#### does not hang or drop trailing content on a truncated escape at end of string

- does not hang or drop trailing content on a truncated escape at end of string
   - Expected: strip_ansi("abc\x1b[3") equals `abc\x1b[3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not hang or drop trailing content on a truncated escape at end of string")
# "\x1b[3" has no terminator letter before the string ends -- the
# lookahead scan exhausts s.len() without setting looks_like_ansi,
# so the ESC and everything after it must fall through unchanged
# rather than being dropped or causing an infinite loop.
expect(strip_ansi("abc\x1b[3")).to_equal("abc\x1b[3")
```

</details>

#### does not hang or drop trailing content on a bare trailing ESC byte

- does not hang or drop trailing content on a bare trailing ESC byte
   - Expected: strip_ansi("abc\x1b") equals `abc\x1b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not hang or drop trailing content on a bare trailing ESC byte")
expect(strip_ansi("abc\x1b")).to_equal("abc\x1b")
```

</details>

#### returns an empty string for an empty string

- returns an empty string for an empty string
   - Expected: strip_ansi("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns an empty string for an empty string")
expect(strip_ansi("")).to_equal("")
```

</details>

#### returns an empty string when the input is only escape sequences

- returns an empty string when the input is only escape sequences
   - Expected: strip_ansi("\x1b[32m\x1b[1m\x1b[0m") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns an empty string when the input is only escape sequences")
expect(strip_ansi("\x1b[32m\x1b[1m\x1b[0m")).to_equal("")
```

</details>

#### passes non-ASCII (multi-byte UTF-8) text through intact

- passes non-ASCII (multi-byte UTF-8) text through intact
   - Expected: strip_ansi("\x1b[32m✓ café 日本語\x1b[0m") equals `✓ café 日本語`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes non-ASCII (multi-byte UTF-8) text through intact")
expect(strip_ansi("\x1b[32m✓ café 日本語\x1b[0m")).to_equal("✓ café 日本語")
```

</details>

#### handles an escape sequence immediately followed by more plain text with no separator

- handles an escape sequence immediately followed by more plain text with no separator
   - Expected: strip_ansi("\x1b[31mFAIL\x1b[0m: assertion mismatch") equals `FAIL: assertion mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles an escape sequence immediately followed by more plain text with no separator")
expect(strip_ansi("\x1b[31mFAIL\x1b[0m: assertion mismatch")).to_equal("FAIL: assertion mismatch")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner_strip_ansi_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering strip_ansi.
- strip_ansi

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `f3fcb60e84c3f02d814e1e566f85f61f0380fac5490a7a5b6422abb296b01b20`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f3fcb60e84c3f02d814e1e566f85f61f0380fac5490a7a5b6422abb296b01b20`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f3fcb60e84c3f02d814e1e566f85f61f0380fac5490a7a5b6422abb296b01b20`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/test_runner_strip_ansi_spec.spl
mirror: doc/06_spec/01_unit/app/test_runner_strip_ansi_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/test_runner_strip_ansi_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/test_runner_strip_ansi_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/test_runner_strip_ansi_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves plain text with no escape sequences unchanged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/test_runner_strip_ansi_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'strips a simple SGR color sequence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/test_runner_strip_ansi_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'strips multiple sequences within one line' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
