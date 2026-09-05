# Reporter Specification

> Tests covering format_bytes, report_console, escape_sdn.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Reporter Specification

## Scenarios

### format_bytes

#### formats small byte counts

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- formats small byte counts


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats small byte counts")
fn run():
    val r0 = format_bytes(0)
    expect(r0).to_contain("0")
    val r512 = format_bytes(512)
    expect(r512).to_contain("512")
run()
```

</details>

#### formats KB range

- formats KB range


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats KB range")
fn run():
    val r1k = format_bytes(1024)
    expect(r1k).to_contain("KB")
    val r2k = format_bytes(2048)
    expect(r2k).to_contain("KB")
run()
```

</details>

#### formats MB range

- formats MB range


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("formats MB range")
fn run():
    val r1m = format_bytes(1048576)
    expect(r1m).to_contain("MB")
    val r2m = format_bytes(2097152)
    expect(r2m).to_contain("MB")
run()
```

</details>

### report_console

#### shows no leaks verdict for clean result

- shows no leaks verdict for clean result


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows no leaks verdict for clean result")
fn run():
    val result = empty_leak_check_result()
    val output = report_console(result)
    expect(output).to_contain("No leaks detected")
    expect(output).to_contain("VERDICT")
run()
```

</details>

#### shows mode in report

- shows mode in report


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows mode in report")
fn run():
    val result = empty_leak_check_result()
    val output = report_console(result)
    expect(output).to_contain("Mode: internal")
run()
```

</details>

### escape_sdn

#### escapes backslashes

- escapes backslashes
   - Expected: result equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes backslashes")
fn run():
    val result = escape_sdn("hello world")
    expect(result).to_equal("hello world")
run()
```

</details>

#### leaves clean strings unchanged

- leaves clean strings unchanged
   - Expected: result equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves clean strings unchanged")
fn run():
    val result = escape_sdn("hello world")
    expect(result).to_equal("hello world")
run()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/leak_check/reporter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering format_bytes, report_console, escape_sdn.
- format_bytes
- report_console
- escape_sdn

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `7d1baa16f513c925933cadd3d2e6f1723fb50525e23615a03580738448e4715e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7d1baa16f513c925933cadd3d2e6f1723fb50525e23615a03580738448e4715e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7d1baa16f513c925933cadd3d2e6f1723fb50525e23615a03580738448e4715e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/leak_check/reporter_spec.spl
mirror: doc/06_spec/unit/app/leak_check/reporter_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/leak_check/reporter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/leak_check/reporter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/leak_check/reporter_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats small byte counts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/leak_check/reporter_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats KB range' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/leak_check/reporter_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'formats MB range' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
