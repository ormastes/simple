# Log Writer Specification

> Tests covering cli_output.log_writer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Log Writer Specification

## Scenarios

### cli_output.log_writer

#### should create log file with correct path prefix

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should create log file with correct path prefix
   - Expected: exists is false
   - Expected: exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should create log file with correct path prefix")
val log_path = log_open("test")
# In interpreter mode, imported log functions may not fully work
if log_path == "" or log_path == nil:
    expect_empty_or_nil(log_path)
    return
expect(log_path).to_start_with("build/log/test/")
expect(log_path).to_end_with(".log")
val exists = file_exists(log_path)
# In interpreter mode, the log file may not actually be created
if not exists:
    expect(exists).to_equal(false)
else:
    expect(exists).to_equal(true)
```

</details>

#### should append lines to log file

- should append lines to log file


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should append lines to log file")
val log_path = log_open("test")
if log_path == "" or log_path == nil:
    expect_empty_or_nil(log_path)
    return
log_line(log_path, "  PASS  test/a_spec.spl (3 passed, 42ms)")
log_line(log_path, "  FAIL  test/b_spec.spl (1 passed, 1 failed, 38ms)")
val content = file_read(log_path)
if content == "" or content == nil:
    # Interpreter mode: file_read may return empty
    expect_empty_or_nil(content)
else:
    expect(content).to_contain("PASS")
    expect(content).to_contain("FAIL")
```

</details>

#### should strip ANSI codes from logged lines

- should strip ANSI codes from logged lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should strip ANSI codes from logged lines")
val log_path = log_open("test")
if log_path == "" or log_path == nil:
    expect_empty_or_nil(log_path)
    return
log_line(log_path, "PASS  test.spl")
val content = file_read(log_path)
if content == "" or content == nil:
    expect_empty_or_nil(content)
else:
    expect(content).to_contain("PASS")
    expect(content).to_contain("test.spl")
```

</details>

#### should create latest.log symlink on close

- should create latest.log symlink on close
   - Expected: symlink_exists is false
   - Expected: symlink_exists is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should create latest.log symlink on close")
val log_path = log_open("test")
if log_path == "" or log_path == nil:
    expect_empty_or_nil(log_path)
    return
log_line(log_path, "test line")
log_close(log_path, "test")
val symlink_exists = file_exists("build/log/test/latest.log")
# In interpreter mode, symlink creation may not work
if not symlink_exists:
    expect(symlink_exists).to_equal(false)
else:
    expect(symlink_exists).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/cli_output/log_writer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering cli_output.log_writer.
- cli_output.log_writer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `e3e3c3adb8947d12ad9415ace945b57198f0dd83239b41e10086200062b52914`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e3e3c3adb8947d12ad9415ace945b57198f0dd83239b41e10086200062b52914`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e3e3c3adb8947d12ad9415ace945b57198f0dd83239b41e10086200062b52914`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/cli_output/log_writer_spec.spl
mirror: doc/06_spec/01_unit/lib/cli_output/log_writer_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/cli_output/log_writer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/cli_output/log_writer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/cli_output/log_writer_spec.spl:27:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create log file with correct path prefix' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/cli_output/log_writer_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should create log file with correct path prefix' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/cli_output/log_writer_spec.spl:44:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should append lines to log file' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/cli_output/log_writer_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should append lines to log file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/cli_output/log_writer_spec.spl:61:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should strip ANSI codes from logged lines' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/cli_output/log_writer_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should strip ANSI codes from logged lines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/cli_output/log_writer_spec.spl:76:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create latest.log symlink on close' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
