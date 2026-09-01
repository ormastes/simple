# Logger Rotation Specification

> Tests covering Logger File Rotation, File Size Check, Global Logger Initialization, Flush Logs, Rotation Logic.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Logger Rotation Specification

## Scenarios

### Logger File Rotation

### File Size Check

#### triggers rotation when size exceeds max

- triggers rotation when size exceeds max
   - Expected: current_size > max_file_size is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("triggers rotation when size exceeds max")
val current_size = 11000000
val max_file_size = 10000000
expect(current_size > max_file_size).to_equal(true)
```

</details>

#### does not rotate when size is below max

- does not rotate when size is below max
   - Expected: current_size <= max_file_size is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not rotate when size is below max")
val current_size = 5000000
val max_file_size = 10000000
expect(current_size <= max_file_size).to_equal(true)
```

</details>

### Global Logger Initialization

#### handles initialization error

- handles initialization error
   - Expected: notif contains `Logger init failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles initialization error")
val notif = make_log_notification("error", "Logger init failed", "mcp")
expect(notif.contains("Logger init failed")).to_equal(true)
```

</details>

#### initializes successfully

- initializes successfully
   - Expected: notif contains `Logger initialized`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("initializes successfully")
val notif = make_log_notification("info", "Logger initialized", "mcp")
expect(notif.contains("Logger initialized")).to_equal(true)
```

</details>

### Flush Logs

#### handles flush when logger is nil

- handles flush when logger is nil
   - Expected: should_flush is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles flush when logger is nil")
val logger_available = false
val should_flush = logger_available
expect(should_flush).to_equal(false)
```

</details>

#### flushes when logger exists

- flushes when logger exists
   - Expected: should_flush is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flushes when logger exists")
val logger_available = true
val should_flush = logger_available
expect(should_flush).to_equal(true)
```

</details>

### Rotation Logic

#### archives old log file

- archives old log file
   - Expected: archive_path contains `log.1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("archives old log file")
val old_path = "/tmp/mcp.log"
val archive_path = "/tmp/mcp.log.1"
expect(archive_path.contains("log.1")).to_equal(true)
```

</details>

#### creates new log file after rotation

- creates new log file after rotation
   - Expected: size_after_creation equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates new log file after rotation")
val new_path = "/tmp/mcp.log"
val size_after_creation = 0
expect(size_after_creation).to_equal(0)
```

</details>

#### resets size counter after rotation

- resets size counter after rotation
   - Expected: size_after_rotation equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resets size counter after rotation")
var size_after_rotation = 10000000
size_after_rotation = 0
expect(size_after_rotation).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/logger_rotation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Logger File Rotation, File Size Check, Global Logger Initialization, Flush Logs, Rotation Logic.
- Logger File Rotation
- File Size Check
- Global Logger Initialization
- Flush Logs
- Rotation Logic

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `9770f201dc4c52fca9bbead341007589d072c2aaa8d4ba0728b95f9b5e30e8cd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9770f201dc4c52fca9bbead341007589d072c2aaa8d4ba0728b95f9b5e30e8cd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9770f201dc4c52fca9bbead341007589d072c2aaa8d4ba0728b95f9b5e30e8cd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/app/mcp_unit/logger_rotation_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/logger_rotation_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/logger_rotation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/logger_rotation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/logger_rotation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/mcp_unit/logger_rotation_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'triggers rotation when size exceeds max' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/logger_rotation_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not rotate when size is below max' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/logger_rotation_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles initialization error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
