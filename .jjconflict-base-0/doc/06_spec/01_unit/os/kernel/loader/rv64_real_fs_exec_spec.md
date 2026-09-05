# Rv64 Real Fs Exec Specification

> Tests covering RV64 real filesystem execution result boundary.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rv64 Real Fs Exec Specification

## Scenarios

### RV64 real filesystem execution result boundary

#### retains target-origin nonce stdout and exit 37 exactly

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- retains target-origin nonce stdout and exit 37 exactly
   - Expected: completed.bytes.len() equals `expected.len()`
   - Expected: completed.bytes[index] equals `expected[index]`
   - Expected: completed.exit_code equals `37`
   - Expected: retained.bytes.len() equals `expected.len()`
   - Expected: retained.exit_code equals `37`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("retains target-origin nonce stdout and exit 37 exactly")
val expected = "SIMPLEOS_FS_EXEC_OK arch=riscv64 nonce=rv64-real-exec-0001\n".bytes()
rv64_process_stdout_begin()
for byte in expected:
    rv64_process_stdout_write_byte(byte)

val completed = rv64_process_stdout_finish(37)
expect(completed.bytes.len()).to_equal(expected.len())
var index: u64 = 0
while index < expected.len():
    expect(completed.bytes[index]).to_equal(expected[index])
    index = index + 1
expect(completed.exit_code).to_equal(37)
expect(completed.truncated).to_be(false)

# Completion closes the capture. A late kernel or stale-task write must
# not alter the authenticated child result.
rv64_process_stdout_write_byte(0x58u8)
val retained = rv64_process_stdout_last_result()
expect(retained.bytes.len()).to_equal(expected.len())
expect(retained.exit_code).to_equal(37)
expect(retained.truncated).to_be(false)
```

</details>

#### marks oversized child output instead of silently accepting it

- marks oversized child output instead of silently accepting it
   - Expected: completed.bytes.len() equals `RV64_PROCESS_STDOUT_LIMIT`
   - Expected: completed.exit_code equals `37`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("marks oversized child output instead of silently accepting it")
rv64_process_stdout_begin()
var count: u64 = 0
while count < RV64_PROCESS_STDOUT_LIMIT + 1:
    rv64_process_stdout_write_byte(0x41u8)
    count = count + 1

val completed = rv64_process_stdout_finish(37)
expect(completed.bytes.len()).to_equal(RV64_PROCESS_STDOUT_LIMIT)
expect(completed.exit_code).to_equal(37)
expect(completed.truncated).to_be(true)
```

</details>

#### clears stale stdout when filesystem launch fails before user entry

- clears stale stdout when filesystem launch fails before user entry
   - Expected: stale.bytes.len() equals `2`
   - Expected: failed.bytes.len() equals `0`
   - Expected: failed.exit_code equals `-8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("clears stale stdout when filesystem launch fails before user entry")
rv64_process_stdout_begin()
rv64_process_stdout_write_byte(0x4fu8)
rv64_process_stdout_write_byte(0x4bu8)
val stale = rv64_process_stdout_finish(37)
expect(stale.bytes.len()).to_equal(2)

val failed = riscv64_fs_exec_failed_capture(-8)
expect(failed.bytes.len()).to_equal(0)
expect(failed.exit_code).to_equal(-8)
expect(failed.truncated).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/rv64_real_fs_exec_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RV64 real filesystem execution result boundary.
- RV64 real filesystem execution result boundary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `284d1279859e1dc22b909575dccb1478b2cd3be8ef967c0aeb0568dff549928a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `284d1279859e1dc22b909575dccb1478b2cd3be8ef967c0aeb0568dff549928a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `284d1279859e1dc22b909575dccb1478b2cd3be8ef967c0aeb0568dff549928a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/kernel/loader/rv64_real_fs_exec_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/loader/rv64_real_fs_exec_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/loader/rv64_real_fs_exec_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/loader/rv64_real_fs_exec_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/loader/rv64_real_fs_exec_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/loader/rv64_real_fs_exec_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains target-origin nonce stdout and exit 37 exactly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/loader/rv64_real_fs_exec_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'marks oversized child output instead of silently accepting it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/loader/rv64_real_fs_exec_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clears stale stdout when filesystem launch fails before user entry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
