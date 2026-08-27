# Compressed Logging E2E

> Tests the full compressed logging pipeline from QEMU semihost output to decoded text. Verifies the SYS_WRITEC-based binary protocol (v3) for bandwidth-efficient logging on resource-constrained bare-metal targets.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compressed Logging E2E

Tests the full compressed logging pipeline from QEMU semihost output to decoded text. Verifies the SYS_WRITEC-based binary protocol (v3) for bandwidth-efficient logging on resource-constrained bare-metal targets.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | In Progress |
| Source | `test/03_system/feature/baremetal/compressed_logging_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the full compressed logging pipeline from QEMU semihost output to decoded
text. Verifies the SYS_WRITEC-based binary protocol (v3) for bandwidth-efficient
logging on resource-constrained bare-metal targets.

## Scenarios

### Compressed Logging v3 (SYS_WRITEC)

<details>
<summary>Advanced: QEMU produces binary protocol output</summary>

#### QEMU produces binary protocol output _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- QEMU produces binary protocol output
   - Expected: file_exists(OUTPUT_FILE) is true
   - Expected: bytes[0] as i64 equals `171`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("QEMU produces binary protocol output")
if _can_run:
    run_qemu_to_file(V3_ELF, OUTPUT_FILE, 10000)
    expect(file_exists(OUTPUT_FILE)).to_equal(true)
    val bytes = read_file_bytes(OUTPUT_FILE)
    expect(bytes[0] as i64).to_equal(171)
    expect(bytes.len()).to_be_greater_than(20)
else:
    print "SKIP: QEMU or V3 ELF not available"
```

</details>


</details>

<details>
<summary>Advanced: binary output contains valid frame structure</summary>

#### binary output contains valid frame structure _(slow)_

- binary output contains valid frame structure
   - Expected: bytes[0] as i64 equals `171`
   - Expected: bytes.len() equals `28`
   - Expected: bytes[1] as i64 equals `1`
   - Expected: bytes[14] as i64 equals `171`
   - Expected: bytes[15] as i64 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("binary output contains valid frame structure")
if _can_run:
    run_qemu_to_file(V3_ELF, OUTPUT_FILE, 10000)
    val bytes = read_file_bytes(OUTPUT_FILE)
    expect(bytes[0] as i64).to_equal(171)
    expect(bytes.len()).to_equal(28)
    expect(bytes[1] as i64).to_equal(1)
    expect(bytes[14] as i64).to_equal(171)
    expect(bytes[15] as i64).to_equal(1)
else:
    print "SKIP: QEMU or V3 ELF not available"
```

</details>


</details>

<details>
<summary>Advanced: decoder resolves handles to Hello message</summary>

#### decoder resolves handles to Hello message _(slow)_

- decoder resolves handles to Hello message


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("decoder resolves handles to Hello message")
if _can_run:
    run_qemu_to_file(V3_ELF, OUTPUT_FILE, 10000)
    val decoded = decode_binary_output(OUTPUT_FILE, SMT_FILE)
    expect(decoded).to_contain("Hello, RISC-V 32!")
else:
    print "SKIP: QEMU or V3 ELF not available"
```

</details>


</details>

<details>
<summary>Advanced: decoder resolves all messages</summary>

#### decoder resolves all messages _(slow)_

- decoder resolves all messages


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("decoder resolves all messages")
if _can_run:
    run_qemu_to_file(V3_ELF, OUTPUT_FILE, 10000)
    val decoded = decode_binary_output(OUTPUT_FILE, SMT_FILE)
    expect(decoded).to_contain("Hello, RISC-V 32!")
    expect(decoded).to_contain("SEMIHOST TEST")
    expect(decoded).to_contain("Success")
else:
    print "SKIP: QEMU or V3 ELF not available"
```

</details>


</details>

<details>
<summary>Advanced: compressed binary data is smaller than text strings</summary>

#### compressed binary data is smaller than text strings _(slow)_

- compressed binary data is smaller than text strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compressed binary data is smaller than text strings")
if _can_run:
    run_qemu_to_file(V3_ELF, OUTPUT_FILE, 10000)
    val bytes = read_file_bytes(OUTPUT_FILE)
    expect(bytes.len()).to_be_less_than(50)
else:
    print "SKIP: QEMU or V3 ELF not available"
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 5 |
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

- Canonical SPipe generation for source `2484ca529f161374ed3a5193cb20e01be382e8000470a04476df470690d6b3b1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2484ca529f161374ed3a5193cb20e01be382e8000470a04476df470690d6b3b1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2484ca529f161374ed3a5193cb20e01be382e8000470a04476df470690d6b3b1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/baremetal/compressed_logging_spec.spl
mirror: doc/06_spec/03_system/feature/baremetal/compressed_logging_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/baremetal/compressed_logging_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/baremetal/compressed_logging_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/baremetal/compressed_logging_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/baremetal/compressed_logging_spec.spl:198:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'QEMU produces binary protocol output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/compressed_logging_spec.spl:210:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binary output contains valid frame structure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/compressed_logging_spec.spl:224:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decoder resolves handles to Hello message' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
