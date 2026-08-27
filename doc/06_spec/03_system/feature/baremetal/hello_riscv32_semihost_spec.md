# RISC-V 32 Semihosting

> Tests RISC-V 32-bit semihosting functionality including SYS_WRITE0 and SYS_EXIT calls. Verifies that bare-metal RV32 programs can communicate with the host debugger or QEMU through the standard semihosting interface.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RISC-V 32 Semihosting

Tests RISC-V 32-bit semihosting functionality including SYS_WRITE0 and SYS_EXIT calls. Verifies that bare-metal RV32 programs can communicate with the host debugger or QEMU through the standard semihosting interface.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | In Progress |
| Source | `test/03_system/feature/baremetal/hello_riscv32_semihost_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests RISC-V 32-bit semihosting functionality including SYS_WRITE0 and SYS_EXIT
calls. Verifies that bare-metal RV32 programs can communicate with the host
debugger or QEMU through the standard semihosting interface.

## Scenarios

### RISC-V 32 Semihosting - Hello World

<details>
<summary>Advanced: prints hello world message</summary>

#### prints hello world message _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- prints hello world message


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prints hello world message")
if _can_run_hello:
    val output = run_qemu_output(BINARY_PATH, 10000)
    expect(output).to_contain("Hello, RISC-V 32!")
else:
    print "SKIP: QEMU or binary not available"
```

</details>


</details>

<details>
<summary>Advanced: outputs semihost test success marker</summary>

#### outputs semihost test success marker _(slow)_

- outputs semihost test success marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("outputs semihost test success marker")
if _can_run_hello:
    val output = run_qemu_output(BINARY_PATH, 10000)
    expect(output).to_contain("SEMIHOST TEST")
    expect(output).to_contain("Success")
else:
    print "SKIP: QEMU or binary not available"
```

</details>


</details>

<details>
<summary>Advanced: outputs exit code 0 message</summary>

#### outputs exit code 0 message _(slow)_

- outputs exit code 0 message


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("outputs exit code 0 message")
if _can_run_hello:
    val output = run_qemu_output(BINARY_PATH, 10000)
    expect(output).to_contain("exit code 0")
else:
    print "SKIP: QEMU or binary not available"
```

</details>


</details>

<details>
<summary>Advanced: completes within 5 seconds</summary>

#### completes within 5 seconds _(slow)_

- completes within 5 seconds


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("completes within 5 seconds")
if _can_run_hello:
    val start = rt_time_now_unix_micros()
    val output = run_qemu_output(BINARY_PATH, 10000)
    val end = rt_time_now_unix_micros()
    val duration_ms = (end - start) / 1000
    expect(duration_ms).to_be_less_than(5000)
else:
    print "SKIP: QEMU or binary not available"
```

</details>


</details>

### RISC-V 32 Semihosting - Intensive C Test

<details>
<summary>Advanced: runs 89 hardware tests on QEMU</summary>

#### runs 89 hardware tests on QEMU _(slow)_

- runs 89 hardware tests on QEMU


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs 89 hardware tests on QEMU")
if _can_run_intensive:
    val output = run_qemu_output(INTENSIVE_PATH, 15000)
    expect(output).to_contain("89 examples, 0 failures")
else:
    print "SKIP: QEMU or intensive ELF not available"
```

</details>


</details>

<details>
<summary>Advanced: verifies semihosting operations</summary>

#### verifies semihosting operations _(slow)_

- verifies semihosting operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("verifies semihosting operations")
if _can_run_intensive:
    val output = run_qemu_output(INTENSIVE_PATH, 15000)
    expect(output).to_contain("SYS_WRITE0 outputs string")
    expect(output).to_contain("SYS_CLOCK returns non-negative value")
else:
    print "SKIP: QEMU or intensive ELF not available"
```

</details>


</details>

<details>
<summary>Advanced: verifies 32-bit arithmetic on real RV32</summary>

#### verifies 32-bit arithmetic on real RV32 _(slow)_

- verifies 32-bit arithmetic on real RV32


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("verifies 32-bit arithmetic on real RV32")
if _can_run_intensive:
    val output = run_qemu_output(INTENSIVE_PATH, 15000)
    expect(output).to_contain("INT32_MAX is 0x7FFFFFFF")
    expect(output).to_contain("signed right shift preserves sign")
else:
    print "SKIP: QEMU or intensive ELF not available"
```

</details>


</details>

<details>
<summary>Advanced: verifies mcycle counter reading</summary>

#### verifies mcycle counter reading _(slow)_

- verifies mcycle counter reading


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("verifies mcycle counter reading")
if _can_run_intensive:
    val output = run_qemu_output(INTENSIVE_PATH, 15000)
    expect(output).to_contain("mcycle is readable")
    expect(output).to_contain("mcycle advances")
    expect(output).to_contain("mcycle difference is reasonable")
else:
    print "SKIP: QEMU or intensive ELF not available"
```

</details>


</details>

<details>
<summary>Advanced: verifies QEMU platform (RV32, M-mode, little-endian)</summary>

#### verifies QEMU platform (RV32, M-mode, little-endian) _(slow)_

- verifies QEMU platform (RV32, M-mode, little-endian)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("verifies QEMU platform (RV32, M-mode, little-endian)")
if _can_run_intensive:
    val output = run_qemu_output(INTENSIVE_PATH, 15000)
    expect(output).to_contain("running on RV32 (pointer is 4 bytes)")
    expect(output).to_contain("mhartid is 0 (boot hart)")
    expect(output).to_contain("RISC-V is little-endian")
else:
    print "SKIP: QEMU or intensive ELF not available"
```

</details>


</details>

<details>
<summary>Advanced: verifies interrupt cause bits are RV32 (bit 31)</summary>

#### verifies interrupt cause bits are RV32 (bit 31) _(slow)_

- verifies interrupt cause bits are RV32 (bit 31)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("verifies interrupt cause bits are RV32 (bit 31)")
if _can_run_intensive:
    val output = run_qemu_output(INTENSIVE_PATH, 15000)
    expect(output).to_contain("interrupt bit is 0x80000000 (bit 31)")
    expect(output).to_contain("M-mode timer interrupt code is 7")
else:
    print "SKIP: QEMU or intensive ELF not available"
```

</details>


</details>

<details>
<summary>Advanced: verifies stack alignment on real hardware</summary>

#### verifies stack alignment on real hardware _(slow)_

- verifies stack alignment on real hardware


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("verifies stack alignment on real hardware")
if _can_run_intensive:
    val output = run_qemu_output(INTENSIVE_PATH, 15000)
    expect(output).to_contain("stack is 16-byte aligned")
    expect(output).to_contain("code is in expected memory region")
else:
    print "SKIP: QEMU or intensive ELF not available"
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 11 |
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

- Canonical SPipe generation for source `359918e46e2c21b22235d99706c04094432cf5ea0eab4ade10fc1f522cf9fa93`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `359918e46e2c21b22235d99706c04094432cf5ea0eab4ade10fc1f522cf9fa93`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `359918e46e2c21b22235d99706c04094432cf5ea0eab4ade10fc1f522cf9fa93`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/baremetal/hello_riscv32_semihost_spec.spl
mirror: doc/06_spec/03_system/feature/baremetal/hello_riscv32_semihost_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/baremetal/hello_riscv32_semihost_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/baremetal/hello_riscv32_semihost_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/baremetal/hello_riscv32_semihost_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prints hello world message' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/hello_riscv32_semihost_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'outputs semihost test success marker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/hello_riscv32_semihost_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'outputs exit code 0 message' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
