# Remote Baremetal QEMU Hello World

> Pure Simple system smoke for the `interpreter(remote(baremetal(riscv32)))` lane using prebuilt RISC-V32 hello-world ELFs.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Remote Baremetal QEMU Hello World

Pure Simple system smoke for the `interpreter(remote(baremetal(riscv32)))` lane using prebuilt RISC-V32 hello-world ELFs.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RBQH-001 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/03_system/feature/app/remote_baremetal/remote_baremetal_qemu_hello_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Pure Simple system smoke for the `interpreter(remote(baremetal(riscv32)))`
lane using prebuilt RISC-V32 hello-world ELFs.

This spec does not go through the Rust CLI mode parser. It exercises the
Pure Simple composite executor directly and verifies that:

- the Pure Simple remote/baremetal executor can run a checked-in SPipe ELF on QEMU
- the stock semihost hello-world fixture still prints short semihost markers

## Examples

```simple
use std.spec.step

val result = run_test_file_composite(HELLO_SPIPE_ELF, options, REMOTE_RISCV32_SPEC)
expect(result.failed).to_equal(0)
expect(result.passed).to_equal(1)
```

## Scenarios

### Pure Simple remote baremetal QEMU hello world

#### runs the checked-in spipe hello elf through stock qemu semihosting

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- runs the checked-in spipe hello elf through stock qemu semihosting


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs the checked-in spipe hello elf through stock qemu semihosting")
if can_run_hello_spipe():
    val output = run_qemu_semihost_output(HELLO_SPIPE_ELF)
    expect(output).to_contain("Baremetal Semihosting")
    expect(output).to_contain("1 examples, 0 failures")
    expect(output).to_contain("Test PASSED")
else:
    print "SKIP: qemu-system-riscv32 or hello spipe elf not available"
```

</details>

#### prints the short semihost hello markers on stock qemu

- prints the short semihost hello markers on stock qemu


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prints the short semihost hello markers on stock qemu")
if can_run_hello_semihost():
    val output = run_qemu_semihost_output(HELLO_SEMIHOST_ELF)
    expect(output).to_contain("Hello, RISC-V 32!")
    expect(output).to_contain("SEMIHOST TEST")
else:
    print "SKIP: qemu-system-riscv32 or hello semihost elf not available"
```

</details>

### Pure Simple remote baremetal GHDL hello world

#### runs the checked-in spipe hello elf through the stock ghdl semihosting runner

- runs the checked-in spipe hello elf through the stock ghdl semihosting runner


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs the checked-in spipe hello elf through the stock ghdl semihosting runner")
if can_run_hello_ghdl():
    val output = run_ghdl_semihost_output(HELLO_SPIPE_ELF)
    expect(output).to_contain("Baremetal Semihosting")
    expect(output).to_contain("1 examples, 0 failures")
    expect(output).to_contain("Test PASSED")
else:
    print "SKIP: ghdl toolchain or hello spipe elf not available"
```

</details>

#### prints the stock spipe summary on the ghdl semihosting runner

- prints the stock spipe summary on the ghdl semihosting runner


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prints the stock spipe summary on the ghdl semihosting runner")
if can_run_hello_ghdl():
    val output = run_ghdl_semihost_output(HELLO_SPIPE_ELF)
    expect(output).to_contain("Baremetal Semihosting")
    expect(output).to_contain("1 examples, 0 failures")
    expect(output).to_contain("Test PASSED")
else:
    print "SKIP: ghdl toolchain or hello spipe elf not available"
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `78c1d88f41144117e6d52683e673aa0cb0953675252bfefa7103916758b0d216`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `78c1d88f41144117e6d52683e673aa0cb0953675252bfefa7103916758b0d216`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `78c1d88f41144117e6d52683e673aa0cb0953675252bfefa7103916758b0d216`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/app/remote_baremetal/remote_baremetal_qemu_hello_spec.spl
mirror: doc/06_spec/03_system/feature/app/remote_baremetal/remote_baremetal_qemu_hello_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/app/remote_baremetal/remote_baremetal_qemu_hello_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/app/remote_baremetal/remote_baremetal_qemu_hello_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/app/remote_baremetal/remote_baremetal_qemu_hello_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs the checked-in spipe hello elf through stock qemu semihosting' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/remote_baremetal/remote_baremetal_qemu_hello_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prints the short semihost hello markers on stock qemu' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/remote_baremetal/remote_baremetal_qemu_hello_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs the checked-in spipe hello elf through the stock ghdl semihosting runner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
