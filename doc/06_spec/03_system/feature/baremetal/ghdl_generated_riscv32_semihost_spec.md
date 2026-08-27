# Ghdl Generated Riscv32 Semihost Specification

> Tests covering Generated RV32 GHDL semihosting.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ghdl Generated Riscv32 Semihost Specification

## Scenarios

### Generated RV32 GHDL semihosting

#### runner script exists and is syntax-valid

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- runner script exists and is syntax-valid
   - Expected: rt_file_exists(GENERATED_RUNNER) is true
   - Expected: result[2] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runner script exists and is syntax-valid")
expect(rt_file_exists(GENERATED_RUNNER)).to_equal(true)
val result = rt_process_run("bash", ["-n", GENERATED_RUNNER])
expect(result[2]).to_equal(0)
```

</details>

<details>
<summary>Advanced: runs hello semihost ELF through the generated core</summary>

#### runs hello semihost ELF through the generated core _(slow)_

- runs hello semihost ELF through the generated core
   - Expected: result[1] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs hello semihost ELF through the generated core")
if not runner_tools_available():
    return "skip: ghdl or riscv objcopy not available"
val result = run_ghdl_output(HELLO_ELF, 120000)
val output = result[0]
expect(result[1]).to_equal(0)
expect(output).to_contain("Hello, RISC-V 32!")
expect(output).to_contain("SEMIHOST TEST")
expect(output).to_contain("Success")
expect(output).to_contain("Test PASSED")
expect(output).to_contain("Cycles:")
```

</details>


</details>

<details>
<summary>Advanced: runs SPipe semihost ELF through the generated core</summary>

#### runs SPipe semihost ELF through the generated core _(slow)_

- runs SPipe semihost ELF through the generated core
   - Expected: result[1] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs SPipe semihost ELF through the generated core")
if not runner_tools_available():
    return "skip: ghdl or riscv objcopy not available"
val result = run_ghdl_output(SPIPE_ELF, 120000)
val output = result[0]
expect(result[1]).to_equal(0)
expect(output).to_contain("Baremetal Semihosting")
expect(output).to_contain("hello_semihost")
expect(output).to_contain("1 examples, 0 failures")
expect(output).to_contain("Test PASSED")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | Active |
| Source | `test/03_system/feature/baremetal/ghdl_generated_riscv32_semihost_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Generated RV32 GHDL semihosting.
- Generated RV32 GHDL semihosting

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 2 |
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

- Canonical SPipe generation for source `4adbf4a38dea5362bd1fffdd0d9ab110508e3639f8f662aae256b279a26dabde`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4adbf4a38dea5362bd1fffdd0d9ab110508e3639f8f662aae256b279a26dabde`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4adbf4a38dea5362bd1fffdd0d9ab110508e3639f8f662aae256b279a26dabde`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/baremetal/ghdl_generated_riscv32_semihost_spec.spl
mirror: doc/06_spec/03_system/feature/baremetal/ghdl_generated_riscv32_semihost_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/baremetal/ghdl_generated_riscv32_semihost_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/baremetal/ghdl_generated_riscv32_semihost_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/baremetal/ghdl_generated_riscv32_semihost_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/baremetal/ghdl_generated_riscv32_semihost_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runner script exists and is syntax-valid' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/ghdl_generated_riscv32_semihost_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs hello semihost ELF through the generated core' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/ghdl_generated_riscv32_semihost_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs SPipe semihost ELF through the generated core' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
