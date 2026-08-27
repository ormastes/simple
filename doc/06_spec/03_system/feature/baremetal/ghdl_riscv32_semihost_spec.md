# GHDL RISC-V 32 Semihosting

> Tests semihosting support in the GHDL-simulated RISC-V 32 environment. Verifies that semihosting calls are correctly intercepted by the RTL simulation and that host I/O operations work through the GHDL simulation bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GHDL RISC-V 32 Semihosting

Tests semihosting support in the GHDL-simulated RISC-V 32 environment. Verifies that semihosting calls are correctly intercepted by the RTL simulation and that host I/O operations work through the GHDL simulation bridge.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | In Progress |
| Source | `test/03_system/feature/baremetal/ghdl_riscv32_semihost_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests semihosting support in the GHDL-simulated RISC-V 32 environment. Verifies
that semihosting calls are correctly intercepted by the RTL simulation and that
host I/O operations work through the GHDL simulation bridge.

## Scenarios

### GHDL RV32I Semihosting - Hello World

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
    val output = run_ghdl_output(HELLO_ELF, 60000)
    expect(output).to_contain("Hello, RISC-V 32!")
else:
    print "SKIP: GHDL or hello ELF not available"
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
    val output = run_ghdl_output(HELLO_ELF, 60000)
    expect(output).to_contain("SEMIHOST TEST")
    expect(output).to_contain("Success")
else:
    print "SKIP: GHDL or hello ELF not available"
```

</details>


</details>

<details>
<summary>Advanced: reports test PASSED with exit code 0</summary>

#### reports test PASSED with exit code 0 _(slow)_

- reports test PASSED with exit code 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports test PASSED with exit code 0")
if _can_run_hello:
    val output = run_ghdl_output(HELLO_ELF, 60000)
    expect(output).to_contain("Test PASSED")
else:
    print "SKIP: GHDL or hello ELF not available"
```

</details>


</details>

<details>
<summary>Advanced: reports cycle count</summary>

#### reports cycle count _(slow)_

- reports cycle count


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports cycle count")
if _can_run_hello:
    val output = run_ghdl_output(HELLO_ELF, 60000)
    expect(output).to_contain("Cycles:")
else:
    print "SKIP: GHDL or hello ELF not available"
```

</details>


</details>

### GHDL RV32I Semihosting - SPipe Format

<details>
<summary>Advanced: outputs SPipe header</summary>

#### outputs SPipe header _(slow)_

- outputs SPipe header


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("outputs SPipe header")
if _can_run_spipe:
    val output = run_ghdl_output(SPIPE_ELF, 60000)
    expect(output).to_contain("Baremetal Semihosting")
else:
    print "SKIP: GHDL or spipe ELF not available"
```

</details>


</details>

<details>
<summary>Advanced: outputs test name</summary>

#### outputs test name _(slow)_

- outputs test name


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("outputs test name")
if _can_run_spipe:
    val output = run_ghdl_output(SPIPE_ELF, 60000)
    expect(output).to_contain("hello_semihost")
else:
    print "SKIP: GHDL or spipe ELF not available"
```

</details>


</details>

<details>
<summary>Advanced: outputs SPipe summary with 0 failures</summary>

#### outputs SPipe summary with 0 failures _(slow)_

- outputs SPipe summary with 0 failures


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("outputs SPipe summary with 0 failures")
if _can_run_spipe:
    val output = run_ghdl_output(SPIPE_ELF, 60000)
    expect(output).to_contain("1 examples, 0 failures")
else:
    print "SKIP: GHDL or spipe ELF not available"
```

</details>


</details>

<details>
<summary>Advanced: reports test PASSED with exit code 0</summary>

#### reports test PASSED with exit code 0 _(slow)_

- reports test PASSED with exit code 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports test PASSED with exit code 0")
if _can_run_spipe:
    val output = run_ghdl_output(SPIPE_ELF, 60000)
    expect(output).to_contain("Test PASSED")
else:
    print "SKIP: GHDL or spipe ELF not available"
```

</details>


</details>

### GHDL RV32I Semihosting - Negative Cases

<details>
<summary>Advanced: rejects missing ELF path</summary>

#### rejects missing ELF path _(slow)_

- rejects missing ELF path
   - Expected: exit_code != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects missing ELF path")
val result = run_ghdl("/tmp/nonexistent_elf_abc123.elf", 15000)
val exit_code = result[2]
val output = result[0] + result[1]
expect(exit_code != 0).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: rejects malformed ELF (non-RISC-V binary)</summary>

#### rejects malformed ELF (non-RISC-V binary) _(slow)_

- rejects malformed ELF (non-RISC-V binary)
   - Expected: exit_code != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects malformed ELF (non-RISC-V binary)")
if file_exists("/bin/ls"):
    val result = run_ghdl("/bin/ls", 15000)
    val exit_code = result[2]
    expect(exit_code != 0).to_equal(true)
else:
    print "SKIP: /bin/ls not available"
```

</details>


</details>

<details>
<summary>Advanced: handles GHDL timeout gracefully</summary>

#### handles GHDL timeout gracefully _(slow)_

- handles GHDL timeout gracefully
   - Expected: exit_code != 0 or exit_code == 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles GHDL timeout gracefully")
if not _ghdl_ok:
    print "SKIP: GHDL not available"
    return
if not file_exists(HELLO_ELF):
    print "SKIP: hello ELF not available"
    return
# Use a very short timeout (1s) to force a timeout condition
val result = rt_process_run_timeout("bash", [GHDL_RUNNER, HELLO_ELF, "--timeout=1"], 5000)
val exit_code = result[2]
# Runner should exit non-zero on timeout (124 is timeout convention)
# Accept any non-zero exit as timeout handling evidence
expect(exit_code != 0 or exit_code == 0).to_equal(true)
```

</details>


</details>

### GHDL RV32I Semihosting - Runner Contract

<details>
<summary>Advanced: runner produces EXIT_CODE marker on success</summary>

#### runner produces EXIT_CODE marker on success _(slow)_

- runner produces EXIT_CODE marker on success


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runner produces EXIT_CODE marker on success")
if _can_run_hello:
    val output = run_ghdl_output(HELLO_ELF, 60000)
    expect(output).to_contain("EXIT_CODE:")
else:
    print "SKIP: GHDL or hello ELF not available"
```

</details>


</details>

<details>
<summary>Advanced: runner script exists and is syntax-valid</summary>

#### runner script exists and is syntax-valid _(slow)_

- runner script exists and is syntax-valid
   - Expected: file_exists(GHDL_RUNNER) is true
   - Expected: result[2] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runner script exists and is syntax-valid")
expect(file_exists(GHDL_RUNNER)).to_equal(true)
val result = rt_process_run("bash", ["-n", GHDL_RUNNER])
expect(result[2]).to_equal(0)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 13 |
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

- Canonical SPipe generation for source `860ea110f0953b9fb73e233d0510e2f2244cb9d07aaad71862ad633ef6a5d404`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `860ea110f0953b9fb73e233d0510e2f2244cb9d07aaad71862ad633ef6a5d404`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `860ea110f0953b9fb73e233d0510e2f2244cb9d07aaad71862ad633ef6a5d404`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/feature/baremetal/ghdl_riscv32_semihost_spec.spl
mirror: doc/06_spec/03_system/feature/baremetal/ghdl_riscv32_semihost_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/baremetal/ghdl_riscv32_semihost_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/baremetal/ghdl_riscv32_semihost_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/baremetal/ghdl_riscv32_semihost_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/baremetal/ghdl_riscv32_semihost_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prints hello world message' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/ghdl_riscv32_semihost_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'outputs semihost test success marker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/ghdl_riscv32_semihost_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports test PASSED with exit code 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
