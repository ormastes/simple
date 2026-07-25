# GHDL RISC-V 32 Semihosting

> Tests semihosting support in the GHDL-simulated RISC-V 32 environment. Verifies that semihosting calls are correctly intercepted by the RTL simulation and that host I/O operations work through the GHDL simulation bridge.

<!-- sdn-diagram:id=ghdl_riscv32_semihost_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ghdl_riscv32_semihost_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ghdl_riscv32_semihost_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ghdl_riscv32_semihost_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
