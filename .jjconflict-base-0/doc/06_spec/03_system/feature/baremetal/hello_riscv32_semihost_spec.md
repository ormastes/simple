# RISC-V 32 Semihosting

> Tests RISC-V 32-bit semihosting functionality including SYS_WRITE0 and SYS_EXIT calls. Verifies that bare-metal RV32 programs can communicate with the host debugger or QEMU through the standard semihosting interface.

<!-- sdn-diagram:id=hello_riscv32_semihost_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hello_riscv32_semihost_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hello_riscv32_semihost_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hello_riscv32_semihost_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
