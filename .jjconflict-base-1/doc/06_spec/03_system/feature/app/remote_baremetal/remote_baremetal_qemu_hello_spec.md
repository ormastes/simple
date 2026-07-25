# Remote Baremetal QEMU Hello World

> Pure Simple system smoke for the `interpreter(remote(baremetal(riscv32)))` lane using prebuilt RISC-V32 hello-world ELFs.

<!-- sdn-diagram:id=remote_baremetal_qemu_hello_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=remote_baremetal_qemu_hello_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

remote_baremetal_qemu_hello_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=remote_baremetal_qemu_hello_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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
val result = run_test_file_composite(HELLO_SPIPE_ELF, options, REMOTE_RISCV32_SPEC)
expect(result.failed).to_equal(0)
expect(result.passed).to_equal(1)
```

## Scenarios

### Pure Simple remote baremetal QEMU hello world

#### runs the checked-in spipe hello elf through stock qemu semihosting

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
