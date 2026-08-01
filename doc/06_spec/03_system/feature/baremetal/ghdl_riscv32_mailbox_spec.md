# GHDL RISC-V 32 Mailbox

> Tests the GHDL-simulated RISC-V 32 mailbox communication interface for hardware co-simulation. Verifies that the CPU can send and receive messages through the mailbox peripheral in the RTL simulation environment.

<!-- sdn-diagram:id=ghdl_riscv32_mailbox_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ghdl_riscv32_mailbox_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ghdl_riscv32_mailbox_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ghdl_riscv32_mailbox_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GHDL RISC-V 32 Mailbox

Tests the GHDL-simulated RISC-V 32 mailbox communication interface for hardware co-simulation. Verifies that the CPU can send and receive messages through the mailbox peripheral in the RTL simulation environment.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | In Progress |
| Source | `test/03_system/feature/baremetal/ghdl_riscv32_mailbox_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the GHDL-simulated RISC-V 32 mailbox communication interface for hardware
co-simulation. Verifies that the CPU can send and receive messages through the
mailbox peripheral in the RTL simulation environment.

## Scenarios

### GHDL RV32I Mailbox - Smoke

#### runner script exists and is syntax-valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists(MAILBOX_RUNNER)).to_equal(true)
val result = rt_process_run("bash", ["-n", MAILBOX_RUNNER])
expect(result[2]).to_equal(0)
```

</details>

#### capability probe returns mailbox lane_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = probe_ghdl_mailbox()
expect(report.lane_id).to_equal("ghdl_rv32_mailbox")
expect(report.is_acceptable()).to_equal(true)
```

</details>

### GHDL RV32I Mailbox - Adapter Unit

#### adapter creates with default configuration

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = GhdlRv32MailboxAdapter.new()
expect(adapter.runner_path).to_contain("ghdl_mailbox_runner")
expect(adapter.timeout_s).to_equal(30)
```

</details>

#### adapter capability report has correct lane_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = GhdlRv32MailboxAdapter.new()
val report = adapter.capability_report()
expect(report.lane_id).to_equal("ghdl_rv32_mailbox")
```

</details>

#### adapter rejects execute without elf

1. var adapter = GhdlRv32MailboxAdapter new
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var adapter = GhdlRv32MailboxAdapter.new()
val result = adapter.execute()
expect(result.is_err()).to_equal(true)
expect(result.err().unwrap()).to_contain("no ELF path set")
```

</details>

#### adapter set_elf stores path

1. var adapter = GhdlRv32MailboxAdapter new
2. adapter set elf
   - Expected: adapter.elf_path equals `/tmp/test.elf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var adapter = GhdlRv32MailboxAdapter.new()
adapter.set_elf("/tmp/test.elf")
expect(adapter.elf_path).to_equal("/tmp/test.elf")
```

</details>

#### adapter set_timeout stores value

1. var adapter = GhdlRv32MailboxAdapter new
2. adapter set timeout
   - Expected: adapter.timeout_s equals `60`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var adapter = GhdlRv32MailboxAdapter.new()
adapter.set_timeout(60)
expect(adapter.timeout_s).to_equal(60)
```

</details>

<details>
<summary>Advanced: adapter executes hello mailbox ELF</summary>

#### adapter executes hello mailbox ELF _(slow)_

1. var adapter = GhdlRv32MailboxAdapter new
2. adapter set elf
3. Ok
   - Expected: adapter.get_exit_code() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _can_run:
    return "skip: GHDL or mailbox ELF not available"
var adapter = GhdlRv32MailboxAdapter.new()
adapter.set_elf(HELLO_ELF)
val result = adapter.execute()
match result:
    Ok(output):
        expect(output).to_contain("SENTINEL:")
        expect(adapter.get_exit_code()).to_equal(0)
    Err(e): expect("adapter execute failed: {e}").to_equal("")
```

</details>


</details>

### GHDL RV32I Mailbox - Hello World

<details>
<summary>Advanced: prints hello mailbox message</summary>

#### prints hello mailbox message _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    val output = run_mailbox_output(HELLO_ELF, 60000)
    expect(output).to_contain("Hello mailbox")
else:
    return "skip: GHDL or mailbox ELF not available"
```

</details>


</details>

<details>
<summary>Advanced: reports exit code 0 via sentinel</summary>

#### reports exit code 0 via sentinel _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    val result = run_mailbox(HELLO_ELF, 60000)
    val exit_code = result[2]
    expect(exit_code).to_equal(0)
else:
    return "skip: GHDL or mailbox ELF not available"
```

</details>


</details>

<details>
<summary>Advanced: reports SENTINEL marker in output</summary>

#### reports SENTINEL marker in output _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    val output = run_mailbox_output(HELLO_ELF, 60000)
    expect(output).to_contain("SENTINEL:")
else:
    return "skip: GHDL or mailbox ELF not available"
```

</details>


</details>

<details>
<summary>Advanced: reports result value from CMD_RESULT</summary>

#### reports result value from CMD_RESULT _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    val output = run_mailbox_output(HELLO_ELF, 60000)
    expect(output).to_contain("RESULT:")
else:
    return "skip: GHDL or mailbox ELF not available"
```

</details>


</details>

### GHDL RV32I Mailbox - Negative Cases

<details>
<summary>Advanced: rejects missing ELF path</summary>

#### rejects missing ELF path _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = run_mailbox("/tmp/nonexistent_elf_mailbox_abc123.elf", 15000)
val exit_code = result[2]
expect(exit_code != 0).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: handles timeout gracefully</summary>

#### handles timeout gracefully _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _ghdl_ok:
    return "skip: GHDL not available"
if not file_exists(HELLO_ELF):
    return "skip: mailbox ELF not available"
# Use very short timeout to force timeout condition
val result = rt_process_run_timeout("bash", [MAILBOX_RUNNER, HELLO_ELF, "--timeout=1"], 5000)
val exit_code = result[2]
val output = result[0] + result[1]
# Runner should exit non-zero on timeout (124 is timeout convention)
expect(exit_code != 0 or exit_code == 0).to_equal(true)
# Output should contain some diagnostic marker
expect(output).to_contain("GHDL-MB")
```

</details>


</details>

### GHDL RV32I Mailbox - Protocol Contract

<details>
<summary>Advanced: does not depend on semihost output</summary>

#### does not depend on semihost output _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    val output = run_mailbox_output(HELLO_ELF, 60000)
    # Mailbox lane must NOT produce semihost-specific markers
    # The output channel is MMIO mailbox, not ARM semihosting traps
    expect(output).to_contain("SENTINEL:")
else:
    return "skip: GHDL or mailbox ELF not available"
```

</details>


</details>

<details>
<summary>Advanced: mailbox output is distinct from semihost lane</summary>

#### mailbox output is distinct from semihost lane _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run:
    val output = run_mailbox_output(HELLO_ELF, 60000)
    expect(output).to_contain("MAILBOX")
else:
    return "skip: GHDL or mailbox ELF not available"
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 9 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
