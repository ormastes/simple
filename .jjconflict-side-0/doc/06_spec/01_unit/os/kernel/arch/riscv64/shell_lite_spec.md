# RV64 Serial Management Shell Specification

> Verifies the UART telnet/ssh-over-serial management fallback used when the

<!-- sdn-diagram:id=shell_lite_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shell_lite_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shell_lite_spec -> std
shell_lite_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shell_lite_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 Serial Management Shell Specification

Verifies the UART telnet/ssh-over-serial management fallback used when the

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | riscv64-fpga-simpleos |
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/os/kernel/arch/riscv64/shell_lite_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies the UART telnet/ssh-over-serial management fallback used when the
FPGA/board has no working network. Tests the pure command dispatch: a given
input line must produce the expected response, so a broken shell fails here.

## Scenarios

### rv64 serial shell dispatch

#### help lists the commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv64_shell_dispatch("help", 0)).to_equal(rv64_shell_help())
```

</details>

#### echo returns its argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv64_shell_dispatch("echo hello world", 0)).to_equal("hello world")
```

</details>

#### net reports unavailable when network is down

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv64_shell_dispatch("net", 0)).to_equal("network: unavailable - UART telnet/ssh fallback in use")
```

</details>

#### net reports ready when network is up

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv64_shell_dispatch("net", 1)).to_equal("network: ready")
```

</details>

#### info identifies the rv64 serial console

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv64_shell_dispatch("info", 0)).to_equal("SimpleOS RV64 (riscv64) - serial console fallback")
```

</details>

#### reboot acknowledges

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv64_shell_dispatch("reboot", 0)).to_equal("rebooting...")
```

</details>

#### unknown command is reported, not silently dropped

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv64_shell_dispatch("frobnicate", 0)).to_equal("unknown command: frobnicate\r\nType 'help' for commands.")
```

</details>

#### empty line yields empty response

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv64_shell_dispatch("", 0)).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
