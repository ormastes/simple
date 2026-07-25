# HTTP Server on RISC-V Baremetal Specification

> This spec distinguishes the current RV64 HTTP-only live gate from full

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HTTP Server on RISC-V Baremetal Specification

This spec distinguishes the current RV64 HTTP-only live gate from full

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #B6-HTTP-BAREMETAL |
| Category | Infrastructure |
| Status | HTTP-only RV64 live gate passing; HTTPS/TLS still blocked |
| Source | `test/02_integration/http_baremetal_spec.spl` |
| Updated | 2026-07-19 |
| Generator | `simple spipe-docgen` (Simple) |

This spec distinguishes the current RV64 HTTP-only live gate from full
HTTP+HTTPS production readiness. RV64 QEMU now proves packet TX/RX, a boot-local
HTTP response, and optional display/storage service markers. TLS remains
fail-closed until RISC-V has production entropy. Deferred mode stays available
only as a regression boundary for older packet-unavailable images.

## Scenarios

### HTTP baremetal QEMU gate

#### keeps RV64 default mode as the full HTTP plus HTTPS production gate

- expect script default mode remains http gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect_script_default_mode_remains_http_gate("scripts/qemu/qemu_rv64_http_test.shs")
```

</details>

#### keeps RV32 default mode as the production HTTP socket gate

- expect script default mode remains http gate


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect_script_default_mode_remains_http_gate("scripts/qemu/qemu_rv32_http_test.shs")
```

</details>

#### documents RV64 HTTP-only mode as the current live QEMU boundary

- expect script has http only boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect_script_has_http_only_boundary("scripts/qemu/qemu_rv64_http_test.shs")
```

</details>

#### keeps RV64 deferred mode as a packet-unavailable regression boundary

- expect script has deferred boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect_script_has_deferred_boundary("scripts/qemu/qemu_rv64_http_test.shs")
expect(rt_file_read_text("scripts/qemu/qemu_rv64_http_test.shs")).to_contain("Network packet RX unavailable")
```

</details>

#### documents RV32 deferred mode as the current non-production boundary

- expect script has deferred boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect_script_has_deferred_boundary("scripts/qemu/qemu_rv32_http_test.shs")
expect(rt_file_read_text("scripts/qemu/qemu_rv32_http_test.shs")).to_contain("Network packet TX unavailable")
```

</details>

### HTTP baremetal production blockers

#### records RV64 packet RX/TX and HTTP-only QEMU smoke as prebuilt-only evidence until source rebuild passes

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = rt_file_read_text("doc/03_plan/os/riscv/riscv_rtl_simpleos_boot.md")

expect(plan).to_contain("HTTP-only prebuilt gate passing; current-source QEMU blocked")
expect(plan).to_contain("packet RX/TX through the boot-local")
expect(plan).to_contain("--expect-http-only")
expect(plan).to_contain("Storage service ready")
expect(plan).to_contain("NVFS root superblock ready")
expect(plan).to_contain("Do not treat the")
expect(plan).to_contain("passing prebuilt ELF smoke as current-source rebuild evidence")
```

</details>

#### records TLS as blocked rather than production-ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = rt_file_read_text("doc/03_plan/os/riscv/riscv_rtl_simpleos_boot.md")

expect(plan).to_contain("TLS Baremetal")
expect(plan).to_contain("Blocked, not complete")
expect(plan).to_contain("Tls13AcceptResult.Accepted")
expect(plan).to_contain("placeholder_entropy")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
