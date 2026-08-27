# Kv260 Network Verification Gate Specification

> Tests covering KV260 network verification gate script structure, KV260 network guide evidence separation, KV260 physical bitstream artifact.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Kv260 Network Verification Gate Specification

## Scenarios

### KV260 network verification gate script structure

#### AC-7: requires --artifacts argument

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- AC-7: requires --artifacts argument


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-7: requires --artifacts argument")
val script = rt_file_read_text("scripts/fpga/check_kv260_simple_rv64_network.shs")
expect(script).to_contain("--artifacts")
expect(script).to_contain("fail \"missing_artifact_dir\"")
```

</details>

#### AC-7: checks all six required artifact files

- AC-7: checks all six required artifact files


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-7: checks all six required artifact files")
val script = rt_file_read_text("scripts/fpga/check_kv260_simple_rv64_network.shs")
expect(script).to_contain("program.log")
expect(script).to_contain("pl_uart.log")
expect(script).to_contain("network.sdn")
expect(script).to_contain("http_health.log")
expect(script).to_contain("http_root.log")
expect(script).to_contain("ssh.log")
```

</details>

#### AC-7: fails when program_log is missing

- AC-7: fails when program_log is missing


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-7: fails when program_log is missing")
val script = rt_file_read_text("scripts/fpga/check_kv260_simple_rv64_network.shs")
expect(script).to_contain("fail \"program_log_missing\"")
```

</details>

#### AC-7: fails when pl_uart_log is missing

- AC-7: fails when pl_uart_log is missing


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-7: fails when pl_uart_log is missing")
val script = rt_file_read_text("scripts/fpga/check_kv260_simple_rv64_network.shs")
expect(script).to_contain("fail \"pl_uart_log_missing\"")
```

</details>

#### AC-7: fails when network metadata is missing

- AC-7: fails when network metadata is missing


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-7: fails when network metadata is missing")
val script = rt_file_read_text("scripts/fpga/check_kv260_simple_rv64_network.shs")
expect(script).to_contain("fail \"network_metadata_missing\"")
```

</details>

#### AC-7: fails when http_health_log is missing

- AC-7: fails when http_health_log is missing


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-7: fails when http_health_log is missing")
val script = rt_file_read_text("scripts/fpga/check_kv260_simple_rv64_network.shs")
expect(script).to_contain("fail \"http_health_log_missing\"")
```

</details>

#### AC-7: fails when http_root_log is missing

- AC-7: fails when http_root_log is missing


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-7: fails when http_root_log is missing")
val script = rt_file_read_text("scripts/fpga/check_kv260_simple_rv64_network.shs")
expect(script).to_contain("fail \"http_root_log_missing\"")
```

</details>

#### AC-7: fails when ssh_log is missing

- AC-7: fails when ssh_log is missing


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-7: fails when ssh_log is missing")
val script = rt_file_read_text("scripts/fpga/check_kv260_simple_rv64_network.shs")
expect(script).to_contain("fail \"ssh_log_missing\"")
```

</details>

#### AC-7: validates bitstream startup marker in program log

- AC-7: validates bitstream startup marker in program log


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-7: validates bitstream startup marker in program log")
val script = rt_file_read_text("scripts/fpga/check_kv260_simple_rv64_network.shs")
expect(script).to_contain("End of startup status: HIGH")
expect(script).to_contain("fail \"kv260_bitstream_startup_missing\"")
```

</details>

#### AC-7: validates SimpleOS RV64 marker in PL UART log

- AC-7: validates SimpleOS RV64 marker in PL UART log


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-7: validates SimpleOS RV64 marker in PL UART log")
val script = rt_file_read_text("scripts/fpga/check_kv260_simple_rv64_network.shs")
expect(script).to_contain("SimpleOS RV64")
expect(script).to_contain("fail \"pl_uart_simpleos_rv64_marker_missing\"")
```

</details>

#### AC-7: validates PMM OK boot marker in PL UART log

- AC-7: validates PMM OK boot marker in PL UART log


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-7: validates PMM OK boot marker in PL UART log")
val script = rt_file_read_text("scripts/fpga/check_kv260_simple_rv64_network.shs")
expect(script).to_contain("PMM OK")
expect(script).to_contain("fail \"pl_uart_boot_marker_missing\"")
```

</details>

#### AC-7: validates Network service ready in PL UART log

- AC-7: validates Network service ready in PL UART log


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-7: validates Network service ready in PL UART log")
val script = rt_file_read_text("scripts/fpga/check_kv260_simple_rv64_network.shs")
expect(script).to_contain("Network service ready")
expect(script).to_contain("fail \"pl_uart_network_ready_missing\"")
```

</details>

#### AC-7: validates physical transport mapping with known types

- AC-7: validates physical transport mapping with known types


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-7: validates physical transport mapping with known types")
val script = rt_file_read_text("scripts/fpga/check_kv260_simple_rv64_network.shs")
expect(script).to_contain("ethernet-mac")
expect(script).to_contain("ps-pl-bridge")
expect(script).to_contain("tap-bridge")
expect(script).to_contain("uart-slip")
expect(script).to_contain("explicit-port-forward")
expect(script).to_contain("fail \"physical_transport_mapping_missing\"")
expect(script).to_contain("fail \"host_endpoint_missing\"")
expect(script).to_contain("fail \"target_endpoint_missing\"")
```

</details>

#### AC-7: validates HTTP 200 for /health

- AC-7: validates HTTP 200 for /health


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-7: validates HTTP 200 for /health")
val script = rt_file_read_text("scripts/fpga/check_kv260_simple_rv64_network.shs")
expect(script).to_contain("fail \"http_health_200_missing\"")
expect(script).to_contain("fail \"http_health_path_missing\"")
expect(script).to_contain("pass \"http_health_200\"")
```

</details>

#### AC-7: validates HTTP 200 for root

- AC-7: validates HTTP 200 for root


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-7: validates HTTP 200 for root")
val script = rt_file_read_text("scripts/fpga/check_kv260_simple_rv64_network.shs")
expect(script).to_contain("fail \"http_root_200_missing\"")
expect(script).to_contain("fail \"http_root_path_missing\"")
expect(script).to_contain("pass \"http_root_200\"")
```

</details>

#### AC-7: validates SSH banner and login

- AC-7: validates SSH banner and login


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-7: validates SSH banner and login")
val script = rt_file_read_text("scripts/fpga/check_kv260_simple_rv64_network.shs")
expect(script).to_contain("SSH-")
expect(script).to_contain("sshd banner")
expect(script).to_contain("fail \"ssh_banner_missing\"")
expect(script).to_contain("fail \"ssh_login_missing\"")
expect(script).to_contain("pass \"ssh_banner_login\"")
```

</details>

#### AC-7: uses set -eu for strict error handling

- AC-7: uses set -eu for strict error handling


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-7: uses set -eu for strict error handling")
val script = rt_file_read_text("scripts/fpga/check_kv260_simple_rv64_network.shs")
expect(script).to_contain("set -eu")
```

</details>

#### AC-7: fail function exits nonzero

- AC-7: fail function exits nonzero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-7: fail function exits nonzero")
val script = rt_file_read_text("scripts/fpga/check_kv260_simple_rv64_network.shs")
expect(script).to_contain("exit 1")
```

</details>

#### AC-7: does not accept QEMU-only evidence

- AC-7: does not accept QEMU-only evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-7: does not accept QEMU-only evidence")
val script = rt_file_read_text("scripts/fpga/check_kv260_simple_rv64_network.shs")
expect(script).to_contain("does not accept QEMU-only")
```

</details>

### KV260 network guide evidence separation

#### AC-8: guide lists physical KV260 bitstream load as a separate lane

- AC-8: guide lists physical KV260 bitstream load as a separate lane


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-8: guide lists physical KV260 bitstream load as a separate lane")
val guide = rt_file_read_text("doc/07_guide/hardware/fpga/kv260_rv64gc_fpga_boot.md")
expect(guide).to_contain("Physical KV260 bitstream load")
expect(guide).to_contain("Verified")
```

</details>

#### AC-8: guide lists QEMU RV64 HTTP as QEMU-only proof

- AC-8: guide lists QEMU RV64 HTTP as QEMU-only proof


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-8: guide lists QEMU RV64 HTTP as QEMU-only proof")
val guide = rt_file_read_text("doc/07_guide/hardware/fpga/kv260_rv64gc_fpga_boot.md")
expect(guide).to_contain("QEMU RV64 HTTP")
expect(guide).to_contain("QEMU-only proof")
```

</details>

#### AC-8: guide lists RTL-sim proof for generated handoff

- AC-8: guide lists RTL-sim proof for generated handoff


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-8: guide lists RTL-sim proof for generated handoff")
val guide = rt_file_read_text("doc/07_guide/hardware/fpga/kv260_rv64gc_fpga_boot.md")
expect(guide).to_contain("Generated RV64 Linux handoff")
expect(guide).to_contain("RTL-sim proof")
```

</details>

#### AC-8: guide lists physical PL UART as not verified

- AC-8: guide lists physical PL UART as not verified


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-8: guide lists physical PL UART as not verified")
val guide = rt_file_read_text("doc/07_guide/hardware/fpga/kv260_rv64gc_fpga_boot.md")
expect(guide).to_contain("Physical PL UART boot log")
expect(guide).to_contain("Not verified")
```

</details>

#### AC-8: guide lists physical network as not verified

- AC-8: guide lists physical network as not verified


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-8: guide lists physical network as not verified")
val guide = rt_file_read_text("doc/07_guide/hardware/fpga/kv260_rv64gc_fpga_boot.md")
expect(guide).to_contain("Physical Simple RV64 network")
expect(guide).to_contain("Not verified")
```

</details>

#### AC-8: guide lists physical HTTP server as not verified

- AC-8: guide lists physical HTTP server as not verified


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-8: guide lists physical HTTP server as not verified")
val guide = rt_file_read_text("doc/07_guide/hardware/fpga/kv260_rv64gc_fpga_boot.md")
expect(guide).to_contain("Physical HTTP server")
expect(guide).to_contain("Not verified")
```

</details>

#### AC-8: guide lists physical sshd as not verified

- AC-8: guide lists physical sshd as not verified


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-8: guide lists physical sshd as not verified")
val guide = rt_file_read_text("doc/07_guide/hardware/fpga/kv260_rv64gc_fpga_boot.md")
expect(guide).to_contain("Physical sshd")
expect(guide).to_contain("Not verified")
```

</details>

#### AC-8: guide explicitly warns QEMU is not physical proof

- AC-8: guide explicitly warns QEMU is not physical proof


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-8: guide explicitly warns QEMU is not physical proof")
val guide = rt_file_read_text("doc/07_guide/hardware/fpga/kv260_rv64gc_fpga_boot.md")
expect(guide).to_contain("must not be\nused to claim physical FPGA web or SSH readiness")
```

</details>

#### AC-8: guide cross-references the FR tracking doc

- AC-8: guide cross-references the FR tracking doc


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-8: guide cross-references the FR tracking doc")
val guide = rt_file_read_text("doc/07_guide/hardware/fpga/kv260_rv64gc_fpga_boot.md")
expect(guide).to_contain("kv260_simple_rv64_network_verification_2026-05-29.md")
```

</details>

### KV260 physical bitstream artifact

#### AC-1: physical program log exists with startup marker

- AC-1: physical program log exists with startup marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("AC-1: physical program log exists with startup marker")
val log = rt_file_read_text("build/kv260_uart_program_20260529_124641/kv260_program_20260529_124641.log")
expect(log).to_contain("End of startup status: HIGH")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/hardware/kv260_network_verification_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering KV260 network verification gate script structure, KV260 network guide evidence separation, KV260 physical bitstream artifact.
- KV260 network verification gate script structure
- KV260 network guide evidence separation
- KV260 physical bitstream artifact

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
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

- Canonical SPipe generation for source `c6837e84333ff35541d099bc5382bc24d1e456a2f4c7a47d1e749c7b497d41f1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c6837e84333ff35541d099bc5382bc24d1e456a2f4c7a47d1e749c7b497d41f1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c6837e84333ff35541d099bc5382bc24d1e456a2f4c7a47d1e749c7b497d41f1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/hardware/kv260_network_verification_gate_spec.spl
mirror: doc/06_spec/03_system/hardware/kv260_network_verification_gate_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/hardware/kv260_network_verification_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/hardware/kv260_network_verification_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/hardware/kv260_network_verification_gate_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-7: requires --artifacts argument' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/hardware/kv260_network_verification_gate_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-7: checks all six required artifact files' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/hardware/kv260_network_verification_gate_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-7: fails when program_log is missing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
