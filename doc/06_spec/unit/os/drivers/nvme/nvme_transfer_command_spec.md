# Nvme Transfer Command Specification

> Tests covering NVMe transfer command.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvme Transfer Command Specification

## Scenarios

### NVMe transfer command

#### builds read and write commands without syscall or C bridge state

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds read and write commands without syscall or C bridge state
   - Expected: read.opcode equals `NVME_TRANSFER_OPCODE_READ`
   - Expected: read.nsid equals `1u32`
   - Expected: read.prp1 equals `0x200000u64`
   - Expected: read.cdw10 equals `2u32`
   - Expected: read.cdw11 equals `1u32`
   - Expected: read.cdw12 equals `7u32`
   - Expected: write.opcode equals `NVME_TRANSFER_OPCODE_WRITE`
   - Expected: write.cdw12 equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds read and write commands without syscall or C bridge state")
val read = nvme_read_io_command(0x100000002u64, 8u32, 0x200000u64, 0x100000100u64).unwrap()
expect(read.opcode).to_equal(NVME_TRANSFER_OPCODE_READ)
expect(read.nsid).to_equal(1u32)
expect(read.prp1).to_equal(0x200000u64)
expect(read.cdw10).to_equal(2u32)
expect(read.cdw11).to_equal(1u32)
expect(read.cdw12).to_equal(7u32)

val write = nvme_write_io_command(4u64, 1u32, 0x300000u64, 16u64).unwrap()
expect(write.opcode).to_equal(NVME_TRANSFER_OPCODE_WRITE)
expect(write.cdw12).to_equal(0u32)
```

</details>

#### builds namespace-aware read and write commands for assigned namespaces

- builds namespace-aware read and write commands for assigned namespaces
   - Expected: read.opcode equals `NVME_TRANSFER_OPCODE_READ`
   - Expected: read.nsid equals `7u32`
   - Expected: read.cdw12 equals `1u32`
   - Expected: write.opcode equals `NVME_TRANSFER_OPCODE_WRITE`
   - Expected: write.nsid equals `9u32`
   - Expected: write.cdw12 equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds namespace-aware read and write commands for assigned namespaces")
val read = nvme_read_io_command_for_namespace(7u32, 4u64, 2u32, 0x200000u64, 16u64).unwrap()
expect(read.opcode).to_equal(NVME_TRANSFER_OPCODE_READ)
expect(read.nsid).to_equal(7u32)
expect(read.cdw12).to_equal(1u32)

val write = nvme_write_io_command_for_namespace(9u32, 8u64, 1u32, 0x300000u64, 16u64).unwrap()
expect(write.opcode).to_equal(NVME_TRANSFER_OPCODE_WRITE)
expect(write.nsid).to_equal(9u32)
expect(write.cdw12).to_equal(0u32)
```

</details>

#### rejects unsafe ranges before command submission

- rejects unsafe ranges before command submission
   - Expected: nvme_read_io_command_for_namespace(0u32, 0u64, 1u32, 0x200000u64, 16u64).unwrap_err() equals `nvme-io-namespace-zero`
   - Expected: nvme_io_lba_range_reason(0u64, 0u32, 16u64) equals `nvme-io-zero-sector-count`
   - Expected: nvme_io_lba_range_reason(0u64, 65537u32, 70000u64) equals `nvme-io-sector-count-too-large`
   - Expected: nvme_io_lba_range_reason(15u64, 2u32, 16u64) equals `nvme-io-beyond-namespace-capacity`
   - Expected: nvme_read_io_command(0u64, 1u32, 0u64, 16u64).unwrap_err() equals `nvme-io-dma-buffer-zero`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unsafe ranges before command submission")
expect(nvme_read_io_command_for_namespace(0u32, 0u64, 1u32, 0x200000u64, 16u64).unwrap_err()).to_equal("nvme-io-namespace-zero")
expect(nvme_io_lba_range_reason(0u64, 0u32, 16u64)).to_equal("nvme-io-zero-sector-count")
expect(nvme_io_lba_range_reason(0u64, 65537u32, 70000u64)).to_equal("nvme-io-sector-count-too-large")
expect(nvme_io_lba_range_reason(15u64, 2u32, 16u64)).to_equal("nvme-io-beyond-namespace-capacity")
expect(nvme_read_io_command(0u64, 1u32, 0u64, 16u64).unwrap_err()).to_equal("nvme-io-dma-buffer-zero")
```

</details>

#### shares flush command and completion status decoding

- shares flush command and completion status decoding
   - Expected: flush.opcode equals `0u8`
   - Expected: flush.nsid equals `1u32`
   - Expected: ns_flush.opcode equals `0u8`
   - Expected: ns_flush.nsid equals `7u32`
   - Expected: nvme_flush_io_command_for_namespace(0u32).unwrap_err() equals `nvme-io-namespace-zero`
   - Expected: nvme_io_status_code(0u32) equals `0u32`
   - Expected: nvme_io_status_code(4u32 << 17) equals `4u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shares flush command and completion status decoding")
val flush = nvme_flush_io_command()
expect(flush.opcode).to_equal(0u8)
expect(flush.nsid).to_equal(1u32)
val ns_flush = nvme_flush_io_command_for_namespace(7u32).unwrap()
expect(ns_flush.opcode).to_equal(0u8)
expect(ns_flush.nsid).to_equal(7u32)
expect(nvme_flush_io_command_for_namespace(0u32).unwrap_err()).to_equal("nvme-io-namespace-zero")
expect(nvme_io_status_code(0u32)).to_equal(0u32)
expect(nvme_io_status_code(4u32 << 17)).to_equal(4u32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/drivers/nvme/nvme_transfer_command_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering NVMe transfer command.
- NVMe transfer command

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8e57fd0d4d667221bdb48e4d349be797c2b4a0079826d72b3d934f45a20c976a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8e57fd0d4d667221bdb48e4d349be797c2b4a0079826d72b3d934f45a20c976a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8e57fd0d4d667221bdb48e4d349be797c2b4a0079826d72b3d934f45a20c976a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/drivers/nvme/nvme_transfer_command_spec.spl
mirror: doc/06_spec/unit/os/drivers/nvme/nvme_transfer_command_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/drivers/nvme/nvme_transfer_command_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/drivers/nvme/nvme_transfer_command_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/drivers/nvme/nvme_transfer_command_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds read and write commands without syscall or C bridge state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/drivers/nvme/nvme_transfer_command_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds namespace-aware read and write commands for assigned namespaces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/drivers/nvme/nvme_transfer_command_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects unsafe ranges before command submission' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
