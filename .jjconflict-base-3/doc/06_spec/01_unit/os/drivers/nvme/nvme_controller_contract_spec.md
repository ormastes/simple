# Nvme Controller Contract Specification

> <details>

<!-- sdn-diagram:id=nvme_controller_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nvme_controller_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nvme_controller_contract_spec -> std
nvme_controller_contract_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nvme_controller_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvme Controller Contract Specification

## Scenarios

### NVMe controller contract

#### decodes q35 CAP fields without relying on the C bridge

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q35_cap = 0x4018200f0107ffu64
expect(nvme_cap_dstrd(q35_cap)).to_equal(0)
expect(nvme_cap_mq_entries(q35_cap)).to_equal(2048)
expect(nvme_cap_doorbell_stride_bytes(q35_cap)).to_equal(4)
expect(nvme_cap_timeout_ms(q35_cap)).to_equal(60000)

val regs = NvmeControllerRegs(
    cap: q35_cap,
    vs: 0x00010300u32,
    cc: 0u32,
    csts: 0u32
)
val facts = nvme_controller_facts(regs, 64u32)
expect(facts.valid).to_equal(true)
expect(facts.supports_required_queue).to_equal(true)
expect(facts.supports_nvm_command_set).to_equal(true)
expect(facts.fatal).to_equal(false)
expect(nvme_controller_refusal_reason(facts)).to_equal("ready")
```

</details>

#### builds the required controller enable value for NVM with 64B SQ and 16B CQ

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cc = nvme_controller_enable_cc()
expect((cc & 1u32) != 0u32).to_equal(true)
expect(((cc >> 16) & 0x0Fu32)).to_equal(6)
expect(((cc >> 20) & 0x0Fu32)).to_equal(4)
```

</details>

#### rejects fatal or undersized controllers instead of reporting fallback success

1. NvmeControllerRegs
   - Expected: fatal.valid is false
   - Expected: nvme_controller_refusal_reason(fatal) equals `nvme-controller-fatal`
2. NvmeControllerRegs
   - Expected: too_small.valid is false
   - Expected: nvme_controller_refusal_reason(too_small) equals `nvme-missing-nvm-command-set`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fatal = nvme_controller_facts(
    NvmeControllerRegs(cap: 0x4018200f0107ffu64, vs: 0x00010300u32, cc: 0u32, csts: 2u32),
    64u32
)
expect(fatal.valid).to_equal(false)
expect(nvme_controller_refusal_reason(fatal)).to_equal("nvme-controller-fatal")

val too_small = nvme_controller_facts(
    NvmeControllerRegs(cap: 0x0000000000000001u64, vs: 0x00010300u32, cc: 0u32, csts: 0u32),
    64u32
)
expect(too_small.valid).to_equal(false)
expect(nvme_controller_refusal_reason(too_small)).to_equal("nvme-missing-nvm-command-set")
```

</details>

#### derives namespace LBA size and refuses unsupported formats

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lbaf0_512 = 9u32 << 16
expect(nvme_lba_size_from_flbas_and_lbaf0(0u8, lbaf0_512)).to_equal(512)
val ns = nvme_namespace_facts(1u32, 8192u64, 0u8, lbaf0_512)
expect(ns.usable).to_equal(true)
expect(ns.formatted_lba_size).to_equal(512)

val missing = nvme_namespace_facts(1u32, 0u64, 0u8, lbaf0_512)
expect(missing.usable).to_equal(false)
expect(nvme_namespace_refusal_reason(missing)).to_equal("nvme-namespace-empty")
expect(nvme_namespace_refusal_reason(ns)).to_equal("ready")
expect(nvme_lba_size_from_flbas_and_lbaf0(1u8, lbaf0_512)).to_equal(0)
```

</details>

#### rejects namespace identify data that would otherwise fall back to fake 512 byte sectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_lbads = 8u32 << 16
val bad = nvme_namespace_facts(1u32, 8192u64, 0u8, bad_lbads)
expect(bad.usable).to_equal(false)
expect(nvme_namespace_refusal_reason(bad)).to_equal("nvme-namespace-invalid-lba-size")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/drivers/nvme/nvme_controller_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- NVMe controller contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
