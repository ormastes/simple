# Freestanding Nvme Adapter Contract Specification

> <details>

<!-- sdn-diagram:id=freestanding_nvme_adapter_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=freestanding_nvme_adapter_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

freestanding_nvme_adapter_contract_spec -> std
freestanding_nvme_adapter_contract_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=freestanding_nvme_adapter_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Freestanding Nvme Adapter Contract Specification

## Scenarios

### freestanding pure NVMe adapter contract

#### accepts only complete pure-Simple transfer evidence before boot probing

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ready = _ready_transfer()
val contract = freestanding_nvme_adapter_contract(ready)
expect(contract.provider).to_equal("simple-driver")
expect(contract.pure_simple).to_equal(true)
expect(contract.block_probe_entry).to_equal("boot_fs_mount_from_device")
expect(contract.transfer_ready).to_equal(true)
expect(freestanding_nvme_adapter_ready(ready)).to_equal(true)
expect(freestanding_nvme_adapter_refusal_reason(ready)).to_equal("ready")
```

</details>

#### rejects C bridge and incomplete transfer evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bridge = nvme_transfer_evidence(
    "c-boot-bridge",
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    true,
    "user-space-driver",
    "raw-device-grant:tok=boot-nvme",
    "non-secure-resource-namespace",
    true,
    true
)
expect(freestanding_nvme_adapter_ready(bridge)).to_equal(false)
expect(freestanding_nvme_adapter_refusal_reason(bridge)).to_equal("nvme-transfer-provider-not-simple:c-boot-bridge")

val missing_sector = nvme_transfer_evidence(
    "simple-driver",
    true,
    true,
    true,
    true,
    true,
    false,
    true,
    true,
    true,
    "user-space-driver",
    "raw-device-grant:tok=boot-nvme",
    "non-secure-resource-namespace",
    true,
    true
)
expect(freestanding_nvme_adapter_ready(missing_sector)).to_equal(false)
expect(freestanding_nvme_adapter_refusal_reason(missing_sector)).to_equal("missing-nvme-sector-read")
```

</details>

#### publishes the provider and shared boot probe entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(freestanding_nvme_adapter_provider()).to_equal("simple-driver")
expect(freestanding_nvme_adapter_block_probe_entry()).to_equal("boot_fs_mount_from_device")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/boot/freestanding_nvme_adapter_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- freestanding pure NVMe adapter contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
