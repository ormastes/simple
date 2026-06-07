# Qemu Arm64 Smf Parity Specification

> 1. Build a role-2 ARM64 SMF envelope for the GUI hot-call symbol

<!-- sdn-diagram:id=qemu_arm64_smf_parity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=qemu_arm64_smf_parity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

qemu_arm64_smf_parity_spec -> std
qemu_arm64_smf_parity_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=qemu_arm64_smf_parity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Qemu Arm64 Smf Parity Specification

## Scenarios

### QEMU ARM64 SMF parity contract

#### accepts the same role-2 arm64 SMF artifact reaching the pure GUI adapter

1. Build a role-2 ARM64 SMF envelope for the GUI hot-call symbol
2. Convert the SMF bytes into the release artifact contract
3. Dispatch a representative pure GUI command batch
4. gui pointer event
5. gui pointer event
6. gui pointer event
7. gui key event
8. Verify the same artifact contract reaches the QEMU framebuffer adapter path
   - Expected: parity.status equals `contract-pass`
   - Expected: parity.adapter equals `simpleos-framebuffer-virtio`
   - Expected: parity.same_artifact_contract is true
   - Expected: parity.live_qemu is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val smf = gui_smf_wrap_native_library([0xCFu8, 0xFAu8, 0xEDu8, 0xFEu8, 1u8], 3u8)
val contract = gui_smf_artifact_contract("build/gui/pure_gui_hot.smf", smf, "gui_dynlib_hot_probe_tick")
val batch = gui_dispatch_events([
    gui_pointer_event("pointer_move", "button.save", 12, 24),
    gui_pointer_event("pointer_down", "button.save", 12, 24),
    gui_pointer_event("pointer_up", "button.save", 12, 24),
    gui_key_event("input.name", "A", "a")
], 0)
val parity = gui_qemu_arm64_smf_parity(contract, batch)
expect(parity.status).to_equal("contract-pass")
expect(parity.adapter).to_equal("simpleos-framebuffer-virtio")
expect(parity.same_artifact_contract).to_equal(true)
expect(parity.live_qemu).to_equal(false)
val row = gui_qemu_arm64_smf_parity_row(parity)
expect(row).to_contain("GUI_QEMU_ARM64_SMF_PARITY")
expect(row).to_contain("status=contract-pass")
expect(row).to_contain("arch=3")
expect(row).to_contain("symbol=gui_dynlib_hot_probe_tick")
expect(row).to_contain("adapter=simpleos-framebuffer-virtio")
expect(row).to_contain("live_qemu=false")
```

</details>

#### fails closed for non-arm64 or empty command-batch parity claims

1. Build a non-ARM64 SMF envelope
2. Pair the wrong-architecture artifact with an empty GUI batch
   - Expected: parity.status equals `contract-fail`
   - Expected: parity.same_artifact_contract is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val smf = gui_smf_wrap_native_library([0x7Fu8, 0x45u8, 0x4Cu8, 0x46u8, 1u8], 1u8)
val contract = gui_smf_artifact_contract("build/gui/pure_gui_hot.smf", smf, "gui_dynlib_hot_probe_tick")
val parity = gui_qemu_arm64_smf_parity(contract, gui_empty_batch())
expect(parity.status).to_equal("contract-fail")
expect(parity.same_artifact_contract).to_equal(false)
expect(gui_qemu_arm64_smf_parity_row(parity)).to_contain("reason=missing-arm64-smf-or-command-batch")
```

</details>

#### fails closed when the SMF artifact targets the wrong hot-call symbol

1. Build an ARM64 SMF envelope for a non-release symbol
2. Dispatch a non-empty GUI command batch that would otherwise satisfy adapter parity
3. gui pointer event
4. Reject the parity row because the artifact targets the wrong hot-call symbol
   - Expected: parity.status equals `contract-fail`
   - Expected: parity.same_artifact_contract is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val smf = gui_smf_wrap_native_library([0xCFu8, 0xFAu8, 0xEDu8, 0xFEu8, 1u8], 3u8)
val contract = gui_smf_artifact_contract("build/gui/pure_gui_hot.smf", smf, "other_symbol")
val batch = gui_dispatch_events([
    gui_pointer_event("pointer_move", "button.save", 12, 24)
], 0)
val parity = gui_qemu_arm64_smf_parity(contract, batch)
expect(parity.status).to_equal("contract-fail")
expect(parity.same_artifact_contract).to_equal(false)
val row = gui_qemu_arm64_smf_parity_row(parity)
expect(row).to_contain("symbol=other_symbol")
expect(row).to_contain("reason=missing-arm64-smf-or-command-batch")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/gui_perf/qemu_arm64_smf_parity_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- QEMU ARM64 SMF parity contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
