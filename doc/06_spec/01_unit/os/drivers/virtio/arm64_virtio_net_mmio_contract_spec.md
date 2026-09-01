# Arm64 Virtio Net Mmio Contract Specification

> Tests covering ARM64 VirtIO-MMIO NIC transport contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Arm64 Virtio Net Mmio Contract Specification

## Scenarios

### ARM64 VirtIO-MMIO NIC transport contract

#### negotiates modern features and publishes both bounded queues

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- negotiates modern features and publishes both bounded queues


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negotiates modern features and publishes both bounded queues")
val source = file_read("examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c")
expect(source).to_contain("ARM64_VIRTIO_NET_DEVICE_ID 1U")
expect(source).to_contain("candidate[VMMIO_VERSION / 4U] == 2U")
expect(source).to_contain("(features_high & 1U) == 0U")
expect(source).to_contain("VIRTIO_STATUS_FEATURES_OK")
expect(source).to_contain("mmio[VMMIO_STATUS / 4U] & VIRTIO_STATUS_FEATURES_OK")
expect(source).to_contain("ARM64_NET_QUEUE_SIZE 8U")
expect(source).to_contain("arm64_net_setup_queue(mmio, 0U")
expect(source).to_contain("arm64_net_setup_queue(mmio, 1U")
expect(source).to_contain("VMMIO_QUEUE_DESC_LOW")
expect(source).to_contain("VMMIO_QUEUE_READY / 4U] = 1U")
```

</details>

#### owns RX write descriptors and bounded TX completion

- owns RX write descriptors and bounded TX completion


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("owns RX write descriptors and bounded TX completion")
val source = file_read("examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c")
expect(source).to_contain("g_arm64_net_rx_desc[i].flags = VIRTQ_DESC_F_WRITE")
expect(source).to_contain("ARM64_NET_POLL_LIMIT 1000000U")
expect(source).to_contain("g_arm64_net_tx_used.idx != g_arm64_net_tx_last_used")
expect(source).to_contain("arm64_clean_dcache_range")
expect(source).to_contain("arm64_invalidate_dcache_range")
expect(source).to_contain("VMMIO_INTERRUPT_ACK")
expect(source).to_contain("g_arm64_net_rx_avail.idx++")
expect(source).to_contain("static void arm64_net_repost_rx")
expect(source).to_contain("g_arm64_net_rx_posted[i] = 1U")
expect(source).to_contain("!g_arm64_net_rx_posted[elem.id]")
expect(source).to_contain("g_arm64_net_rx_posted[elem.id] = 0U")
expect(source).to_contain("mmio[VMMIO_STATUS / 4U] |= VIRTIO_STATUS_FAILED")
expect(source).to_contain("g_arm64_net_ready = 0U")
expect(source).to_contain("arm64_net_repost_rx((uint16_t)elem.id)")
```

</details>

#### wires ARM transport into the existing driver and netstack owner

- wires ARM transport into the existing driver and netstack owner


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wires ARM transport into the existing driver and netstack owner")
val driver = file_read("src/os/drivers/virtio/_VirtioNet/driver_operations.spl")
val init = file_read("src/os/services/netstack/netstack_init.spl")
expect(driver).to_contain("me init_arm64_mmio()")
expect(driver).to_contain("VIRTIO_NET_TRANSPORT_ARM64_MMIO")
expect(driver).to_contain("rt_arm64_virtio_net_send")
expect(driver).to_contain("rt_arm64_virtio_net_recv")
expect(init).to_contain("fn net_boot_init_arm64_mmio()")
expect(init).to_contain("NetstackService.new(g_net_driver)")
```

</details>

#### routes direct sockets with bounded reusable descriptor ownership

- routes direct sockets with bounded reusable descriptor ownership


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes direct sockets with bounded reusable descriptor ownership")
val init = file_read("src/os/services/netstack/netstack_init.spl")
expect(init).to_contain("candidate < 100 + ARM64_NET_FD_CAPACITY")
expect(init).to_contain("g_arm64_net_fd_map.remove(i)")
expect(init).to_contain("return -4096")
expect(init).to_contain("net_tcp_close(internal as i64)")
expect(init).to_contain("val internal = net_tcp_accept")
expect(init).to_contain("svc.poll_once()")
expect(init).to_contain("user_copyin_bytes")
expect(init).to_contain("user_copyout_bytes")
expect(init).to_contain("owner_task: u64")
expect(init).to_contain("owner_task == spl_shim_current_task_id()")
expect(init).to_contain("pub fn net_arm64_task_teardown")
```

</details>

#### denies ambient ring3 device and DMA authority

- denies ambient ring3 device and DMA authority


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("denies ambient ring3 device and DMA authority")
val source = file_read("examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c")
expect(source).to_contain("case 80: /* DevEnumerate */ return -1")
expect(source).to_contain("case 81: /* DevGetInfo */ return -1")
expect(source).to_contain("case 82: /* DeviceGrant */ return -1")
expect(source).to_contain("case 83: /* MapBar */ return -1")
expect(source).to_contain("case 84: /* AllocDma */ return -1")
expect(source).to_contain("case 85: /* FreeDma */ return -1")
expect(source).to_contain("case 86: /* DeviceWaitIrq */ return -1")
expect(source).to_contain("case 87: /* DeviceAckIrq */ return -1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/drivers/virtio/arm64_virtio_net_mmio_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ARM64 VirtIO-MMIO NIC transport contract.
- ARM64 VirtIO-MMIO NIC transport contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `10a71a2a56b6befcb38e37fcdacb9bfb698f9a3df62f129c9f0b67f4da1ce35b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `10a71a2a56b6befcb38e37fcdacb9bfb698f9a3df62f129c9f0b67f4da1ce35b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `10a71a2a56b6befcb38e37fcdacb9bfb698f9a3df62f129c9f0b67f4da1ce35b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/drivers/virtio/arm64_virtio_net_mmio_contract_spec.spl
mirror: doc/06_spec/01_unit/os/drivers/virtio/arm64_virtio_net_mmio_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/drivers/virtio/arm64_virtio_net_mmio_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/drivers/virtio/arm64_virtio_net_mmio_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/drivers/virtio/arm64_virtio_net_mmio_contract_spec.spl:11:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'negotiates modern features and publishes both bounded queues' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/drivers/virtio/arm64_virtio_net_mmio_contract_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'owns RX write descriptors and bounded TX completion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/drivers/virtio/arm64_virtio_net_mmio_contract_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wires ARM transport into the existing driver and netstack owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
