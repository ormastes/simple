# Simpleos Memory Leveling Specification

> <details>

<!-- sdn-diagram:id=simpleos_memory_leveling_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_memory_leveling_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_memory_leveling_spec -> std
simpleos_memory_leveling_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_memory_leveling_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Memory Leveling Specification

## Scenarios

### SimpleOS memory leveling policy

#### REQ-001 profile footprint

#### exposes baremetal static profile as no swap and no migration

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = memory_profile_baremetal_static()
val summary = memory_profile_summary(profile)
expect(summary).to_contain("profile=baremetal_static")
expect(summary).to_contain("swap=off")
expect(summary).to_contain("migration=off")
expect(summary).to_contain("gpu=off")
expect(summary).to_contain("nic=off")
expect(summary).to_contain("dma_pin=on")
```

</details>

#### exposes heterogeneous device profile with GPU NIC DMA and shadow state

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile = memory_profile_heterogeneous_device()
val summary = profile_summary_line(profile)
expect(summary).to_contain("profile=heterogeneous_device")
expect(summary).to_contain("swap=on")
expect(summary).to_contain("migration=on")
expect(summary).to_contain("gpu=on")
expect(summary).to_contain("nic=on")
expect(summary).to_contain("shadow=on")
```

</details>

#### REQ-002 baremetal simplicity

#### keeps normal cold pages instead of swapping or migrating on baremetal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decision = memory_leveling_decide(memory_profile_baremetal_static(), memory_page_cpu_cold(10))
expect(decision.action).to_equal(MEMORY_ACTION_KEEP)
expect(decision.reason).to_equal("baremetal-static-no-migration")
```

</details>

#### REQ-003 device pinned safety

#### rejects DMA pinned pages before swap decisions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decision = memory_leveling_decide(memory_profile_heterogeneous_device(), memory_page_dma_pinned(20))
expect(decision.action).to_equal(MEMORY_ACTION_REJECT)
expect(decision.reason).to_equal("dma-pinned-not-swappable")
```

</details>

#### rejects NIC registered pages before swap decisions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decision = memory_leveling_decide(memory_profile_heterogeneous_device(), memory_page_nic_registered(21))
expect(decision.action).to_equal(MEMORY_ACTION_REJECT)
expect(decision.reason).to_equal("nic-registered-not-swappable")
```

</details>

#### rejects GPU resident pages until coherence proof exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decision = memory_leveling_decide(memory_profile_heterogeneous_device(), memory_page_gpu_resident(22))
expect(decision.action).to_equal(MEMORY_ACTION_REJECT)
expect(decision.reason).to_equal("gpu-resident-needs-coherence")
```

</details>

#### REQ-004 default swap and demotion

#### demotes cold CPU pages under the default SimpleOS profile

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decision = memory_leveling_decide(memory_profile_simpleos_default(), memory_page_cpu_cold(30))
expect(decision.action).to_equal(MEMORY_ACTION_DEMOTE_COLD)
expect(decision.reason).to_equal("cold-cpu-page-to-swap")
```

</details>

#### keeps hot CPU pages under the default SimpleOS profile

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decision = memory_leveling_decide(memory_profile_simpleos_default(), memory_page_cpu_hot(31))
expect(decision.action).to_equal(MEMORY_ACTION_KEEP)
expect(decision.reason).to_equal("cpu-page-kept")
```

</details>

#### REQ-005 fail closed heterogeneous model

#### rejects unknown externally visible page states

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = movement_decision_line(memory_profile_heterogeneous_device(), memory_page_unknown(40))
expect(line).to_contain("action=reject")
expect(line).to_contain("reason=external-visible-unknown-owner")
```

</details>

#### REQ-006 Simple language model boundary

#### treats device handles as non movable external memory

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val intent = simple_memory_device_gpu()
val decision = memory_leveling_decide(memory_profile_heterogeneous_device(), memory_page_from_simple_intent(41, intent))
expect(simple_memory_intent_movable(intent)).to_equal(false)
expect(decision.action).to_equal(MEMORY_ACTION_REJECT)
```

</details>

#### REQ-006A Simple language intent API

#### keeps shared hot CPU intent movable and in CPU memory

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val intent = simple_memory_shared_cpu_hot()
val page = memory_page_from_simple_intent(50, intent)
val decision = memory_leveling_decide(memory_profile_simpleos_default(), page)
expect(simple_memory_intent_movable(intent)).to_equal(true)
expect(simple_memory_intent_summary(intent)).to_contain("owner=shared")
expect(decision.action).to_equal(MEMORY_ACTION_KEEP)
```

</details>

#### demotes isolated cold CPU intent through the OS policy

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = memory_page_from_simple_intent(51, simple_memory_iso_cpu_cold())
val decision = memory_leveling_decide(memory_profile_simpleos_default(), page)
expect(decision.action).to_equal(MEMORY_ACTION_DEMOTE_COLD)
expect(decision.reason).to_equal("cold-cpu-page-to-swap")
```

</details>

#### maps language GPU NIC and DMA intents to fail-closed OS pages

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gpu_decision = memory_leveling_decide(memory_profile_heterogeneous_device(), memory_page_from_simple_intent(52, simple_memory_device_gpu()))
val nic_decision = memory_leveling_decide(memory_profile_heterogeneous_device(), memory_page_from_simple_intent(53, simple_memory_network_registered()))
val dma_decision = memory_leveling_decide(memory_profile_heterogeneous_device(), memory_page_from_simple_intent(54, simple_memory_dma_pinned()))
expect(gpu_decision.reason).to_equal("gpu-resident-needs-coherence")
expect(nic_decision.reason).to_equal("nic-registered-not-swappable")
expect(dma_decision.reason).to_equal("dma-pinned-not-swappable")
```

</details>

#### REQ-007 no unsupported hardware completion claim

#### labels this implementation as hardware gated evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(memory_leveling_evidence_scope()).to_equal("hardware-gated")
```

</details>

#### REQ-008 real hardware target gate

#### requires real evidence before accepting hardware decisions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val decision = memory_leveling_real_hardware_decide(memory_profile_heterogeneous_device(), simple_memory_device_gpu())
expect(decision.action).to_equal(MEMORY_ACTION_REJECT)
expect(decision.reason).to_equal("real-hardware-evidence-required")
```

</details>

#### applies CPU policy to real x86 ARM and RISC-V targets

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x86 = memory_leveling_real_hardware_decide(memory_profile_simpleos_default(), simple_memory_x86_cpu_real())
val arm = memory_leveling_real_hardware_decide(memory_profile_simpleos_default(), simple_memory_arm_cpu_real())
val riscv = memory_leveling_real_hardware_decide(memory_profile_simpleos_default(), simple_memory_riscv_cpu_real())
expect(x86.action).to_equal(MEMORY_ACTION_KEEP)
expect(arm.action).to_equal(MEMORY_ACTION_KEEP)
expect(riscv.action).to_equal(MEMORY_ACTION_KEEP)
```

</details>

#### keeps real Vulkan Metal CUDA and RDMA device memory fail closed

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vulkan = memory_leveling_real_hardware_decide(memory_profile_heterogeneous_device(), simple_memory_vulkan_gpu_real())
val metal = memory_leveling_real_hardware_decide(memory_profile_heterogeneous_device(), simple_memory_metal_gpu_real())
val cuda = memory_leveling_real_hardware_decide(memory_profile_heterogeneous_device(), simple_memory_cuda_gpu_real())
val rdma = memory_leveling_real_hardware_decide(memory_profile_heterogeneous_device(), simple_memory_rdma_nic_real())
expect(vulkan.reason).to_equal("vulkan-gpu-memory-pinned")
expect(metal.reason).to_equal("metal-gpu-memory-pinned")
expect(cuda.reason).to_equal("cuda-gpu-memory-pinned")
expect(rdma.reason).to_equal("rdma-registered-not-swappable")
```

</details>

#### marks real hardware intents separately from model intents

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(simple_memory_intent_real_hardware(simple_memory_x86_cpu_real())).to_equal(true)
expect(simple_memory_intent_real_hardware(simple_memory_device_gpu())).to_equal(false)
```

</details>

#### REQ-009 Vulkan and CUDA readback backed pinning

#### pins real Vulkan and CUDA memory when readback proof exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vulkan = memory_leveling_real_hardware_decide(memory_profile_heterogeneous_device(), simple_memory_vulkan_gpu_readback_real())
val cuda = memory_leveling_real_hardware_decide(memory_profile_heterogeneous_device(), simple_memory_cuda_gpu_readback_real())
expect(vulkan.action).to_equal(MEMORY_ACTION_PIN_DEVICE)
expect(vulkan.reason).to_equal("vulkan-readback-backed-pinned")
expect(cuda.action).to_equal(MEMORY_ACTION_PIN_DEVICE)
expect(cuda.reason).to_equal("cuda-readback-backed-pinned")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_memory_leveling_spec.spl` |
| Updated | 2026-07-08 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS memory leveling policy

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
