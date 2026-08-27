# Simpleos Memory Leveling Specification

> Tests covering SimpleOS memory leveling policy.

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
#### exposes heterogeneous device profile with GPU NIC DMA and shadow state

- exposes heterogeneous device profile with GPU NIC DMA and shadow state


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exposes heterogeneous device profile with GPU NIC DMA and shadow state")
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

- keeps normal cold pages instead of swapping or migrating on baremetal
   - Expected: decision.action equals `MEMORY_ACTION_KEEP`
   - Expected: decision.reason equals `baremetal-static-no-migration`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps normal cold pages instead of swapping or migrating on baremetal")
val decision = memory_leveling_decide(memory_profile_baremetal_static(), memory_page_cpu_cold(10))
expect(decision.action).to_equal(MEMORY_ACTION_KEEP)
expect(decision.reason).to_equal("baremetal-static-no-migration")
```

</details>

#### REQ-003 device pinned safety

#### rejects DMA pinned pages before swap decisions

- rejects DMA pinned pages before swap decisions
   - Expected: decision.action equals `MEMORY_ACTION_REJECT`
   - Expected: decision.reason equals `dma-pinned-not-swappable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects DMA pinned pages before swap decisions")
val decision = memory_leveling_decide(memory_profile_heterogeneous_device(), memory_page_dma_pinned(20))
expect(decision.action).to_equal(MEMORY_ACTION_REJECT)
expect(decision.reason).to_equal("dma-pinned-not-swappable")
```

</details>

#### rejects NIC registered pages before swap decisions

- rejects NIC registered pages before swap decisions
   - Expected: decision.action equals `MEMORY_ACTION_REJECT`
   - Expected: decision.reason equals `nic-registered-not-swappable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects NIC registered pages before swap decisions")
val decision = memory_leveling_decide(memory_profile_heterogeneous_device(), memory_page_nic_registered(21))
expect(decision.action).to_equal(MEMORY_ACTION_REJECT)
expect(decision.reason).to_equal("nic-registered-not-swappable")
```

</details>

#### rejects GPU resident pages until coherence proof exists

- rejects GPU resident pages until coherence proof exists
   - Expected: decision.action equals `MEMORY_ACTION_REJECT`
   - Expected: decision.reason equals `gpu-resident-needs-coherence`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects GPU resident pages until coherence proof exists")
val decision = memory_leveling_decide(memory_profile_heterogeneous_device(), memory_page_gpu_resident(22))
expect(decision.action).to_equal(MEMORY_ACTION_REJECT)
expect(decision.reason).to_equal("gpu-resident-needs-coherence")
```

</details>

#### REQ-004 default swap and demotion

#### demotes cold CPU pages under the default SimpleOS profile

- demotes cold CPU pages under the default SimpleOS profile
   - Expected: decision.action equals `MEMORY_ACTION_DEMOTE_COLD`
   - Expected: decision.reason equals `cold-cpu-page-to-swap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("demotes cold CPU pages under the default SimpleOS profile")
val decision = memory_leveling_decide(memory_profile_simpleos_default(), memory_page_cpu_cold(30))
expect(decision.action).to_equal(MEMORY_ACTION_DEMOTE_COLD)
expect(decision.reason).to_equal("cold-cpu-page-to-swap")
```

</details>

#### keeps hot CPU pages under the default SimpleOS profile

- keeps hot CPU pages under the default SimpleOS profile
   - Expected: decision.action equals `MEMORY_ACTION_KEEP`
   - Expected: decision.reason equals `cpu-page-kept`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps hot CPU pages under the default SimpleOS profile")
val decision = memory_leveling_decide(memory_profile_simpleos_default(), memory_page_cpu_hot(31))
expect(decision.action).to_equal(MEMORY_ACTION_KEEP)
expect(decision.reason).to_equal("cpu-page-kept")
```

</details>

#### REQ-005 fail closed heterogeneous model

#### rejects unknown externally visible page states

- rejects unknown externally visible page states


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects unknown externally visible page states")
val line = movement_decision_line(memory_profile_heterogeneous_device(), memory_page_unknown(40))
expect(line).to_contain("action=reject")
expect(line).to_contain("reason=external-visible-unknown-owner")
```

</details>

#### REQ-006 Simple language model boundary

#### treats device handles as non movable external memory

- treats device handles as non movable external memory
   - Expected: simple_memory_intent_movable(intent) is false
   - Expected: decision.action equals `MEMORY_ACTION_REJECT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("treats device handles as non movable external memory")
val intent = simple_memory_device_gpu()
val decision = memory_leveling_decide(memory_profile_heterogeneous_device(), memory_page_from_simple_intent(41, intent))
expect(simple_memory_intent_movable(intent)).to_equal(false)
expect(decision.action).to_equal(MEMORY_ACTION_REJECT)
```

</details>

#### REQ-006A Simple language intent API

#### keeps shared hot CPU intent movable and in CPU memory

- keeps shared hot CPU intent movable and in CPU memory
   - Expected: simple_memory_intent_movable(intent) is true
   - Expected: decision.action equals `MEMORY_ACTION_KEEP`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps shared hot CPU intent movable and in CPU memory")
val intent = simple_memory_shared_cpu_hot()
val page = memory_page_from_simple_intent(50, intent)
val decision = memory_leveling_decide(memory_profile_simpleos_default(), page)
expect(simple_memory_intent_movable(intent)).to_equal(true)
expect(simple_memory_intent_summary(intent)).to_contain("owner=shared")
expect(decision.action).to_equal(MEMORY_ACTION_KEEP)
```

</details>

#### demotes isolated cold CPU intent through the OS policy

- demotes isolated cold CPU intent through the OS policy
   - Expected: decision.action equals `MEMORY_ACTION_DEMOTE_COLD`
   - Expected: decision.reason equals `cold-cpu-page-to-swap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("demotes isolated cold CPU intent through the OS policy")
val page = memory_page_from_simple_intent(51, simple_memory_iso_cpu_cold())
val decision = memory_leveling_decide(memory_profile_simpleos_default(), page)
expect(decision.action).to_equal(MEMORY_ACTION_DEMOTE_COLD)
expect(decision.reason).to_equal("cold-cpu-page-to-swap")
```

</details>

#### maps language GPU NIC and DMA intents to fail-closed OS pages

- maps language GPU NIC and DMA intents to fail-closed OS pages
   - Expected: gpu_decision.reason equals `gpu-resident-needs-coherence`
   - Expected: nic_decision.reason equals `nic-registered-not-swappable`
   - Expected: dma_decision.reason equals `dma-pinned-not-swappable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps language GPU NIC and DMA intents to fail-closed OS pages")
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

- labels this implementation as hardware gated evidence
   - Expected: memory_leveling_evidence_scope() equals `hardware-gated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("labels this implementation as hardware gated evidence")
expect(memory_leveling_evidence_scope()).to_equal("hardware-gated")
```

</details>

#### REQ-008 real hardware target gate

#### requires real evidence before accepting hardware decisions

- requires real evidence before accepting hardware decisions
   - Expected: decision.action equals `MEMORY_ACTION_REJECT`
   - Expected: decision.reason equals `real-hardware-evidence-required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires real evidence before accepting hardware decisions")
val decision = memory_leveling_real_hardware_decide(memory_profile_heterogeneous_device(), simple_memory_device_gpu())
expect(decision.action).to_equal(MEMORY_ACTION_REJECT)
expect(decision.reason).to_equal("real-hardware-evidence-required")
```

</details>

#### applies CPU policy to real x86 ARM and RISC-V targets

- applies CPU policy to real x86 ARM and RISC-V targets
   - Expected: x86.action equals `MEMORY_ACTION_KEEP`
   - Expected: arm.action equals `MEMORY_ACTION_KEEP`
   - Expected: riscv.action equals `MEMORY_ACTION_KEEP`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("applies CPU policy to real x86 ARM and RISC-V targets")
val x86 = memory_leveling_real_hardware_decide(memory_profile_simpleos_default(), simple_memory_x86_cpu_real())
val arm = memory_leveling_real_hardware_decide(memory_profile_simpleos_default(), simple_memory_arm_cpu_real())
val riscv = memory_leveling_real_hardware_decide(memory_profile_simpleos_default(), simple_memory_riscv_cpu_real())
expect(x86.action).to_equal(MEMORY_ACTION_KEEP)
expect(arm.action).to_equal(MEMORY_ACTION_KEEP)
expect(riscv.action).to_equal(MEMORY_ACTION_KEEP)
```

</details>

#### keeps real Vulkan Metal CUDA and RDMA device memory fail closed

- keeps real Vulkan Metal CUDA and RDMA device memory fail closed
   - Expected: vulkan.reason equals `vulkan-gpu-memory-pinned`
   - Expected: metal.reason equals `metal-gpu-memory-pinned`
   - Expected: cuda.reason equals `cuda-gpu-memory-pinned`
   - Expected: rdma.reason equals `rdma-registered-not-swappable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps real Vulkan Metal CUDA and RDMA device memory fail closed")
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

- marks real hardware intents separately from model intents
   - Expected: simple_memory_intent_real_hardware(simple_memory_x86_cpu_real()) is true
   - Expected: simple_memory_intent_real_hardware(simple_memory_device_gpu()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("marks real hardware intents separately from model intents")
expect(simple_memory_intent_real_hardware(simple_memory_x86_cpu_real())).to_equal(true)
expect(simple_memory_intent_real_hardware(simple_memory_device_gpu())).to_equal(false)
```

</details>

#### REQ-009 Vulkan and CUDA readback backed pinning

#### pins real Vulkan and CUDA memory when readback proof exists

- pins real Vulkan and CUDA memory when readback proof exists
   - Expected: vulkan.action equals `MEMORY_ACTION_PIN_DEVICE`
   - Expected: vulkan.reason equals `vulkan-readback-backed-pinned`
   - Expected: cuda.action equals `MEMORY_ACTION_PIN_DEVICE`
   - Expected: cuda.reason equals `cuda-readback-backed-pinned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pins real Vulkan and CUDA memory when readback proof exists")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS memory leveling policy.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-001`
- `REQ-002`
- `REQ-003`
- `REQ-004`
- `REQ-005`
- `REQ-006`
- `REQ-006A`
- `REQ-007`
- `REQ-008`
- `REQ-009`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `db8debe2b2b155e7adf80bc5f47a5578c456fc2ea385830778fe93afb004befa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `db8debe2b2b155e7adf80bc5f47a5578c456fc2ea385830778fe93afb004befa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `db8debe2b2b155e7adf80bc5f47a5578c456fc2ea385830778fe93afb004befa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/os/simpleos_memory_leveling_spec.spl
mirror: doc/06_spec/03_system/os/simpleos_memory_leveling_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=90 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=85; blocker cap makes effective=49
doc/06_spec/03_system/os/simpleos_memory_leveling_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/simpleos_memory_leveling_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/simpleos_memory_leveling_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 10 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/os/simpleos_memory_leveling_spec.spl:59:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'exposes baremetal static profile as no swap and no migration' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/os/simpleos_memory_leveling_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes heterogeneous device profile with GPU NIC DMA and shadow state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos_memory_leveling_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps normal cold pages instead of swapping or migrating on baremetal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos_memory_leveling_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects DMA pinned pages before swap decisions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
