# Wine Ntdll Process Info Specification

> <details>

<!-- sdn-diagram:id=wine_ntdll_process_info_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_ntdll_process_info_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_ntdll_process_info_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_ntdll_process_info_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Ntdll Process Info Specification

## Scenarios

### Wine NTDLL process information bridge

#### executes bounded process and thread information queries

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_ntdll_execute_process_info(["NtQueryInformationProcess", "NtQueryInformationThread"], _classes(), wine_ntdll_process_thread_info_default())

expect(result.ok).to_equal(true)
expect(result.process_id).to_equal(10)
expect(result.thread_id).to_equal(20)
expect(result.peb_address).to_equal(0x7ffdf000)
expect(result.teb_address).to_equal(0x7ffde000)
expect(result.image_base).to_equal(0x400000)
expect(result.classes).to_equal("ProcessBasicInformation ProcessImageInformation ThreadBasicInformation")
expect(result.operations).to_equal("NtQueryInformationProcess NtQueryInformationThread")
```

</details>

#### keeps process information dispatch and classes bounded

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wrong_family = wine_ntdll_execute_process_info(["NtQueryInformationProcess", "NtCreateFile"], _classes(), wine_ntdll_process_thread_info_default())
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:NtCreateFile")

val wrong_class = wine_ntdll_execute_process_info(["NtQueryInformationProcess", "NtQueryInformationThread"], ["ThreadBasicInformation", "ProcessImageInformation", "ProcessBasicInformation"], wine_ntdll_process_thread_info_default())
expect(wrong_class.ok).to_equal(false)
expect(wrong_class.error).to_equal("ntdll-process-info-class-expected:ProcessBasicInformation")
```

</details>

#### rejects invalid process and thread facts

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val invalid = WineNtdllProcessThreadInfo(
    process_id: 10,
    thread_id: 0,
    peb_address: 0x7ffdf000,
    teb_address: 0x7ffde000,
    image_base: 0x400000,
    priority: 8
)
val result = wine_ntdll_execute_process_info(["NtQueryInformationProcess", "NtQueryInformationThread"], _classes(), invalid)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("NtQueryInformationThread:invalid-thread-id")
```

</details>

#### requires PEB/TEB initialization evidence before process-info handoff

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_ntdll_execute_process_info_with_peb_teb(["NtQueryInformationProcess", "NtQueryInformationThread"], _classes(), wine_peb_teb_init_default())
expect(result.ok).to_equal(true)
expect(result.peb_address).to_equal(0x7ffdf000)
expect(result.teb_address).to_equal(0x7ffde000)

val missing = WinePebTebInitEvidence(
    process_id: 10,
    thread_id: 20,
    peb_address: 0x7ffdf000,
    teb_address: 0x7ffde000,
    image_base: 0x400000,
    stack_base: 0x7ffef000,
    stack_limit: 0x7ffee000,
    tls_vector_address: 0x7ffdd000,
    process_parameters_address: 0x7ffdc000,
    evidence: "simpleos-process-identity simpleos-thread-identity"
)
val blocked = wine_ntdll_execute_process_info_with_peb_teb(["NtQueryInformationProcess", "NtQueryInformationThread"], _classes(), missing)
expect(blocked.ok).to_equal(false)
expect(blocked.error).to_equal("peb-teb:missing-simpleos-address-space")
```

</details>

#### requires PEB/TEB memory-write readiness before the write-aware process-info handoff

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val result = wine_ntdll_execute_process_info_with_peb_teb_writes(["NtQueryInformationProcess", "NtQueryInformationThread"], _classes(), init, writes)
expect(result.ok).to_equal(true)
expect(result.peb_address).to_equal(0x7ffdf000)
expect(result.teb_address).to_equal(0x7ffde000)
expect(result.operations).to_contain("PEBWrite")
expect(result.operations).to_contain("NtQueryInformationProcess NtQueryInformationThread")

val blocked_writes = wine_peb_teb_memory_write_gate(init, wine_vm_process_space_new(10, 30, "pid fs ipc net capability"))
val blocked = wine_ntdll_execute_process_info_with_peb_teb_writes(["NtQueryInformationProcess", "NtQueryInformationThread"], _classes(), init, blocked_writes)
expect(blocked.ok).to_equal(false)
expect(blocked.error).to_equal("peb-teb-write:peb-write:page-fault-unmapped")
```

</details>

#### requires PEB/TEB layout records before the layout-aware process-info handoff

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val result = wine_ntdll_execute_process_info_with_peb_teb_layout(["NtQueryInformationProcess", "NtQueryInformationThread"], _classes(), init, layout)
expect(result.ok).to_equal(true)
expect(result.peb_address).to_equal(0x7ffdf000)
expect(result.teb_address).to_equal(0x7ffde000)
expect(result.operations).to_contain("PEBTEBLayoutWritePlan")
expect(result.operations).to_contain("NtQueryInformationProcess NtQueryInformationThread")

val blocked_writes = wine_peb_teb_memory_write_gate(init, wine_vm_process_space_new(10, 30, "pid fs ipc net capability"))
val blocked_layout = wine_peb_teb_layout_write_plan(init, blocked_writes)
val blocked = wine_ntdll_execute_process_info_with_peb_teb_layout(["NtQueryInformationProcess", "NtQueryInformationThread"], _classes(), init, blocked_layout)
expect(blocked.ok).to_equal(false)
expect(blocked.error).to_equal("peb-teb-layout:write:peb-write:page-fault-unmapped")
```

</details>

#### requires PEB/TEB VM byte-write readback before the VM-aware process-info handoff

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_ntdll_execute_process_info_with_peb_teb_vm_writes(["NtQueryInformationProcess", "NtQueryInformationThread"], _classes(), init, vm_writes)
expect(result.ok).to_equal(true)
expect(result.peb_address).to_equal(0x7ffdf000)
expect(result.teb_address).to_equal(0x7ffde000)
expect(result.operations).to_contain("PEBTEBLayoutVMReadback")
expect(result.operations).to_contain("NtQueryInformationProcess NtQueryInformationThread")

val blocked_writes = wine_peb_teb_memory_write_gate(init, wine_vm_process_space_new(10, 30, "pid fs ipc net capability"))
val blocked_layout = wine_peb_teb_layout_write_plan(init, blocked_writes)
val blocked_bytes = wine_peb_teb_layout_byte_writes(blocked_layout)
val blocked_vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), blocked_bytes)
val blocked = wine_ntdll_execute_process_info_with_peb_teb_vm_writes(["NtQueryInformationProcess", "NtQueryInformationThread"], _classes(), init, blocked_vm_writes)
expect(blocked.ok).to_equal(false)
expect(blocked.error).to_equal("peb-teb-vm-write:bytes:layout:write:peb-write:page-fault-unmapped")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_ntdll_process_info_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine NTDLL process information bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
