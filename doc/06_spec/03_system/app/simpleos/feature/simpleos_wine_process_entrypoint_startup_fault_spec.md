# Simpleos Wine Process Entrypoint Startup Fault Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_process_entrypoint_startup_fault_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_process_entrypoint_startup_fault_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_process_entrypoint_startup_fault_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_process_entrypoint_startup_fault_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Entrypoint Startup Fault Specification

## Scenarios

### REQ-045: process imported entrypoint startup fault rollback

#### records SEH rollback after import-bound entrypoint handoff while keeping PE code non-executing

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val fault = WineVmFault(process_id: 77, thread_id: 12, address: 0x402000, access: "execute", policy: "deliver-seh")
val result = wine_process_record_imported_entrypoint_startup_fault(plan, _known_hello_with_second_import_descriptor(), 4, 8, fault)
expect(result.ok).to_equal(true)
expect(result.status).to_equal("imported-entrypoint-startup-fault-rollback-recorded")
expect(result.rollback_count).to_equal(2)
expect(result.evidence).to_contain("imported-entrypoint-handoff-ready")
expect(result.evidence).to_contain("seh-dispatch-recorded")
expect(result.evidence).to_contain("no-arbitrary-execution")
```

</details>

#### requires PEB/TEB VM byte-write readback before import-bound entrypoint rollback

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fault = WineVmFault(process_id: 77, thread_id: 12, address: 0x402000, access: "execute", policy: "deliver-seh")
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_process_record_imported_entrypoint_handoff_startup_fault_with_peb_teb_vm_writes(_ready_handoff(), fault, vm_writes)

expect(result.ok).to_equal(true)
expect(result.status).to_equal("imported-entrypoint-startup-fault-rollback-recorded")
expect(result.evidence).to_contain("peb-teb-vm-writes-ready")
expect(result.evidence).to_contain("VMWriteReadback:PEBTEBLayoutBytes")
expect(result.evidence).to_contain("no-arbitrary-execution")
```

</details>

#### blocks import-bound entrypoint rollback without carrying mapped state when PEB/TEB VM byte writes fail

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fault = WineVmFault(process_id: 77, thread_id: 12, address: 0x402000, access: "execute", policy: "deliver-seh")
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(wine_vm_process_space_new(10, 30, "pid fs ipc net capability"), bytes)
val result = wine_process_record_imported_entrypoint_handoff_startup_fault_with_peb_teb_vm_writes(_ready_handoff(), fault, vm_writes)

expect(result.ok).to_equal(false)
expect(result.error).to_equal("imported-entrypoint-handoff:peb-teb-vm-write:vm-write:NtTib.StackBase:page-fault-unmapped")
expect(result.mapped_base).to_equal(0)
expect(result.mapped_size).to_equal(0)
expect(result.entry_address).to_equal(0)
expect(result.module_count).to_equal(0)
expect(result.rollback_count).to_equal(0)
expect(result.evidence).to_contain("imported-entrypoint-handoff-blocked")
expect(result.evidence).to_contain("process-entrypoint-startup-fault-blocked")
expect(result.evidence).to_contain("no-arbitrary-execution")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_entrypoint_startup_fault_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- REQ-045: process imported entrypoint startup fault rollback

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
