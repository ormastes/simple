# Wine Process Session Known Console Dispatch Specification

> <details>

<!-- sdn-diagram:id=wine_process_session_known_console_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_process_session_known_console_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_process_session_known_console_dispatch_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_process_session_known_console_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Process Session Known Console Dispatch Specification

## Scenarios

### Wine process session known-console dispatch

#### plans bounded known-console dispatch after CPU preflight

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_known_console_dispatch(plan, wine_known_hello_exe_fixture_bytes(), 8, wine_cpu_execution_evidence_text(wine_cpu_execution_evidence_all_ready()))
expect(result.ok).to_equal(true)
expect(result.command).to_equal("game.exe")
expect(result.instruction_sequence).to_equal("xor-rcx-rcx call-rip-indirect lea-rdx-rip-rel32 call-rip-indirect xor-ecx-ecx call-rip-indirect")
expect(result.instruction_count).to_equal(6)
expect(result.call_sequence).to_equal("GetStdHandle WriteFile ExitProcess")
expect(result.call_count).to_equal(3)
expect(result.status).to_equal("dispatch-planned")
```

</details>

#### plans known-console dispatch only after PEB/TEB VM byte-write readback

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_process_plan_known_console_dispatch_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 8, wine_cpu_execution_evidence_text(wine_cpu_execution_evidence_all_ready()), vm_writes)

expect(result.ok).to_equal(true)
expect(result.instruction_count).to_equal(6)
expect(result.call_sequence).to_equal("GetStdHandle WriteFile ExitProcess")
expect(result.call_count).to_equal(3)
expect(result.status).to_equal("dispatch-planned")
```

</details>

#### blocks known-console dispatch when PEB/TEB VM byte writes are not ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(wine_vm_process_space_new(10, 30, "pid fs ipc net capability"), bytes)
val result = wine_process_plan_known_console_dispatch_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 8, wine_cpu_execution_evidence_text(wine_cpu_execution_evidence_all_ready()), vm_writes)

expect(result.ok).to_equal(false)
expect(result.error).to_equal("peb-teb-vm-write:vm-write:NtTib.StackBase:page-fault-unmapped")
expect(result.status).to_equal("rejected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_process_session_known_console_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine process session known-console dispatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
