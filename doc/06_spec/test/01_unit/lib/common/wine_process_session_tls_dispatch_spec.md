# Wine Process Session Tls Dispatch Specification

> <details>

<!-- sdn-diagram:id=wine_process_session_tls_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_process_session_tls_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_process_session_tls_dispatch_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_process_session_tls_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Process Session Tls Dispatch Specification

## Scenarios

### Wine process session TLS callback dispatch

#### records a loader-owned TLS callback dispatch after relocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_record_tls_callback_dispatch(plan, _known_hello_with_tls_callback(), 0x400000, 0x400000, "native-module-open tls-callback")
expect(result.ok).to_equal(true)
expect(result.mapped_base).to_equal(0x400000)
expect(result.callback_count).to_equal(1)
expect(result.first_callback_rva).to_equal(0x2000)
expect(result.dispatch_count).to_equal(1)
expect(result.evidence).to_contain("tls-callback-table")
expect(result.evidence).to_contain("tls-callback-target-mapped")
expect(result.evidence).to_contain("tls-callback-dispatch-recorded")
expect(result.evidence).to_contain("loader-tls-callback-dispatch-owned")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("tls-callback-dispatch-recorded")
```

</details>

#### accepts an empty TLS callback table without dispatching

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_record_tls_callback_dispatch(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback")
expect(result.ok).to_equal(true)
expect(result.callback_count).to_equal(0)
expect(result.dispatch_count).to_equal(0)
expect(result.evidence).to_contain("tls-callback-table-empty")
expect(result.evidence).to_contain("tls-callback-dispatch-empty")
expect(result.status).to_equal("tls-callback-dispatch-empty")
```

</details>

#### records TLS callback dispatch only after PEB/TEB VM byte-write readback

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
val result = wine_process_record_tls_callback_dispatch_with_peb_teb_vm_writes(plan, _known_hello_with_tls_callback(), 0x400000, 0x400000, "native-module-open tls-callback", vm_writes)

expect(result.ok).to_equal(true)
expect(result.status).to_equal("tls-callback-dispatch-recorded")
expect(result.evidence).to_contain("peb-teb-vm-writes-ready")
expect(result.evidence).to_contain("VMWriteReadback:PEBTEBLayoutBytes")
expect(result.evidence).to_contain("tls-callback-dispatch-recorded")
```

</details>

#### blocks TLS callback dispatch when PEB/TEB VM byte writes are not ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(wine_vm_process_space_new(10, 30, "pid fs ipc net capability"), bytes)
val result = wine_process_record_tls_callback_dispatch_with_peb_teb_vm_writes(plan, _known_hello_with_tls_callback(), 0x400000, 0x400000, "native-module-open tls-callback", vm_writes)

expect(result.ok).to_equal(false)
expect(result.error).to_equal("peb-teb-vm-write:vm-write:NtTib.StackBase:page-fault-unmapped")
expect(result.status).to_equal("rejected")
expect(result.evidence).to_contain("full-image-handoff-blocked")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_process_session_tls_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine process session TLS callback dispatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
