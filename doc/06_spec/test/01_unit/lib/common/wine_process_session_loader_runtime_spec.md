# Wine Process Session Loader Runtime Specification

> <details>

<!-- sdn-diagram:id=wine_process_session_loader_runtime_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_process_session_loader_runtime_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_process_session_loader_runtime_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_process_session_loader_runtime_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Process Session Loader Runtime Specification

## Scenarios

### Wine process session loader runtime preflight

#### composes full-image handoff with relocation and TLS runtime evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_full_image_loader_runtime(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback")
expect(result.ok).to_equal(true)
expect(result.command).to_equal("game.exe")
expect(result.relocation_count).to_equal(0)
expect(result.tls_callback_count).to_equal(0)
expect(result.evidence).to_contain("full-image-loader-runtime-planned")
expect(result.evidence).to_contain("relocation-runtime-planned")
expect(result.evidence).to_contain("tls-runtime-planned")
expect(result.evidence).to_contain("relocation-no-entries")
expect(result.evidence).to_contain("tls-callback-table-empty")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("full-image-loader-runtime-planned")
```

</details>

#### rejects loader runtime preflight when TLS callback support is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_full_image_loader_runtime(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open")
expect(result.ok).to_equal(false)
expect(result.error).to_equal("tls:missing-api-tls-callback")
expect(result.relocation_count).to_equal(0)
expect(result.tls_callback_count).to_equal(0)
expect(result.evidence).to_contain("relocation-no-entries")
expect(result.evidence).to_contain("tls-directory")
expect(result.status).to_equal("rejected")
```

</details>

#### composes PEB/TEB VM byte-write readback before loader runtime evidence

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
val result = wine_process_plan_full_image_loader_runtime_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", vm_writes)

expect(result.ok).to_equal(true)
expect(result.status).to_equal("full-image-loader-runtime-planned")
expect(result.evidence).to_contain("peb-teb-vm-writes-ready")
expect(result.evidence).to_contain("VMWriteReadback:PEBTEBLayoutBytes")
expect(result.evidence).to_contain("full-image-loader-runtime-planned")
```

</details>

#### blocks loader runtime evidence when PEB/TEB VM byte writes are not ready

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
val result = wine_process_plan_full_image_loader_runtime_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", vm_writes)

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
| Source | `test/01_unit/lib/common/wine_process_session_loader_runtime_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine process session loader runtime preflight

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
