# Wine Process Session Thunk Load Bind Specification

> <details>

<!-- sdn-diagram:id=wine_process_session_thunk_load_bind_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_process_session_thunk_load_bind_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_process_session_thunk_load_bind_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_process_session_thunk_load_bind_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Process Session Thunk Load Bind Specification

## Scenarios

### Wine process session thunk load binding

#### requires module-load evidence before planning import thunk patches

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_import_thunk_patches(plan, wine_known_hello_exe_fixture_bytes(), 8)
expect(result.ok).to_equal(true)
expect(result.dll_name).to_equal("kernel32.dll")
expect(result.patch_count).to_equal(3)
expect(result.evidence).to_contain("import-module-loaded")
expect(result.evidence).to_contain("import-module-loader-sequence")
expect(result.evidence).to_contain("import-thunk-records-planned")
expect(result.evidence).to_contain("import-thunk-records-bounded")
expect(result.evidence).to_contain("import-thunks-bound")
expect(result.status).to_equal("thunk-patch-planned")
```

</details>

#### propagates load-and-bind rejection before thunk planning

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_plan_import_thunk_patches(plan, wine_known_hello_exe_fixture_bytes(), 0)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("invalid-symbol-limit")
expect(result.status).to_equal("blocked")
```

</details>

#### plans import thunk patches only after PEB/TEB VM byte-write readback

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_process_plan_import_thunk_patches_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 8, vm_writes)

expect(result.ok).to_equal(true)
expect(result.patch_count).to_equal(3)
expect(result.evidence).to_contain("peb-teb-vm-writes-ready")
expect(result.evidence).to_contain("tls-callback-dispatch-empty")
expect(result.evidence).to_contain("import-thunks-bound")
expect(result.status).to_equal("thunk-patch-planned")
```

</details>

#### blocks import thunk planning when PEB/TEB VM byte writes are not ready

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
val result = wine_process_plan_import_thunk_patches_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 8, vm_writes)

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
| Source | `test/01_unit/lib/common/wine_process_session_thunk_load_bind_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine process session thunk load binding

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
