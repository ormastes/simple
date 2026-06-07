# Wine Dll View Dllmain Handoff Specification

> <details>

<!-- sdn-diagram:id=wine_dll_view_dllmain_handoff_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_dll_view_dllmain_handoff_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_dll_view_dllmain_handoff_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_dll_view_dllmain_handoff_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Dll View Dllmain Handoff Specification

## Scenarios

### wine dll view DllMain handoff

#### prepares DllMain handoff after TLS planning without executing DLL code

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _dll_with_import_relocation_tls()
val files = [wine_dll_probe_file("\\KnownDlls\\game.dll", data)]
val result = wine_dll_prepare_file_view_dllmain_handoff("game.dll", "C:\\Games", "C:\\Users\\Player", [], ["game.dll"], files, data, 0x400000, 0x500000, 77, 78, "pid fs ipc net capability", 2, 4, "native-module-open tls-callback", false)
expect(result.ok).to_equal(true)
expect(result.status).to_equal("dllmain-handoff-ready")
expect(result.entrypoint_rva).to_equal(0x2100)
expect(result.entrypoint_address).to_equal(0x502100)
expect(result.callback_count).to_equal(1)
expect(result.dispatch_count).to_equal(1)
expect(result.evidence).to_contain("dllmain-process-attach-planned")
expect(result.evidence).to_contain("tls-before-dllmain")
expect(result.evidence).to_contain("no-dllmain-executed")
```

</details>

#### blocks attempts to execute DllMain from the retained view handoff

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _dll_with_import_relocation_tls()
val files = [wine_dll_probe_file("\\KnownDlls\\game.dll", data)]
val result = wine_dll_prepare_file_view_dllmain_handoff("game.dll", "C:\\Games", "C:\\Users\\Player", [], ["game.dll"], files, data, 0x400000, 0x500000, 77, 78, "pid fs ipc net capability", 2, 4, "native-module-open tls-callback", true)
expect(result.ok).to_equal(true)
expect(result.evidence).to_contain("dllmain-execution-requested")
expect(result.evidence).to_contain("dllmain-exec-dispatched")
expect(result.status).to_equal("dllmain-exec-dispatched")
```

</details>

#### requires PEB/TEB loader-lock startup before retained DllMain handoff

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _dll_with_import_relocation_tls()
val files = [wine_dll_probe_file("\\KnownDlls\\game.dll", data)]
val handoff = wine_dll_prepare_file_view_dllmain_handoff("game.dll", "C:\\Games", "C:\\Users\\Player", [], ["game.dll"], files, data, 0x400000, 0x500000, 77, 78, "pid fs ipc net capability", 2, 4, "native-module-open tls-callback", false)
expect(handoff.ok).to_equal(true)
val result = wine_dllmain_handoff_require_peb_teb_loader_lock(handoff, true, "ready", "PEB TEB TLS ProcessParameters LoaderLock")

expect(result.ok).to_equal(true)
expect(result.status).to_equal("dllmain-handoff-ready")
expect(result.evidence).to_contain("peb-teb-loader-lock-ready")
expect(result.evidence).to_contain("PEB TEB TLS ProcessParameters LoaderLock")
expect(result.evidence).to_contain("dllmain-process-attach-planned")
```

</details>

#### blocks retained DllMain handoff when PEB/TEB loader-lock ordering is invalid

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _dll_with_import_relocation_tls()
val files = [wine_dll_probe_file("\\KnownDlls\\game.dll", data)]
val handoff = wine_dll_prepare_file_view_dllmain_handoff("game.dll", "C:\\Games", "C:\\Users\\Player", [], ["game.dll"], files, data, 0x400000, 0x500000, 77, 78, "pid fs ipc net capability", 2, 4, "native-module-open tls-callback", false)
expect(handoff.ok).to_equal(true)
val result = wine_dllmain_handoff_require_peb_teb_loader_lock(handoff, false, "loader-lock:kernel32-critical-section-sequence-expected:InitializeCriticalSection", "")

expect(result.ok).to_equal(false)
expect(result.error).to_equal("peb-teb-loader-lock:loader-lock:kernel32-critical-section-sequence-expected:InitializeCriticalSection")
expect(result.evidence).to_contain("dllmain-handoff-blocked")
expect(result.status).to_equal("rejected")
```

</details>

#### requires PEB/TEB writes before retained DllMain handoff

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _dll_with_import_relocation_tls()
val files = [wine_dll_probe_file("\\KnownDlls\\game.dll", data)]
val handoff = wine_dll_prepare_file_view_dllmain_handoff("game.dll", "C:\\Games", "C:\\Users\\Player", [], ["game.dll"], files, data, 0x400000, 0x500000, 77, 78, "pid fs ipc net capability", 2, 4, "native-module-open tls-callback", false)
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val result = wine_dllmain_handoff_require_peb_teb_writes(handoff, true, "ready", "PEB TEB TLS ProcessParameters LoaderLock", writes)

expect(result.ok).to_equal(true)
expect(result.status).to_equal("dllmain-handoff-ready")
expect(result.evidence).to_contain("peb-teb-writes-ready")
expect(result.evidence).to_contain("PEBWrite")
expect(result.evidence).to_contain("dllmain-process-attach-planned")
```

</details>

#### blocks retained DllMain handoff when PEB/TEB writes are not mapped

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _dll_with_import_relocation_tls()
val files = [wine_dll_probe_file("\\KnownDlls\\game.dll", data)]
val handoff = wine_dll_prepare_file_view_dllmain_handoff("game.dll", "C:\\Games", "C:\\Users\\Player", [], ["game.dll"], files, data, 0x400000, 0x500000, 77, 78, "pid fs ipc net capability", 2, 4, "native-module-open tls-callback", false)
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, wine_vm_process_space_new(10, 30, "pid fs ipc net capability"))
val result = wine_dllmain_handoff_require_peb_teb_writes(handoff, true, "ready", "PEB TEB TLS ProcessParameters LoaderLock", writes)

expect(result.ok).to_equal(false)
expect(result.error).to_equal("peb-teb-write:peb-write:page-fault-unmapped")
expect(result.evidence).to_contain("dllmain-handoff-blocked")
expect(result.status).to_equal("rejected")
```

</details>

#### requires PEB/TEB layout records before retained DllMain handoff

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _dll_with_import_relocation_tls()
val files = [wine_dll_probe_file("\\KnownDlls\\game.dll", data)]
val handoff = wine_dll_prepare_file_view_dllmain_handoff("game.dll", "C:\\Games", "C:\\Users\\Player", [], ["game.dll"], files, data, 0x400000, 0x500000, 77, 78, "pid fs ipc net capability", 2, 4, "native-module-open tls-callback", false)
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val result = wine_dllmain_handoff_require_peb_teb_layout(handoff, true, "ready", "PEB TEB TLS ProcessParameters LoaderLock", layout)

expect(result.ok).to_equal(true)
expect(result.status).to_equal("dllmain-handoff-ready")
expect(result.evidence).to_contain("peb-teb-layout-ready")
expect(result.evidence).to_contain("PEBTEBLayoutWritePlan")
expect(result.evidence).to_contain("dllmain-process-attach-planned")
```

</details>

#### blocks retained DllMain handoff when PEB/TEB layout records are not ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _dll_with_import_relocation_tls()
val files = [wine_dll_probe_file("\\KnownDlls\\game.dll", data)]
val handoff = wine_dll_prepare_file_view_dllmain_handoff("game.dll", "C:\\Games", "C:\\Users\\Player", [], ["game.dll"], files, data, 0x400000, 0x500000, 77, 78, "pid fs ipc net capability", 2, 4, "native-module-open tls-callback", false)
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, wine_vm_process_space_new(10, 30, "pid fs ipc net capability"))
val layout = wine_peb_teb_layout_write_plan(init, writes)
val result = wine_dllmain_handoff_require_peb_teb_layout(handoff, true, "ready", "PEB TEB TLS ProcessParameters LoaderLock", layout)

expect(result.ok).to_equal(false)
expect(result.error).to_equal("peb-teb-layout:write:peb-write:page-fault-unmapped")
expect(result.evidence).to_contain("dllmain-handoff-blocked")
expect(result.status).to_equal("rejected")
```

</details>

#### requires PEB/TEB VM byte-write readback before retained DllMain handoff

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _dll_with_import_relocation_tls()
val files = [wine_dll_probe_file("\\KnownDlls\\game.dll", data)]
val handoff = wine_dll_prepare_file_view_dllmain_handoff("game.dll", "C:\\Games", "C:\\Users\\Player", [], ["game.dll"], files, data, 0x400000, 0x500000, 77, 78, "pid fs ipc net capability", 2, 4, "native-module-open tls-callback", false)
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_dllmain_handoff_require_peb_teb_vm_writes(handoff, true, "ready", "PEB TEB TLS ProcessParameters LoaderLock", vm_writes)

expect(result.ok).to_equal(true)
expect(result.status).to_equal("dllmain-handoff-ready")
expect(result.evidence).to_contain("peb-teb-vm-writes-ready")
expect(result.evidence).to_contain("PEBTEBLayoutVMReadback")
expect(result.evidence).to_contain("dllmain-process-attach-planned")
```

</details>

#### blocks retained DllMain handoff when PEB/TEB VM byte writes are not ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _dll_with_import_relocation_tls()
val files = [wine_dll_probe_file("\\KnownDlls\\game.dll", data)]
val handoff = wine_dll_prepare_file_view_dllmain_handoff("game.dll", "C:\\Games", "C:\\Users\\Player", [], ["game.dll"], files, data, 0x400000, 0x500000, 77, 78, "pid fs ipc net capability", 2, 4, "native-module-open tls-callback", false)
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, wine_vm_process_space_new(10, 30, "pid fs ipc net capability"))
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_dllmain_handoff_require_peb_teb_vm_writes(handoff, true, "ready", "PEB TEB TLS ProcessParameters LoaderLock", vm_writes)

expect(result.ok).to_equal(false)
expect(result.error).to_equal("peb-teb-vm-write:bytes:layout:write:peb-write:page-fault-unmapped")
expect(result.mapped_base).to_equal(0)
expect(result.mapped_size).to_equal(0)
expect(result.entrypoint_address).to_equal(0)
expect(result.callback_count).to_equal(0)
expect(result.dispatch_count).to_equal(0)
expect(result.evidence).to_contain("dllmain-handoff-blocked")
expect(result.evidence).to_contain("no-dllmain-executed")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("rejected")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_dll_view_dllmain_handoff_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wine dll view DllMain handoff

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
