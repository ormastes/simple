# Wine Process Session Mapped Image Specification

> <details>

<!-- sdn-diagram:id=wine_process_session_mapped_image_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_process_session_mapped_image_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_process_session_mapped_image_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_process_session_mapped_image_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Process Session Mapped Image Specification

## Scenarios

### Wine process session mapped image preflight

#### maps the patched known-console image into a bounded process address space

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_map_known_console_image(plan, wine_known_hello_exe_fixture_bytes(), 8, wine_cpu_execution_evidence_text(wine_cpu_execution_evidence_all_ready()))
expect(result.ok).to_equal(true)
expect(result.command).to_equal("game.exe")
expect(result.mapped_base).to_equal(0x400000)
expect(result.mapped_size).to_equal(0x5000)
expect(result.evidence).to_contain("process-image-mapped")
expect(result.evidence).to_contain("os-process")
expect(result.evidence).to_contain("os-address-space")
expect(result.evidence).to_contain("os-vma")
expect(result.evidence).to_contain("image-map")
expect(result.evidence).to_contain("process-vma-write-window")
expect(result.evidence).to_contain("process-vma-rx-restored")
expect(result.evidence).to_contain("no-host-code-jump")
expect(result.status).to_equal("mapped-image-preflight-ready")
```

</details>

#### blocks mapped-image preflight before non-import CPU evidence is complete

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_map_known_console_image(plan, wine_known_hello_exe_fixture_bytes(), 8, "")
expect(result.ok).to_equal(false)
expect(result.error).to_equal("missing-thread-context")
expect(result.mapped_image.len()).to_equal(0)
expect(result.mapped_base).to_equal(0)
expect(result.mapped_size).to_equal(0)
expect(result.evidence).to_contain("mapped-image-preflight-blocked")
expect(result.evidence).to_contain("no-process-image-mapped")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("blocked")
```

</details>

#### maps the known-console image only after PEB/TEB VM byte-write readback

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_process_map_known_console_image_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 8, wine_cpu_execution_evidence_text(wine_cpu_execution_evidence_all_ready()), vm_writes)

expect(result.ok).to_equal(true)
expect(result.mapped_base).to_equal(0x400000)
expect(result.evidence).to_contain("peb-teb-vm-writes-ready")
expect(result.evidence).to_contain("tls-callback-dispatch-empty")
expect(result.evidence).to_contain("process-image-mapped")
expect(result.evidence).to_contain("no-host-code-jump")
expect(result.status).to_equal("mapped-image-preflight-ready")
```

</details>

#### blocks mapped-image preflight when PEB/TEB VM byte writes are not ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(wine_vm_process_space_new(10, 30, "pid fs ipc net capability"), bytes)
val result = wine_process_map_known_console_image_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 8, wine_cpu_execution_evidence_text(wine_cpu_execution_evidence_all_ready()), vm_writes)

expect(result.ok).to_equal(false)
expect(result.error).to_equal("peb-teb-vm-write:vm-write:NtTib.StackBase:page-fault-unmapped")
expect(result.mapped_image.len()).to_equal(0)
expect(result.mapped_base).to_equal(0)
expect(result.mapped_size).to_equal(0)
expect(result.status).to_equal("rejected")
expect(result.evidence).to_contain("full-image-handoff-blocked")
```

</details>

#### blocks VM-gated mapped-image preflight without mapped image before CPU evidence is complete

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_map_known_console_image_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 8, "", _ready_vm_writes())

expect(result.ok).to_equal(false)
expect(result.error).to_equal("missing-thread-context")
expect(result.mapped_image.len()).to_equal(0)
expect(result.mapped_base).to_equal(0)
expect(result.mapped_size).to_equal(0)
expect(result.evidence).to_contain("mapped-image-preflight-blocked")
expect(result.evidence).to_contain("no-process-image-mapped")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("blocked")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_process_session_mapped_image_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine process session mapped image preflight

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
