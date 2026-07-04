# Simpleos Wine Process Vma Thunk Write Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_process_vma_thunk_write_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_process_vma_thunk_write_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_process_vma_thunk_write_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_process_vma_thunk_write_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Vma Thunk Write Specification

## Scenarios

### SimpleOS Wine VMA thunk writes

### REQ-027: bounded process VMA thunk patch window

#### should patch known thunk slots through a bounded process VMA write window

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_apply_known_kernel32_thunk_patches_in_vma(plan, wine_known_hello_exe_fixture_bytes(), 8)
val get_std_handle_offset = pe_rva_to_file_offset(result.patched_image, 0x2060)
val write_file_offset = pe_rva_to_file_offset(result.patched_image, 0x2068)
val exit_process_offset = pe_rva_to_file_offset(result.patched_image, 0x2070)
expect(result.ok).to_equal(true)
expect(result.patched_count).to_equal(3)
expect(_read_u64_le(result.patched_image, get_std_handle_offset)).to_equal(0x120000 + 5)
expect(_read_u64_le(result.patched_image, write_file_offset)).to_equal(0x120000 + 6)
expect(_read_u64_le(result.patched_image, exit_process_offset)).to_equal(0x120000 + 7)
expect(result.evidence).to_contain("process-image-mapped")
expect(result.evidence).to_contain("process-vma-write-window")
expect(result.evidence).to_contain("process-vma-write-enabled")
expect(result.evidence).to_contain("process-vma-rx-restored")
expect(result.evidence).to_contain("no-host-code-jump")
expect(result.status).to_equal("vma-thunk-patches-applied")
```

</details>

#### should reject VMA thunk writes before record planning passes

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_apply_known_kernel32_thunk_patches_in_vma(plan, wine_known_hello_exe_fixture_bytes(), 0)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("invalid-symbol-limit")
expect(result.patched_image.len()).to_equal(0)
expect(result.mapped_base).to_equal(0)
expect(result.mapped_size).to_equal(0)
expect(result.patched_count).to_equal(0)
expect(result.evidence).to_contain("vma-thunk-patches-blocked")
expect(result.evidence).to_contain("no-vma-thunk-written")
expect(result.evidence).to_contain("no-arbitrary-execution")
```

</details>

#### should require PEB/TEB VM byte-write readback before VMA thunk writes

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
val result = wine_process_apply_known_kernel32_thunk_patches_in_vma_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 8, vm_writes)

expect(result.ok).to_equal(true)
expect(result.patched_count).to_equal(3)
expect(result.evidence).to_contain("peb-teb-vm-writes-ready")
expect(result.evidence).to_contain("tls-callback-dispatch-empty")
expect(result.evidence).to_contain("process-vma-write-window")
expect(result.evidence).to_contain("no-host-code-jump")
expect(result.status).to_equal("vma-thunk-patches-applied")
```

</details>

#### should reject VM-gated VMA thunk writes before record planning passes without patched image

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_apply_known_kernel32_thunk_patches_in_vma_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 0, _ready_vm_writes())

expect(result.ok).to_equal(false)
expect(result.error).to_equal("invalid-symbol-limit")
expect(result.patched_image.len()).to_equal(0)
expect(result.mapped_base).to_equal(0)
expect(result.mapped_size).to_equal(0)
expect(result.patched_count).to_equal(0)
expect(result.evidence).to_contain("peb-teb-vm-writes-ready")
expect(result.evidence).to_contain("vma-thunk-patches-blocked")
expect(result.evidence).to_contain("no-vma-thunk-written")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("blocked")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_vma_thunk_write_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS Wine VMA thunk writes
- REQ-027: bounded process VMA thunk patch window

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
