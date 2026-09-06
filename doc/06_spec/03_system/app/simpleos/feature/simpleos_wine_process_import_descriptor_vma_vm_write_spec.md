# Simpleos Wine Process Import Descriptor Vma Vm Write Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_process_import_descriptor_vma_vm_write_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_process_import_descriptor_vma_vm_write_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_process_import_descriptor_vma_vm_write_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_process_import_descriptor_vma_vm_write_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Import Descriptor Vma Vm Write Specification

## Scenarios

### SimpleOS Wine process import descriptor VMA VM writes

#### should block descriptor thunk VMA patching without patched image when PEB/TEB VM byte writes fail

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, wine_vm_process_space_new(10, 30, "pid fs ipc net capability"))
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_process_apply_import_descriptor_thunk_patches_in_vma_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 4, 8, vm_writes)

expect(result.ok).to_equal(false)
expect(result.error).to_equal("peb-teb-vm-write:bytes:layout:write:peb-write:page-fault-unmapped")
expect(result.patched_image.len()).to_equal(0)
expect(result.mapped_base).to_equal(0)
expect(result.mapped_size).to_equal(0)
expect(result.patched_count).to_equal(0)
expect(result.evidence).to_contain("import-descriptor-vma-thunk-patches-blocked")
expect(result.evidence).to_contain("no-vma-thunk-written")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("rejected")
```

</details>

#### should block descriptor thunk VMA patching without patched image when descriptor planning rejects

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_apply_import_descriptor_thunk_patches_in_vma_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 0, 8, _ready_vm_writes())

expect(result.ok).to_equal(false)
expect(result.error).to_equal("invalid-import-descriptor-limit")
expect(result.patched_image.len()).to_equal(0)
expect(result.mapped_base).to_equal(0)
expect(result.mapped_size).to_equal(0)
expect(result.patched_count).to_equal(0)
expect(result.evidence).to_contain("peb-teb-vm-writes-ready")
expect(result.evidence).to_contain("import-descriptor-vma-thunk-patches-blocked")
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
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_import_descriptor_vma_vm_write_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS Wine process import descriptor VMA VM writes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
