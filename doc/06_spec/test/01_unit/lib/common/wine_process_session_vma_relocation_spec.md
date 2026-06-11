# Wine Process Session Vma Relocation Specification

> <details>

<!-- sdn-diagram:id=wine_process_session_vma_relocation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_process_session_vma_relocation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_process_session_vma_relocation_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_process_session_vma_relocation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Process Session Vma Relocation Specification

## Scenarios

### Wine process session VMA relocation application

#### applies a bounded DIR64 relocation through a process VMA write window

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val data = _known_hello_with_dir64_relocation()
val target_offset = pe_rva_to_file_offset(data, 0x2018)
val result = wine_process_apply_loader_relocations_in_vma(plan, data, 0x400000, 0x500000, "native-module-open tls-callback")
expect(result.ok).to_equal(true)
expect(result.mapped_base).to_equal(0x500000)
expect(result.relocation_count).to_equal(1)
expect(result.target_rva).to_equal(0x2018)
expect(_read_u64_le(result.patched_image, target_offset)).to_equal(0x502018)
expect(result.evidence).to_contain("relocation-dir64")
expect(result.evidence).to_contain("loader-relocations-vma-applied")
expect(result.evidence).to_contain("process-vma-write-enabled")
expect(result.evidence).to_contain("process-vma-rx-restored")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("loader-relocations-vma-applied")
```

</details>

#### applies loader relocations only after PEB/TEB VM byte-write readback

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val data = _known_hello_with_dir64_relocation()
val target_offset = pe_rva_to_file_offset(data, 0x2018)
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_process_apply_loader_relocations_in_vma_with_peb_teb_vm_writes(plan, data, 0x400000, 0x500000, "native-module-open tls-callback", vm_writes)

expect(result.ok).to_equal(true)
expect(result.status).to_equal("loader-relocations-vma-applied")
expect(_read_u64_le(result.patched_image, target_offset)).to_equal(0x502018)
expect(result.evidence).to_contain("peb-teb-vm-writes-ready")
expect(result.evidence).to_contain("VMWriteReadback:PEBTEBLayoutBytes")
expect(result.evidence).to_contain("loader-relocations-vma-applied")
```

</details>

#### blocks loader relocations when PEB/TEB VM byte writes are not ready

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val data = _known_hello_with_dir64_relocation()
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(wine_vm_process_space_new(10, 30, "pid fs ipc net capability"), bytes)
val result = wine_process_apply_loader_relocations_in_vma_with_peb_teb_vm_writes(plan, data, 0x400000, 0x500000, "native-module-open tls-callback", vm_writes)

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
| Source | `test/01_unit/lib/common/wine_process_session_vma_relocation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine process session VMA relocation application

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
