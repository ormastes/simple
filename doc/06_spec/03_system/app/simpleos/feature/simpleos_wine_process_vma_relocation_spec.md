# Simpleos Wine Process Vma Relocation Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_process_vma_relocation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_process_vma_relocation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_process_vma_relocation_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_process_vma_relocation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Vma Relocation Specification

## Scenarios

### SimpleOS Wine VMA relocation application

### REQ-036: loader-owned relocation mutation through process VMA

#### should apply a bounded relocation in the mapped process image without executing PE code

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val data = _known_hello_with_dir64_relocation()
val target_offset = pe_rva_to_file_offset(data, 0x2018)
val result = wine_process_apply_loader_relocations_in_vma(plan, data, 0x400000, 0x500000, "native-module-open tls-callback")
expect(result.ok).to_equal(true)
expect(result.relocation_count).to_equal(1)
expect(result.target_rva).to_equal(0x2018)
expect(_read_u64_le(result.patched_image, target_offset)).to_equal(0x502018)
expect(result.evidence).to_contain("loader-relocations-vma-applied")
expect(result.evidence).to_contain("process-vma-rx-restored")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("loader-relocations-vma-applied")
```

</details>

#### should require PEB/TEB VM byte-write readback before loader relocation mutation

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
expect(result.evidence).to_contain("no-arbitrary-execution")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_vma_relocation_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS Wine VMA relocation application
- REQ-036: loader-owned relocation mutation through process VMA

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
