# Simpleos Wine Process Mapped Image Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_process_mapped_image_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_process_mapped_image_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_process_mapped_image_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_process_mapped_image_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Mapped Image Specification

## Scenarios

### SimpleOS Wine process mapped image

### REQ-026: mapped patched process image preflight

#### should map the patched image into a SimpleOS process VMA before dispatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val mapped = wine_process_map_known_console_image(plan, wine_known_hello_exe_fixture_bytes(), 8, wine_cpu_execution_evidence_text(wine_cpu_execution_evidence_all_ready()))
expect(mapped.ok).to_equal(true)
expect(mapped.mapped_base).to_equal(0x400000)
expect(mapped.mapped_size).to_equal(0x5000)
expect(mapped.evidence).to_contain("process-image-mapped")
expect(mapped.evidence).to_contain("os-process")
expect(mapped.evidence).to_contain("os-address-space")
expect(mapped.evidence).to_contain("os-vma")
expect(mapped.evidence).to_contain("image-map")
expect(mapped.evidence).to_contain("process-vma-write-window")
expect(mapped.evidence).to_contain("process-vma-rx-restored")
expect(mapped.evidence).to_contain("no-host-code-jump")
expect(mapped.status).to_equal("mapped-image-preflight-ready")
```

</details>

#### should reject mapped-image preflight before CPU evidence is complete

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val mapped = wine_process_map_known_console_image(plan, wine_known_hello_exe_fixture_bytes(), 8, "")
expect(mapped.ok).to_equal(false)
expect(mapped.error).to_equal("missing-thread-context")
expect(mapped.mapped_image.len()).to_equal(0)
expect(mapped.mapped_base).to_equal(0)
expect(mapped.mapped_size).to_equal(0)
expect(mapped.evidence).to_contain("mapped-image-preflight-blocked")
expect(mapped.evidence).to_contain("no-process-image-mapped")
expect(mapped.evidence).to_contain("no-arbitrary-execution")
expect(mapped.status).to_equal("blocked")
```

</details>

#### should require PEB/TEB VM byte-write readback before mapped-image preflight

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
val mapped = wine_process_map_known_console_image_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 8, wine_cpu_execution_evidence_text(wine_cpu_execution_evidence_all_ready()), vm_writes)

expect(mapped.ok).to_equal(true)
expect(mapped.mapped_base).to_equal(0x400000)
expect(mapped.evidence).to_contain("peb-teb-vm-writes-ready")
expect(mapped.evidence).to_contain("tls-callback-dispatch-empty")
expect(mapped.evidence).to_contain("process-image-mapped")
expect(mapped.evidence).to_contain("no-host-code-jump")
expect(mapped.status).to_equal("mapped-image-preflight-ready")
```

</details>

#### should reject VM-gated mapped-image preflight before CPU evidence is complete without mapped image

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val mapped = wine_process_map_known_console_image_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 8, "", _ready_vm_writes())

expect(mapped.ok).to_equal(false)
expect(mapped.error).to_equal("missing-thread-context")
expect(mapped.mapped_image.len()).to_equal(0)
expect(mapped.mapped_base).to_equal(0)
expect(mapped.mapped_size).to_equal(0)
expect(mapped.evidence).to_contain("mapped-image-preflight-blocked")
expect(mapped.evidence).to_contain("no-process-image-mapped")
expect(mapped.evidence).to_contain("no-arbitrary-execution")
expect(mapped.status).to_equal("blocked")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_mapped_image_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS Wine process mapped image
- REQ-026: mapped patched process image preflight

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
