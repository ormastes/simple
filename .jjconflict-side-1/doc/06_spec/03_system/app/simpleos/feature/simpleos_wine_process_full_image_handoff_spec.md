# Simpleos Wine Process Full Image Handoff Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_process_full_image_handoff_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_process_full_image_handoff_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_process_full_image_handoff_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_process_full_image_handoff_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Full Image Handoff Specification

## Scenarios

### SimpleOS Wine full image handoff

### REQ-028: arbitrary process image VM handoff

#### should map a validated full-Wine process image into an OS-backed VM without executing it

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val handoff = wine_process_prepare_full_image_handoff(plan, wine_known_hello_exe_fixture_bytes())
expect(handoff.ok).to_equal(true)
expect(handoff.mapped_base).to_equal(0x400000)
expect(handoff.mapped_size).to_equal(0x5000)
expect(handoff.entry_address).to_equal(0x402000)
expect(handoff.evidence).to_contain("arbitrary-process-image-handoff")
expect(handoff.evidence).to_contain("os-vma")
expect(handoff.evidence).to_contain("thread-stack")
expect(handoff.evidence).to_contain("guard-page")
expect(handoff.evidence).to_contain("no-host-code-jump")
expect(handoff.status).to_equal("full-image-handoff-ready")
```

</details>

#### should keep arbitrary image handoff behind full-Wine and PE validation gates

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val controlled = wine_process_session_plan(wine_process_session_request_new("hello.exe", [], "C:\\"), _hello_gates())
val unsupported = wine_process_prepare_full_image_handoff(controlled, wine_known_hello_exe_fixture_bytes())
expect(unsupported.ok).to_equal(false)
expect(unsupported.error).to_equal("unsupported-process-session")

val full = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val malformed = wine_process_prepare_full_image_handoff(full, _zero_bytes(0))
expect(malformed.ok).to_equal(false)
expect(malformed.error).to_equal("too-small")
```

</details>

#### should require PEB/TEB VM byte-write readback before full image handoff readiness

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
val handoff = wine_process_prepare_full_image_handoff_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), vm_writes)

expect(handoff.ok).to_equal(true)
expect(handoff.status).to_equal("full-image-handoff-ready")
expect(handoff.evidence).to_contain("peb-teb-vm-writes-ready")
expect(handoff.evidence).to_contain("VMWriteReadback:PEBTEBLayoutBytes")
expect(handoff.evidence).to_contain("arbitrary-process-image-handoff")
```

</details>

#### should block full image handoff before image mapping when PEB/TEB VM byte writes fail

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
val handoff = wine_process_prepare_full_image_handoff_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), vm_writes)

expect(handoff.ok).to_equal(false)
expect(handoff.error).to_equal("peb-teb-vm-write:vm-write:NtTib.StackBase:page-fault-unmapped")
expect(handoff.status).to_equal("rejected")
expect(handoff.mapped_base).to_equal(0)
expect(handoff.entry_address).to_equal(0)
expect(handoff.evidence).to_contain("full-image-handoff-blocked")
expect(handoff.evidence).to_contain("no-arbitrary-execution")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_full_image_handoff_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS Wine full image handoff
- REQ-028: arbitrary process image VM handoff

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
