# Wine Process Session Full Image Handoff Specification

> <details>

<!-- sdn-diagram:id=wine_process_session_full_image_handoff_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_process_session_full_image_handoff_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_process_session_full_image_handoff_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_process_session_full_image_handoff_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Process Session Full Image Handoff Specification

## Scenarios

### Wine process session full image handoff

#### maps a validated full-Wine PE image and stack into an OS-backed process VM

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_prepare_full_image_handoff(plan, wine_known_hello_exe_fixture_bytes())
expect(result.ok).to_equal(true)
expect(result.command).to_equal("game.exe")
expect(result.mapped_base).to_equal(0x400000)
expect(result.mapped_size).to_equal(0x5000)
expect(result.entry_address).to_equal(0x402000)
expect(result.evidence).to_contain("full-image-validated")
expect(result.evidence).to_contain("arbitrary-process-image-handoff")
expect(result.evidence).to_contain("os-process")
expect(result.evidence).to_contain("os-address-space")
expect(result.evidence).to_contain("os-vma")
expect(result.evidence).to_contain("image-map")
expect(result.evidence).to_contain("thread-stack")
expect(result.evidence).to_contain("guard-page")
expect(result.evidence).to_contain("no-host-code-jump")
expect(result.status).to_equal("full-image-handoff-ready")
```

</details>

#### keeps full-image handoff behind full-Wine plan and image validation gates

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val controlled = wine_process_session_plan(wine_process_session_request_new("hello.exe", [], "C:\\"), _hello_gates())
val blocked = wine_process_prepare_full_image_handoff(controlled, wine_known_hello_exe_fixture_bytes())
expect(blocked.ok).to_equal(false)
expect(blocked.error).to_equal("unsupported-process-session")
expect(blocked.status).to_equal("blocked")

val full = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val malformed = wine_process_prepare_full_image_handoff(full, _zero_bytes(0))
expect(malformed.ok).to_equal(false)
expect(malformed.error).to_equal("too-small")
expect(malformed.status).to_equal("rejected")
```

</details>

#### requires PEB/TEB VM byte-write readback before full image handoff readiness

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
val result = wine_process_prepare_full_image_handoff_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), vm_writes)

expect(result.ok).to_equal(true)
expect(result.status).to_equal("full-image-handoff-ready")
expect(result.evidence).to_contain("peb-teb-vm-writes-ready")
expect(result.evidence).to_contain("VMWriteReadback:PEBTEBLayoutBytes")
expect(result.evidence).to_contain("arbitrary-process-image-handoff")
```

</details>

#### blocks full image handoff readiness when PEB/TEB VM byte writes are not ready

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
val result = wine_process_prepare_full_image_handoff_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), vm_writes)

expect(result.ok).to_equal(false)
expect(result.error).to_equal("peb-teb-vm-write:vm-write:NtTib.StackBase:page-fault-unmapped")
expect(result.status).to_equal("rejected")
expect(result.mapped_base).to_equal(0)
expect(result.entry_address).to_equal(0)
expect(result.evidence).to_contain("full-image-handoff-blocked")
expect(result.evidence).to_contain("no-arbitrary-execution")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_process_session_full_image_handoff_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine process session full image handoff

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
