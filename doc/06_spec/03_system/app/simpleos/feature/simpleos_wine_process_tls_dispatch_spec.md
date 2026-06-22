# Simpleos Wine Process Tls Dispatch Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_process_tls_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_process_tls_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_process_tls_dispatch_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_process_tls_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Tls Dispatch Specification

## Scenarios

### SimpleOS Wine TLS callback dispatch

### REQ-037: loader-owned TLS callback dispatch record

#### should record a mapped TLS callback dispatch after relocation without executing PE code

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = wine_process_session_plan(wine_process_session_request_new("game.exe", [], "C:\\Games"), _full_gates())
val result = wine_process_record_tls_callback_dispatch(plan, _known_hello_with_tls_callback(), 0x400000, 0x400000, "native-module-open tls-callback")
expect(result.ok).to_equal(true)
expect(result.callback_count).to_equal(1)
expect(result.first_callback_rva).to_equal(0x2000)
expect(result.dispatch_count).to_equal(1)
expect(result.evidence).to_contain("tls-callback-target-mapped")
expect(result.evidence).to_contain("loader-tls-callback-dispatch-owned")
expect(result.evidence).to_contain("no-arbitrary-execution")
expect(result.status).to_equal("tls-callback-dispatch-recorded")
```

</details>

#### should require PEB/TEB VM byte-write readback before TLS callback dispatch record

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
val result = wine_process_record_tls_callback_dispatch_with_peb_teb_vm_writes(plan, _known_hello_with_tls_callback(), 0x400000, 0x400000, "native-module-open tls-callback", vm_writes)

expect(result.ok).to_equal(true)
expect(result.status).to_equal("tls-callback-dispatch-recorded")
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
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_tls_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS Wine TLS callback dispatch
- REQ-037: loader-owned TLS callback dispatch record

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
