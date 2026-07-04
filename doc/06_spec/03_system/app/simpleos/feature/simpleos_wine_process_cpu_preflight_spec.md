# Simpleos Wine Process Cpu Preflight Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_process_cpu_preflight_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_process_cpu_preflight_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_process_cpu_preflight_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_process_cpu_preflight_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Process Cpu Preflight Specification

## Scenarios

### SimpleOS Wine CPU dispatch VM preflight

### REQ-017: process CPU dispatch preflight

#### should require PEB/TEB VM byte-write readback before CPU dispatch preflight

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
val preflight = wine_process_cpu_dispatch_preflight_with_peb_teb_vm_writes(plan, wine_known_hello_exe_fixture_bytes(), 0x400000, 0x400000, "native-module-open tls-callback", 8, wine_cpu_execution_evidence_text(wine_cpu_execution_evidence_all_ready()), vm_writes)

expect(preflight.ok).to_equal(true)
expect(preflight.evidence).to_contain("peb-teb-vm-writes-ready")
expect(preflight.evidence).to_contain("process-image-mapped")
expect(preflight.evidence).to_contain("x86_64-dispatch")
expect(preflight.status).to_equal("cpu-preflight-ready")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_process_cpu_preflight_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS Wine CPU dispatch VM preflight
- REQ-017: process CPU dispatch preflight

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
