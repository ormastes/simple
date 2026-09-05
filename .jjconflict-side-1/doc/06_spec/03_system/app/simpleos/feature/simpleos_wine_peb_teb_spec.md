# Simpleos Wine Peb Teb Specification

> <details>

<!-- sdn-diagram:id=simpleos_wine_peb_teb_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wine_peb_teb_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wine_peb_teb_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wine_peb_teb_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Peb Teb Specification

## Scenarios

### SimpleOS Wine PEB/TEB startup evidence

### REQ-018: bounded known-console process dispatch plan

#### should validate PEB/TEB/TLS evidence before NTDLL process-info handoff

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init = wine_peb_teb_init_gate(wine_peb_teb_init_default())
expect(init.ok).to_equal(true)
expect(init.operations).to_equal("PEB TEB TLS ProcessParameters")

val result = wine_ntdll_execute_process_info_with_peb_teb(["NtQueryInformationProcess", "NtQueryInformationThread"], _classes(), wine_peb_teb_init_default())
expect(result.ok).to_equal(true)
expect(result.classes).to_equal("ProcessBasicInformation ProcessImageInformation ThreadBasicInformation")
expect(result.peb_address).to_equal(0x7ffdf000)
expect(result.teb_address).to_equal(0x7ffde000)
```

</details>

#### should require loader-lock sequencing around PEB/TEB startup evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_peb_teb_init_with_loader_lock(wine_peb_teb_init_default(), _loader_lock_symbols(), wine_kernel32_critical_section_table_new())
expect(result.ok).to_equal(true)
expect(result.operations).to_equal("PEB TEB TLS ProcessParameters LoaderLock")
```

</details>

#### should require writable VM mappings before PEB/TEB startup mutation

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_peb_teb_memory_write_gate(wine_peb_teb_init_default(), _startup_write_space())
expect(result.ok).to_equal(true)
expect(result.state).to_equal("ready")
expect(result.write_count).to_equal(4)
expect(result.operations).to_contain("PEBWrite")
expect(result.operations).to_contain("ProcessParametersWrite")
```

</details>

#### should compose PEB/TEB memory-write readiness before NTDLL process-info handoff

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val result = wine_ntdll_execute_process_info_with_peb_teb_writes(["NtQueryInformationProcess", "NtQueryInformationThread"], _classes(), init, writes)
expect(result.ok).to_equal(true)
expect(result.operations).to_contain("PEBWrite")
expect(result.operations).to_contain("NtQueryInformationProcess")
expect(result.peb_address).to_equal(0x7ffdf000)
```

</details>

#### should plan concrete x64 PEB/TEB startup layout writes

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val plan = wine_peb_teb_layout_write_plan(init, writes)
expect(plan.ok).to_equal(true)
expect(plan.record_count).to_equal(6)
expect(plan.records[3].field_name).to_equal("ProcessEnvironmentBlock")
expect(plan.records[3].address).to_equal(0x7ffde060)
expect(plan.records[4].field_name).to_equal("ImageBaseAddress")
expect(plan.records[5].field_name).to_equal("ProcessParameters")
```

</details>

#### should compose PEB/TEB layout writes before NTDLL process-info handoff

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val plan = wine_peb_teb_layout_write_plan(init, writes)
val result = wine_ntdll_execute_process_info_with_peb_teb_layout(["NtQueryInformationProcess", "NtQueryInformationThread"], _classes(), init, plan)
expect(result.ok).to_equal(true)
expect(result.operations).to_contain("PEBTEBLayoutWritePlan")
expect(result.operations).to_contain("NtQueryInformationProcess")
expect(result.peb_address).to_equal(0x7ffdf000)
```

</details>

#### should materialize PEB/TEB startup layout writes as byte payloads

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val plan = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(plan)
expect(bytes.ok).to_equal(true)
expect(bytes.write_count).to_equal(6)
expect(bytes.byte_count).to_equal(48)
expect(bytes.writes[3].field_name).to_equal("ProcessEnvironmentBlock")
expect(bytes.writes[3].bytes[1]).to_equal(0xf0)
expect(bytes.writes[3].bytes[2]).to_equal(0xfd)
expect(bytes.operations).to_contain("PEBTEBLayoutBytesWritten")
```

</details>

#### should apply PEB/TEB startup layout bytes to VM memory with readback

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val plan = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(plan)
val applied = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
expect(applied.ok).to_equal(true)
expect(applied.write_count).to_equal(6)
expect(applied.byte_count).to_equal(48)
expect(applied.operations).to_contain("PEBTEBLayoutVMReadback")
```

</details>

#### should compose VM byte-write readback before NTDLL process-info handoff

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val plan = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(plan)
val applied = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_ntdll_execute_process_info_with_peb_teb_vm_writes(["NtQueryInformationProcess", "NtQueryInformationThread"], _classes(), init, applied)
expect(result.ok).to_equal(true)
expect(result.operations).to_contain("PEBTEBLayoutVMReadback")
expect(result.operations).to_contain("NtQueryInformationProcess")
expect(result.teb_address).to_equal(0x7ffde000)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_peb_teb_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS Wine PEB/TEB startup evidence
- REQ-018: bounded known-console process dispatch plan

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
