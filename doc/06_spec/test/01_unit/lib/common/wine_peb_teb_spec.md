# Wine Peb Teb Specification

> <details>

<!-- sdn-diagram:id=wine_peb_teb_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_peb_teb_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_peb_teb_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_peb_teb_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Peb Teb Specification

## Scenarios

### Wine PEB/TEB initialization gate

#### lists the SimpleOS and MDSOC evidence required before PEB/TEB handoff

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val required = wine_peb_teb_required_evidence()
expect(required.len()).to_equal(8)
expect(required[0]).to_equal("simpleos-process-identity")
expect(required[1]).to_equal("simpleos-thread-identity")
expect(required[2]).to_equal("simpleos-address-space")
expect(required[3]).to_equal("simpleos-stack-bounds")
expect(required[4]).to_equal("simpleos-process-parameters")
expect(required[5]).to_equal("simpleos-tls-vector")
expect(required[6]).to_equal("simpleos-mdsoc-process-port")
expect(required[7]).to_equal("simpleos-mdsoc-thread-port")
```

</details>

#### accepts bounded aligned PEB, TEB, TLS, process-parameter, and stack evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_peb_teb_init_gate(wine_peb_teb_init_default())
expect(result.ok).to_equal(true)
expect(result.state).to_equal("ready")
expect(result.peb_address).to_equal(0x7ffdf000)
expect(result.teb_address).to_equal(0x7ffde000)
expect(result.stack_base).to_equal(0x7ffef000)
expect(result.stack_limit).to_equal(0x7ffee000)
expect(result.tls_vector_address).to_equal(0x7ffdd000)
expect(result.process_parameters_address).to_equal(0x7ffdc000)
expect(result.operations).to_equal("PEB TEB TLS ProcessParameters")
```

</details>

#### rejects missing MDSOC ownership evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init = WinePebTebInitEvidence(
    process_id: 10,
    thread_id: 20,
    peb_address: 0x7ffdf000,
    teb_address: 0x7ffde000,
    image_base: 0x400000,
    stack_base: 0x7ffef000,
    stack_limit: 0x7ffee000,
    tls_vector_address: 0x7ffdd000,
    process_parameters_address: 0x7ffdc000,
    evidence: "simpleos-process-identity simpleos-thread-identity simpleos-address-space simpleos-stack-bounds simpleos-process-parameters simpleos-tls-vector"
)
val result = wine_peb_teb_init_gate(init)
expect(result.ok).to_equal(false)
expect(result.state).to_equal("missing-simpleos-mdsoc-process-port")
```

</details>

#### rejects invalid stack ordering and unaligned PEB addresses

<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad_stack = WinePebTebInitEvidence(
    process_id: 10,
    thread_id: 20,
    peb_address: 0x7ffdf000,
    teb_address: 0x7ffde000,
    image_base: 0x400000,
    stack_base: 0x7ffee000,
    stack_limit: 0x7ffef000,
    tls_vector_address: 0x7ffdd000,
    process_parameters_address: 0x7ffdc000,
    evidence: "simpleos-process-identity simpleos-thread-identity simpleos-address-space simpleos-stack-bounds simpleos-process-parameters simpleos-tls-vector simpleos-mdsoc-process-port simpleos-mdsoc-thread-port"
)
expect(wine_peb_teb_init_gate(bad_stack).state).to_equal("invalid-stack-bounds")

val unaligned = WinePebTebInitEvidence(
    process_id: 10,
    thread_id: 20,
    peb_address: 0x7ffdf008,
    teb_address: 0x7ffde000,
    image_base: 0x400000,
    stack_base: 0x7ffef000,
    stack_limit: 0x7ffee000,
    tls_vector_address: 0x7ffdd000,
    process_parameters_address: 0x7ffdc000,
    evidence: "simpleos-process-identity simpleos-thread-identity simpleos-address-space simpleos-stack-bounds simpleos-process-parameters simpleos-tls-vector simpleos-mdsoc-process-port simpleos-mdsoc-thread-port"
)
expect(wine_peb_teb_init_gate(unaligned).state).to_equal("invalid-peb-address")
```

</details>

#### requires the bounded loader-lock sequence around PEB/TEB startup

1. wine peb teb init default
2. wine kernel32 critical section table new
   - Expected: blocked.ok is false
   - Expected: blocked.state equals `loader-lock:kernel32-critical-section-sequence-expected:InitializeCriticalSec... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_peb_teb_init_with_loader_lock(wine_peb_teb_init_default(), _loader_lock_symbols(), wine_kernel32_critical_section_table_new())
expect(result.ok).to_equal(true)
expect(result.operations).to_equal("PEB TEB TLS ProcessParameters LoaderLock")

val blocked = wine_peb_teb_init_with_loader_lock(
    wine_peb_teb_init_default(),
    ["EnterCriticalSection", "InitializeCriticalSection", "LeaveCriticalSection", "DeleteCriticalSection"],
    wine_kernel32_critical_section_table_new()
)
expect(blocked.ok).to_equal(false)
expect(blocked.state).to_equal("loader-lock:kernel32-critical-section-sequence-expected:InitializeCriticalSection")
```

</details>

#### requires writable VM mappings before PEB/TEB startup fields are mutated

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_peb_teb_memory_write_gate(wine_peb_teb_init_default(), _peb_teb_write_space())
expect(result.ok).to_equal(true)
expect(result.state).to_equal("ready")
expect(result.write_count).to_equal(4)
expect(result.operations).to_equal("PEB TEB TLS ProcessParameters PEBWrite TEBWrite TLSVectorWrite ProcessParametersWrite")
```

</details>

#### blocks PEB/TEB memory writes without mapped writable startup pages

1. var read only =  peb teb write space
2. read only =  commit fixed
   - Expected: blocked.ok is false
   - Expected: blocked.state equals `peb-write:page-fault-write`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = wine_peb_teb_memory_write_gate(wine_peb_teb_init_default(), wine_vm_process_space_new(10, 30, "pid fs ipc net capability"))
expect(result.ok).to_equal(false)
expect(result.state).to_equal("peb-write:page-fault-unmapped")
expect(result.write_count).to_equal(0)

var read_only = _peb_teb_write_space()
read_only = _commit_fixed(wine_vm_process_space_new(10, 30, "pid fs ipc net capability"), 0x7ffdf000, 0x1000, "r")
val blocked = wine_peb_teb_memory_write_gate(wine_peb_teb_init_default(), read_only)
expect(blocked.ok).to_equal(false)
expect(blocked.state).to_equal("peb-write:page-fault-write")
```

</details>

#### plans x64 PEB/TEB layout writes after VM write readiness

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _peb_teb_write_space())
val plan = wine_peb_teb_layout_write_plan(init, writes)

expect(plan.ok).to_equal(true)
expect(plan.state).to_equal("ready")
expect(plan.record_count).to_equal(6)
expect(plan.records[0].field_name).to_equal("NtTib.StackBase")
expect(plan.records[0].address).to_equal(0x7ffde008)
expect(plan.records[0].value).to_equal(0x7ffef000)
expect(plan.records[3].field_name).to_equal("ProcessEnvironmentBlock")
expect(plan.records[3].address).to_equal(0x7ffde060)
expect(plan.records[3].value).to_equal(0x7ffdf000)
expect(plan.records[4].field_name).to_equal("ImageBaseAddress")
expect(plan.records[4].address).to_equal(0x7ffdf010)
expect(plan.records[5].field_name).to_equal("ProcessParameters")
expect(plan.records[5].value).to_equal(0x7ffdc000)
expect(plan.operations).to_contain("PEBTEBLayoutWritePlan")
```

</details>

#### blocks PEB/TEB layout planning when VM write readiness failed

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, wine_vm_process_space_new(10, 30, "pid fs ipc net capability"))
val plan = wine_peb_teb_layout_write_plan(init, writes)

expect(plan.ok).to_equal(false)
expect(plan.state).to_equal("write:peb-write:page-fault-unmapped")
expect(plan.record_count).to_equal(0)
```

</details>

#### materializes PEB/TEB layout records as little-endian byte writes

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _peb_teb_write_space())
val plan = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(plan)

expect(bytes.ok).to_equal(true)
expect(bytes.state).to_equal("ready")
expect(bytes.write_count).to_equal(6)
expect(bytes.byte_count).to_equal(48)
expect(bytes.writes[0].field_name).to_equal("NtTib.StackBase")
expect(bytes.writes[0].address).to_equal(0x7ffde008)
expect(bytes.writes[0].bytes[0]).to_equal(0x00)
expect(bytes.writes[0].bytes[1]).to_equal(0xf0)
expect(bytes.writes[0].bytes[2]).to_equal(0xfe)
expect(bytes.writes[0].bytes[3]).to_equal(0x7f)
expect(bytes.writes[4].field_name).to_equal("ImageBaseAddress")
expect(bytes.writes[4].bytes[0]).to_equal(0x00)
expect(bytes.writes[4].bytes[1]).to_equal(0x00)
expect(bytes.writes[4].bytes[2]).to_equal(0x40)
expect(bytes.operations).to_contain("PEBTEBLayoutBytesWritten")
```

</details>

#### blocks byte writes when PEB/TEB layout planning failed

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, wine_vm_process_space_new(10, 30, "pid fs ipc net capability"))
val plan = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(plan)

expect(bytes.ok).to_equal(false)
expect(bytes.state).to_equal("layout:write:peb-write:page-fault-unmapped")
expect(bytes.write_count).to_equal(0)
```

</details>

#### applies PEB/TEB byte writes to VM memory and verifies readback

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _peb_teb_write_space())
val plan = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(plan)
val applied = wine_peb_teb_apply_layout_byte_writes(_peb_teb_write_space(), bytes)

expect(applied.ok).to_equal(true)
expect(applied.state).to_equal("ready")
expect(applied.write_count).to_equal(6)
expect(applied.byte_count).to_equal(48)
expect(applied.operations).to_contain("PEBTEBLayoutVMBytesWritten")
expect(applied.operations).to_contain("PEBTEBLayoutVMReadback")
```

</details>

#### blocks PEB/TEB VM byte writes on read-only startup memory

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _peb_teb_write_space())
val plan = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(plan)
val read_only = _commit_fixed(wine_vm_process_space_new(10, 30, "pid fs ipc net capability"), 0x7ffde000, 0x1000, "r")
val applied = wine_peb_teb_apply_layout_byte_writes(read_only, bytes)

expect(applied.ok).to_equal(false)
expect(applied.state).to_equal("vm-write:NtTib.StackBase:page-fault-write")
expect(applied.write_count).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_peb_teb_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine PEB/TEB initialization gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
