# Wine Ntdll Process Info Specification

> Tests covering Wine NTDLL process information bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Ntdll Process Info Specification

## Scenarios

### Wine NTDLL process information bridge

#### executes bounded process and thread information queries

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- executes bounded process and thread information queries
   - Expected: result.ok is true
   - Expected: result.process_id equals `10`
   - Expected: result.thread_id equals `20`
   - Expected: result.peb_address equals `0x7ffdf000`
   - Expected: result.teb_address equals `0x7ffde000`
   - Expected: result.image_base equals `0x400000`
   - Expected: result.classes equals `ProcessBasicInformation ProcessImageInformation ThreadBasicInformation`
   - Expected: result.operations equals `NtQueryInformationProcess NtQueryInformationThread`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("executes bounded process and thread information queries")
val result = wine_ntdll_execute_process_info(["NtQueryInformationProcess", "NtQueryInformationThread"], _classes(), wine_ntdll_process_thread_info_default())

expect(result.ok).to_equal(true)
expect(result.process_id).to_equal(10)
expect(result.thread_id).to_equal(20)
expect(result.peb_address).to_equal(0x7ffdf000)
expect(result.teb_address).to_equal(0x7ffde000)
expect(result.image_base).to_equal(0x400000)
expect(result.classes).to_equal("ProcessBasicInformation ProcessImageInformation ThreadBasicInformation")
expect(result.operations).to_equal("NtQueryInformationProcess NtQueryInformationThread")
```

</details>

#### keeps process information dispatch and classes bounded

- keeps process information dispatch and classes bounded
   - Expected: wrong_family.ok is false
   - Expected: wrong_family.error equals `bridge-wrong-category:NtCreateFile`
   - Expected: wrong_class.ok is false
   - Expected: wrong_class.error equals `ntdll-process-info-class-expected:ProcessBasicInformation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps process information dispatch and classes bounded")
val wrong_family = wine_ntdll_execute_process_info(["NtQueryInformationProcess", "NtCreateFile"], _classes(), wine_ntdll_process_thread_info_default())
expect(wrong_family.ok).to_equal(false)
expect(wrong_family.error).to_equal("bridge-wrong-category:NtCreateFile")

val wrong_class = wine_ntdll_execute_process_info(["NtQueryInformationProcess", "NtQueryInformationThread"], ["ThreadBasicInformation", "ProcessImageInformation", "ProcessBasicInformation"], wine_ntdll_process_thread_info_default())
expect(wrong_class.ok).to_equal(false)
expect(wrong_class.error).to_equal("ntdll-process-info-class-expected:ProcessBasicInformation")
```

</details>

#### rejects invalid process and thread facts

- rejects invalid process and thread facts
   - Expected: result.ok is false
   - Expected: result.error equals `NtQueryInformationThread:invalid-thread-id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects invalid process and thread facts")
val invalid = WineNtdllProcessThreadInfo(
    process_id: 10,
    thread_id: 0,
    peb_address: 0x7ffdf000,
    teb_address: 0x7ffde000,
    image_base: 0x400000,
    priority: 8
)
val result = wine_ntdll_execute_process_info(["NtQueryInformationProcess", "NtQueryInformationThread"], _classes(), invalid)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("NtQueryInformationThread:invalid-thread-id")
```

</details>

#### requires PEB/TEB initialization evidence before process-info handoff

- requires PEB/TEB initialization evidence before process-info handoff
   - Expected: result.ok is true
   - Expected: result.peb_address equals `0x7ffdf000`
   - Expected: result.teb_address equals `0x7ffde000`
   - Expected: blocked.ok is false
   - Expected: blocked.error equals `peb-teb:missing-simpleos-address-space`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requires PEB/TEB initialization evidence before process-info handoff")
val result = wine_ntdll_execute_process_info_with_peb_teb(["NtQueryInformationProcess", "NtQueryInformationThread"], _classes(), wine_peb_teb_init_default())
expect(result.ok).to_equal(true)
expect(result.peb_address).to_equal(0x7ffdf000)
expect(result.teb_address).to_equal(0x7ffde000)

val missing = WinePebTebInitEvidence(
    process_id: 10,
    thread_id: 20,
    peb_address: 0x7ffdf000,
    teb_address: 0x7ffde000,
    image_base: 0x400000,
    stack_base: 0x7ffef000,
    stack_limit: 0x7ffee000,
    tls_vector_address: 0x7ffdd000,
    process_parameters_address: 0x7ffdc000,
    evidence: "simpleos-process-identity simpleos-thread-identity"
)
val blocked = wine_ntdll_execute_process_info_with_peb_teb(["NtQueryInformationProcess", "NtQueryInformationThread"], _classes(), missing)
expect(blocked.ok).to_equal(false)
expect(blocked.error).to_equal("peb-teb:missing-simpleos-address-space")
```

</details>

#### requires PEB/TEB memory-write readiness before the write-aware process-info handoff

- requires PEB/TEB memory-write readiness before the write-aware process-info handoff
   - Expected: result.ok is true
   - Expected: result.peb_address equals `0x7ffdf000`
   - Expected: result.teb_address equals `0x7ffde000`
   - Expected: blocked.ok is false
   - Expected: blocked.error equals `peb-teb-write:peb-write:page-fault-unmapped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requires PEB/TEB memory-write readiness before the write-aware process-info handoff")
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val result = wine_ntdll_execute_process_info_with_peb_teb_writes(["NtQueryInformationProcess", "NtQueryInformationThread"], _classes(), init, writes)
expect(result.ok).to_equal(true)
expect(result.peb_address).to_equal(0x7ffdf000)
expect(result.teb_address).to_equal(0x7ffde000)
expect(result.operations).to_contain("PEBWrite")
expect(result.operations).to_contain("NtQueryInformationProcess NtQueryInformationThread")

val blocked_writes = wine_peb_teb_memory_write_gate(init, wine_vm_process_space_new(10, 30, "pid fs ipc net capability"))
val blocked = wine_ntdll_execute_process_info_with_peb_teb_writes(["NtQueryInformationProcess", "NtQueryInformationThread"], _classes(), init, blocked_writes)
expect(blocked.ok).to_equal(false)
expect(blocked.error).to_equal("peb-teb-write:peb-write:page-fault-unmapped")
```

</details>

#### requires PEB/TEB layout records before the layout-aware process-info handoff

- requires PEB/TEB layout records before the layout-aware process-info handoff
   - Expected: result.ok is true
   - Expected: result.peb_address equals `0x7ffdf000`
   - Expected: result.teb_address equals `0x7ffde000`
   - Expected: blocked.ok is false
   - Expected: blocked.error equals `peb-teb-layout:write:peb-write:page-fault-unmapped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requires PEB/TEB layout records before the layout-aware process-info handoff")
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val result = wine_ntdll_execute_process_info_with_peb_teb_layout(["NtQueryInformationProcess", "NtQueryInformationThread"], _classes(), init, layout)
expect(result.ok).to_equal(true)
expect(result.peb_address).to_equal(0x7ffdf000)
expect(result.teb_address).to_equal(0x7ffde000)
expect(result.operations).to_contain("PEBTEBLayoutWritePlan")
expect(result.operations).to_contain("NtQueryInformationProcess NtQueryInformationThread")

val blocked_writes = wine_peb_teb_memory_write_gate(init, wine_vm_process_space_new(10, 30, "pid fs ipc net capability"))
val blocked_layout = wine_peb_teb_layout_write_plan(init, blocked_writes)
val blocked = wine_ntdll_execute_process_info_with_peb_teb_layout(["NtQueryInformationProcess", "NtQueryInformationThread"], _classes(), init, blocked_layout)
expect(blocked.ok).to_equal(false)
expect(blocked.error).to_equal("peb-teb-layout:write:peb-write:page-fault-unmapped")
```

</details>

#### requires PEB/TEB VM byte-write readback before the VM-aware process-info handoff

- requires PEB/TEB VM byte-write readback before the VM-aware process-info handoff
   - Expected: result.ok is true
   - Expected: result.peb_address equals `0x7ffdf000`
   - Expected: result.teb_address equals `0x7ffde000`
   - Expected: blocked.ok is false
   - Expected: blocked.error equals `peb-teb-vm-write:bytes:layout:write:peb-write:page-fault-unmapped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requires PEB/TEB VM byte-write readback before the VM-aware process-info handoff")
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val layout = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(layout)
val vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_ntdll_execute_process_info_with_peb_teb_vm_writes(["NtQueryInformationProcess", "NtQueryInformationThread"], _classes(), init, vm_writes)
expect(result.ok).to_equal(true)
expect(result.peb_address).to_equal(0x7ffdf000)
expect(result.teb_address).to_equal(0x7ffde000)
expect(result.operations).to_contain("PEBTEBLayoutVMReadback")
expect(result.operations).to_contain("NtQueryInformationProcess NtQueryInformationThread")

val blocked_writes = wine_peb_teb_memory_write_gate(init, wine_vm_process_space_new(10, 30, "pid fs ipc net capability"))
val blocked_layout = wine_peb_teb_layout_write_plan(init, blocked_writes)
val blocked_bytes = wine_peb_teb_layout_byte_writes(blocked_layout)
val blocked_vm_writes = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), blocked_bytes)
val blocked = wine_ntdll_execute_process_info_with_peb_teb_vm_writes(["NtQueryInformationProcess", "NtQueryInformationThread"], _classes(), init, blocked_vm_writes)
expect(blocked.ok).to_equal(false)
expect(blocked.error).to_equal("peb-teb-vm-write:bytes:layout:write:peb-write:page-fault-unmapped")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_ntdll_process_info_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine NTDLL process information bridge.
- Wine NTDLL process information bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `63d6b0c85a473304e2d78aa3ac138858069d6e59a0ec5af5d37ae1865d38b54e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `63d6b0c85a473304e2d78aa3ac138858069d6e59a0ec5af5d37ae1865d38b54e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `63d6b0c85a473304e2d78aa3ac138858069d6e59a0ec5af5d37ae1865d38b54e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/wine_ntdll_process_info_spec.spl
mirror: doc/06_spec/01_unit/lib/common/wine_ntdll_process_info_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/wine_ntdll_process_info_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/wine_ntdll_process_info_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/wine_ntdll_process_info_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/wine_ntdll_process_info_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes bounded process and thread information queries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_ntdll_process_info_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps process information dispatch and classes bounded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_ntdll_process_info_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid process and thread facts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
