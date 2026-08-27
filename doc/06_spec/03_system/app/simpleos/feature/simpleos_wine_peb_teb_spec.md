# Simpleos Wine Peb Teb Specification

> Tests covering SimpleOS Wine PEB/TEB startup evidence, REQ-018: bounded known-console process dispatch plan.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Wine Peb Teb Specification

## Scenarios

### SimpleOS Wine PEB/TEB startup evidence

### REQ-018: bounded known-console process dispatch plan

#### PEB/TEB/TLS evidence validates before NTDLL process-info handoff

- validate gated PEB/TEB init and execute the NTDLL process-info handoff
   - Expected: init.ok is true
   - Expected: init.operations equals `PEB TEB TLS ProcessParameters`
   - Expected: result.ok is true
   - Expected: result.classes equals `ProcessBasicInformation ProcessImageInformation ThreadBasicInformation`
   - Expected: result.peb_address equals `0x7ffdf000`
   - Expected: result.teb_address equals `0x7ffde000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-018
# @req REQ-SSPEC-SYSTEM
step("validate gated PEB/TEB init and execute the NTDLL process-info handoff")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# evidence(protocol_json): operations/classes/peb/teb addresses asserted below are the complete typed oracle
val init = wine_peb_teb_init_gate(wine_peb_teb_init_default())
expect(init.ok).to_equal(true)
expect(init.operations).to_equal("PEB TEB TLS ProcessParameters")

val result = wine_ntdll_execute_process_info_with_peb_teb(["NtQueryInformationProcess", "NtQueryInformationThread"], _classes(), wine_peb_teb_init_default())
expect(result.ok).to_equal(true)
expect(result.classes).to_equal("ProcessBasicInformation ProcessImageInformation ThreadBasicInformation")
expect(result.peb_address).to_equal(0x7ffdf000)  # oracle: canonical modeled PEB base in the startup VM space
expect(result.teb_address).to_equal(0x7ffde000)  # oracle: canonical modeled TEB base in the startup VM space
```

</details>

#### loader-lock sequencing wraps PEB/TEB startup evidence

- initialize PEB/TEB with loader-lock critical-section sequencing
   - Expected: result.ok is true
   - Expected: result.operations equals `PEB TEB TLS ProcessParameters LoaderLock`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("initialize PEB/TEB with loader-lock critical-section sequencing")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val result = wine_peb_teb_init_with_loader_lock(wine_peb_teb_init_default(), _loader_lock_symbols(), wine_kernel32_critical_section_table_new())
expect(result.ok).to_equal(true)
expect(result.operations).to_equal("PEB TEB TLS ProcessParameters LoaderLock")
```

</details>

#### writable VM mappings gate PEB/TEB startup mutation

- gate PEB/TEB writes on a writable startup VM space
   - Expected: result.ok is true
   - Expected: result.state equals `ready`
   - Expected: result.write_count equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gate PEB/TEB writes on a writable startup VM space")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val result = wine_peb_teb_memory_write_gate(wine_peb_teb_init_default(), _startup_write_space())
expect(result.ok).to_equal(true)
expect(result.state).to_equal("ready")
expect(result.write_count).to_equal(4)  # oracle: PEB, TEB, TLS vector, ProcessParameters = four bounded writes
expect(result.operations).to_contain("PEBWrite")
expect(result.operations).to_contain("ProcessParametersWrite")
```

</details>

#### PEB/TEB memory-write readiness composes into NTDLL process-info handoff

- execute NTDLL process info with PEB/TEB memory-write readiness
   - Expected: result.ok is true
   - Expected: result.peb_address equals `0x7ffdf000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("execute NTDLL process info with PEB/TEB memory-write readiness")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val result = wine_ntdll_execute_process_info_with_peb_teb_writes(["NtQueryInformationProcess", "NtQueryInformationThread"], _classes(), init, writes)
expect(result.ok).to_equal(true)
expect(result.operations).to_contain("PEBWrite")
expect(result.operations).to_contain("NtQueryInformationProcess")
expect(result.peb_address).to_equal(0x7ffdf000)  # oracle: canonical modeled PEB base in the startup VM space
```

</details>

#### concrete x64 PEB/TEB startup layout writes are planned

- plan the x64 PEB/TEB layout write records
   - Expected: plan.ok is true
   - Expected: plan.record_count equals `6`
   - Expected: plan.records[3].field_name equals `ProcessEnvironmentBlock`
   - Expected: plan.records[3].address equals `0x7ffde060`
   - Expected: plan.records[4].field_name equals `ImageBaseAddress`
   - Expected: plan.records[5].field_name equals `ProcessParameters`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("plan the x64 PEB/TEB layout write records")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val plan = wine_peb_teb_layout_write_plan(init, writes)
expect(plan.ok).to_equal(true)
expect(plan.record_count).to_equal(6)  # oracle: InMemoryOrderModuleList, TEB self/slots fields, ProcessEnvironmentBlock, ImageBaseAddress, ProcessParameters = six layout records
expect(plan.records[3].field_name).to_equal("ProcessEnvironmentBlock")
expect(plan.records[3].address).to_equal(0x7ffde060)  # oracle: TEB+0x60 hosts the ProcessEnvironmentBlock pointer on x64
expect(plan.records[4].field_name).to_equal("ImageBaseAddress")
expect(plan.records[5].field_name).to_equal("ProcessParameters")
```

</details>

#### PEB/TEB layout writes compose into NTDLL process-info handoff

- execute NTDLL process info with the PEB/TEB layout write plan
   - Expected: result.ok is true
   - Expected: result.peb_address equals `0x7ffdf000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("execute NTDLL process info with the PEB/TEB layout write plan")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val plan = wine_peb_teb_layout_write_plan(init, writes)
val result = wine_ntdll_execute_process_info_with_peb_teb_layout(["NtQueryInformationProcess", "NtQueryInformationThread"], _classes(), init, plan)
expect(result.ok).to_equal(true)
expect(result.operations).to_contain("PEBTEBLayoutWritePlan")
expect(result.operations).to_contain("NtQueryInformationProcess")
expect(result.peb_address).to_equal(0x7ffdf000)  # oracle: canonical modeled PEB base in the startup VM space
```

</details>

#### PEB/TEB startup layout writes materialize as byte payloads

- materialize the layout plan into byte payloads
   - Expected: bytes.ok is true
   - Expected: bytes.write_count equals `6`
   - Expected: bytes.byte_count equals `48`
   - Expected: bytes.writes[3].field_name equals `ProcessEnvironmentBlock`
   - Expected: bytes.writes[3].bytes[1] equals `0xf0`
   - Expected: bytes.writes[3].bytes[2] equals `0xfd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("materialize the layout plan into byte payloads")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val plan = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(plan)
expect(bytes.ok).to_equal(true)
expect(bytes.write_count).to_equal(6)  # oracle: one byte payload per layout record
expect(bytes.byte_count).to_equal(48)  # oracle: six records x eight bytes per x64 pointer/quad
expect(bytes.writes[3].field_name).to_equal("ProcessEnvironmentBlock")
expect(bytes.writes[3].bytes[1]).to_equal(0xf0)  # oracle: low byte of the 0x7ffdf000 PEB address, little-endian
expect(bytes.writes[3].bytes[2]).to_equal(0xfd)  # oracle: second byte of the 0x7ffdf000 PEB address, little-endian
expect(bytes.operations).to_contain("PEBTEBLayoutBytesWritten")
```

</details>

#### PEB/TEB startup layout bytes apply to VM memory with readback

- apply layout bytes to the VM space and read them back
   - Expected: applied.ok is true
   - Expected: applied.write_count equals `6`
   - Expected: applied.byte_count equals `48`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("apply layout bytes to the VM space and read them back")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val plan = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(plan)
val applied = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
expect(applied.ok).to_equal(true)
expect(applied.write_count).to_equal(6)  # oracle: one VM write per layout record
expect(applied.byte_count).to_equal(48)  # oracle: six records x eight bytes per x64 pointer/quad
expect(applied.operations).to_contain("PEBTEBLayoutVMReadback")
```

</details>

#### VM byte-write readback composes into NTDLL process-info handoff

- execute NTDLL process info with applied VM byte-writes
   - Expected: result.ok is true
   - Expected: result.teb_address equals `0x7ffde000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("execute NTDLL process info with applied VM byte-writes")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val init = wine_peb_teb_init_default()
val writes = wine_peb_teb_memory_write_gate(init, _startup_write_space())
val plan = wine_peb_teb_layout_write_plan(init, writes)
val bytes = wine_peb_teb_layout_byte_writes(plan)
val applied = wine_peb_teb_apply_layout_byte_writes(_startup_write_space(), bytes)
val result = wine_ntdll_execute_process_info_with_peb_teb_vm_writes(["NtQueryInformationProcess", "NtQueryInformationThread"], _classes(), init, applied)
expect(result.ok).to_equal(true)
expect(result.operations).to_contain("PEBTEBLayoutVMReadback")
expect(result.operations).to_contain("NtQueryInformationProcess")
expect(result.teb_address).to_equal(0x7ffde000)  # oracle: canonical modeled TEB base in the startup VM space
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_wine_peb_teb_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS Wine PEB/TEB startup evidence, REQ-018: bounded known-console process dispatch plan.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-018`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `969557ac7573fef20e2671d434bd96f96d4d1893e03635a58902941c5dcf4a5e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `969557ac7573fef20e2671d434bd96f96d4d1893e03635a58902941c5dcf4a5e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `969557ac7573fef20e2671d434bd96f96d4d1893e03635a58902941c5dcf4a5e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/03_system/app/simpleos/feature/simpleos_wine_peb_teb_spec.spl
mirror: doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_peb_teb_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_peb_teb_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos/feature/simpleos_wine_peb_teb_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
