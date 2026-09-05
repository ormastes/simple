# Deploy Toolchains Artifact Admission Specification

> Tests covering SimpleOS guest toolchain artifact admission.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Deploy Toolchains Artifact Admission Specification

## Scenarios

### SimpleOS guest toolchain artifact admission

#### admits a bounded x86_64 executable candidate structurally

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- admits a bounded x86_64 executable candidate structurally
   - Expected: guest_static_tool_candidate_admit(x86_64_exec_candidate()) equals `Ok(())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits a bounded x86_64 executable candidate structurally")
expect(guest_static_tool_candidate_admit(x86_64_exec_candidate())).to_equal(Ok(()))
```

</details>

#### rejects the current all-zero placeholder shape

- rejects the current all-zero placeholder shape


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects the current all-zero placeholder shape")
expect(guest_static_tool_candidate_admit([0u8, 0u8, 0u8, 0u8])).to_equal(
    Err("ELF too small for ident")
)
```

</details>

#### rejects a truncated program-header table

- rejects a truncated program-header table


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a truncated program-header table")
val truncated = x86_64_exec_candidate().slice(0, 100)
expect(guest_static_tool_candidate_admit(truncated)).to_equal(
    Err("ELF64 program header table is truncated")
)
```

</details>

#### rejects a valid header for the wrong target machine

- rejects a valid header for the wrong target machine


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a valid header for the wrong target machine")
var wrong_target = x86_64_exec_candidate()
wrong_target[18] = 183u8
expect(guest_static_tool_candidate_admit(wrong_target)).to_equal(
    Err("ELF64 machine is not the expected target architecture")
)
```

</details>

#### requires the entry to lie in an executable load segment

- requires the entry to lie in an executable load segment


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires the entry to lie in an executable load segment")
var non_exec = x86_64_exec_candidate()
non_exec[68] = 4u8
expect(guest_static_tool_candidate_admit(non_exec)).to_equal(
    Err("ELF entry is not inside an executable PT_LOAD segment")
)
```

</details>

#### rejects an entry that points only into the zero-filled BSS tail

- rejects an entry that points only into the zero-filled BSS tail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an entry that points only into the zero-filled BSS tail")
var bss_entry = x86_64_exec_candidate()
# p_filesz=1, p_memsz=2, entry=vaddr+1.
bss_entry[24] = 1u8
bss_entry[104] = 2u8
expect(guest_static_tool_candidate_admit(bss_entry)).to_equal(
    Err("ELF entry is not inside an executable PT_LOAD segment")
)
```

</details>

#### rejects an overflowing in-memory load range

- rejects an overflowing in-memory load range


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an overflowing in-memory load range")
var overflowing = x86_64_exec_candidate()
var i = 104
while i < 112:
    overflowing[i] = 0xffu8
    i = i + 1
expect(guest_static_tool_candidate_admit(overflowing)).to_equal(
    Err("ELF PT_LOAD virtual range overflows")
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/port/deploy_toolchains_artifact_admission_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS guest toolchain artifact admission.
- SimpleOS guest toolchain artifact admission

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `74e9140108d7a04aa945075d7133fabcfe412746744571b1325e1142efd7d54e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `74e9140108d7a04aa945075d7133fabcfe412746744571b1325e1142efd7d54e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `74e9140108d7a04aa945075d7133fabcfe412746744571b1325e1142efd7d54e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/port/deploy_toolchains_artifact_admission_spec.spl
mirror: doc/06_spec/01_unit/os/port/deploy_toolchains_artifact_admission_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/port/deploy_toolchains_artifact_admission_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/port/deploy_toolchains_artifact_admission_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/port/deploy_toolchains_artifact_admission_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits a bounded x86_64 executable candidate structurally' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/port/deploy_toolchains_artifact_admission_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects the current all-zero placeholder shape' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/port/deploy_toolchains_artifact_admission_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a truncated program-header table' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
