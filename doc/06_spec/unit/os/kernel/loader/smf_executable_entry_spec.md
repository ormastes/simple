# Smf Executable Entry Specification

> Tests covering SMF executable entry helper.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smf Executable Entry Specification

## Scenarios

### SMF executable entry helper

#### returns the typed entry point for an x86_64 executable envelope

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns the typed entry point for an x86_64 executable envelope
   - Expected: entry.is_ok() is true
   - Expected: entry.unwrap() equals `0x1234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the typed entry point for an x86_64 executable envelope")
val bytes = _smf_exec_fixture(1)
val entry = smf_executable_entry_point_for_arch(bytes, Architecture.X86_64)
expect(entry.is_ok()).to_equal(true)
expect(entry.unwrap()).to_equal(0x1234)
```

</details>

#### rejects an executable envelope for the wrong architecture

- rejects an executable envelope for the wrong architecture
   - Expected: entry.is_err() is true
   - Expected: entry.unwrap_err() equals `SMF_ERR_WRONG_ARCH`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an executable envelope for the wrong architecture")
val bytes = _smf_exec_fixture(3)
val entry = smf_executable_entry_point_for_arch(bytes, Architecture.X86_64)
expect(entry.is_err()).to_equal(true)
expect(entry.unwrap_err()).to_equal(SMF_ERR_WRONG_ARCH)
```

</details>

#### extracts the same embedded ELF stub used by filesystem spawn

- extracts the same embedded ELF stub used by filesystem spawn
   - Expected: stub.is_ok() is true
   - Expected: stub.unwrap().len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts the same embedded ELF stub used by filesystem spawn")
val bytes = _smf_exec_fixture(1)
val stub = smf_extract_executable_stub_for_arch(bytes, Architecture.X86_64)
expect(stub.is_ok()).to_equal(true)
expect(stub.unwrap().len()).to_equal(8)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/loader/smf_executable_entry_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SMF executable entry helper.
- SMF executable entry helper

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `a36f700101c68008e8d835b33d0541643c83a8c78d9d093fdfb36c17b5770451`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a36f700101c68008e8d835b33d0541643c83a8c78d9d093fdfb36c17b5770451`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a36f700101c68008e8d835b33d0541643c83a8c78d9d093fdfb36c17b5770451`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/os/kernel/loader/smf_executable_entry_spec.spl
mirror: doc/06_spec/unit/os/kernel/loader/smf_executable_entry_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/loader/smf_executable_entry_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/loader/smf_executable_entry_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/loader/smf_executable_entry_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/kernel/loader/smf_executable_entry_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the typed entry point for an x86_64 executable envelope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/loader/smf_executable_entry_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an executable envelope for the wrong architecture' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/loader/smf_executable_entry_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts the same embedded ELF stub used by filesystem spawn' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
