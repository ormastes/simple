# Fs Exec Blob Coherence Specification

> Tests covering x86_64 fs-exec blob diagnostic predicate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fs Exec Blob Coherence Specification

## Scenarios

### x86_64 fs-exec blob diagnostic predicate

#### rejects a zero blob regardless of byte length

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects a zero blob regardless of byte length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a zero blob regardless of byte length")
expect(x86_64_fs_exec_handoff_blob_ready(0, 0.to_u64())).to_be(false)
expect(x86_64_fs_exec_handoff_blob_ready(5, 0.to_u64())).to_be(false)
```

</details>

#### rejects a too-small byte length with a nonzero blob

- rejects a too-small byte length with a nonzero blob


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a too-small byte length with a nonzero blob")
expect(x86_64_fs_exec_handoff_blob_ready(4, 1.to_u64())).to_be(false)
```

</details>

#### reports diagnostic readiness without authorizing execution

- reports diagnostic readiness without authorizing execution
   - Expected: result equals `-13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("reports diagnostic readiness without authorizing execution")
expect(x86_64_fs_exec_handoff_blob_ready(5, 1.to_u64())).to_be(true)
val result = x86_64_fs_exec_spawn("/sys/apps/unsigned.elf", [], [])
expect(result).to_equal(-13)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/fs_exec_blob_coherence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering x86_64 fs-exec blob diagnostic predicate.
- x86_64 fs-exec blob diagnostic predicate

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `95a5a4d581dfa4d59de35e2151d2a2dd965bf852a95c5ae69677574a2a162b64`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `95a5a4d581dfa4d59de35e2151d2a2dd965bf852a95c5ae69677574a2a162b64`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `95a5a4d581dfa4d59de35e2151d2a2dd965bf852a95c5ae69677574a2a162b64`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/kernel/loader/fs_exec_blob_coherence_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/loader/fs_exec_blob_coherence_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/loader/fs_exec_blob_coherence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/loader/fs_exec_blob_coherence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/loader/fs_exec_blob_coherence_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/loader/fs_exec_blob_coherence_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a zero blob regardless of byte length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/loader/fs_exec_blob_coherence_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a too-small byte length with a nonzero blob' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/loader/fs_exec_blob_coherence_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports diagnostic readiness without authorizing execution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
