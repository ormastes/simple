# Nvfs Name Persistence Specification

> Tests covering NvfsPosixDriver name table persistence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nvfs Name Persistence Specification

## Scenarios

### NvfsPosixDriver name table persistence

#### file created on first mount survives remount

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- file created on first mount survives remount
   - Expected: res.file_found is true
   - Expected: res.read_ok is true
   - Expected: res.read_n equals `3`
   - Expected: res.first_byte equals `0xABu8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("file created on first mount survives remount")
var dev = _make_persist_device()
val res = _do_write_remount_read(dev)
expect(res.file_found).to_equal(true)
expect(res.read_ok).to_equal(true)
expect(res.read_n).to_equal(3)
expect(res.first_byte).to_equal(0xABu8)
```

</details>

#### multiple files persist across remount

- multiple files persist across remount
   - Expected: found equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("multiple files persist across remount")
var dev = _make_persist_device()
val found = _do_multi_file_remount(dev)
expect(found).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/storage/nvfs/nvfs_name_persistence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering NvfsPosixDriver name table persistence.
- NvfsPosixDriver name table persistence

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `09758d374870d2ab1d42969fa7fa3e54f2bbf32d519bad5ca14071b99423f6b0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `09758d374870d2ab1d42969fa7fa3e54f2bbf32d519bad5ca14071b99423f6b0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `09758d374870d2ab1d42969fa7fa3e54f2bbf32d519bad5ca14071b99423f6b0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/integration/storage/nvfs/nvfs_name_persistence_spec.spl
mirror: doc/06_spec/integration/storage/nvfs/nvfs_name_persistence_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/storage/nvfs/nvfs_name_persistence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/storage/nvfs/nvfs_name_persistence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/storage/nvfs/nvfs_name_persistence_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/storage/nvfs/nvfs_name_persistence_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'file created on first mount survives remount' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/nvfs/nvfs_name_persistence_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'multiple files persist across remount' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
