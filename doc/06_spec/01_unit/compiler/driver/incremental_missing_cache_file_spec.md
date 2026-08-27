# Incremental Missing Cache File Specification

> Tests covering incremental cache reads on a missing file.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Incremental Missing Cache File Specification

## Scenarios

### incremental cache reads on a missing file

#### read returns nil (not empty text) for a missing path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- read returns nil (not empty text) for a missing path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read returns nil (not empty text) for a missing path")
val got = incremental_file_read_text(missing)
expect got == nil
```

</details>

#### parse of a missing cache file is an Err, never a parse of nil

- parse of a missing cache file is an Err, never a parse of nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse of a missing cache file is an Err, never a parse of nil")
val r = incremental_parse_file(missing)
expect r.is_err()
```

</details>

#### fingerprint of a missing file is a miss

- fingerprint of a missing file is a miss


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fingerprint of a missing file is a miss")
expect FileFingerprint.from_file(missing) == nil
```

</details>

#### dependency interface fold over a missing dep fails closed (nil)

- dependency interface fold over a missing dep fails closed (nil)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dependency interface fold over a missing dep fails closed (nil)")
expect incremental_dependency_interface_fold([missing]) == nil
```

</details>

#### BuildCache.load on a missing cache path yields an empty cache

- BuildCache.load on a missing cache path yields an empty cache


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BuildCache.load on a missing cache path yields an empty cache")
val cache = BuildCache.load(missing)
expect cache.entries.keys().len() == 0
```

</details>

#### fingerprint of an existing binary (non-UTF-8) file is NOT a miss

- fingerprint of an existing binary (non-UTF-8) file is NOT a miss


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fingerprint of an existing binary (non-UTF-8) file is NOT a miss")
# rt_file_read_text is nil for non-UTF-8 bytes; native capsule receipts
# fingerprint .o files through this path, so nil-text must fall back to
# a byte digest rather than report the object as missing.
val fp = FileFingerprint.from_file("/bin/sh")
expect fp != nil
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/incremental_missing_cache_file_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering incremental cache reads on a missing file.
- incremental cache reads on a missing file

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `853146d580187bd96713a060478166fe651b30212dbf1276a12f73776dd5a170`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `853146d580187bd96713a060478166fe651b30212dbf1276a12f73776dd5a170`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `853146d580187bd96713a060478166fe651b30212dbf1276a12f73776dd5a170`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/driver/incremental_missing_cache_file_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/incremental_missing_cache_file_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/incremental_missing_cache_file_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/incremental_missing_cache_file_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/incremental_missing_cache_file_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'read returns nil (not empty text) for a missing path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/incremental_missing_cache_file_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parse of a missing cache file is an Err, never a parse of nil' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/incremental_missing_cache_file_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fingerprint of a missing file is a miss' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
