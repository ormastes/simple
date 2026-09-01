# NoGC Sync Mutable Runtime Contracts

> The sync mutable runtime-family surface is no-GC-first. GC metadata, rooting-adjacent pointer helpers, and reference utilities that are needed by hosted sync code live under `nogc_sync_mut` unless a separate GC sync family is explicitly designed later.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NoGC Sync Mutable Runtime Contracts

The sync mutable runtime-family surface is no-GC-first. GC metadata, rooting-adjacent pointer helpers, and reference utilities that are needed by hosted sync code live under `nogc_sync_mut` unless a separate GC sync family is explicitly designed later.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Stdlib |
| Status | Implemented |
| Source | `test/feature/lib/gc_parity/nogc_sync_mut_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The sync mutable runtime-family surface is no-GC-first. GC metadata,
rooting-adjacent pointer helpers, and reference utilities that are needed by
hosted sync code live under `nogc_sync_mut` unless a separate GC sync family is
explicitly designed later.

## Scenarios

### NoGC sync mutable runtime contracts

#### when configuring GC-adjacent hosted services

#### uses nogc_sync_mut for sync GC metadata

- uses nogc_sync_mut for sync GC metadata
   - Expected: config.young_size equals `4 * 1024`
   - Expected: config.old_size equals `16 * 1024`
   - Expected: stats.collections equals `0`
   - Expected: stats.bytes_allocated equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses nogc_sync_mut for sync GC metadata")
val config = GcConfig.with_heap_size(20 * 1024)
expect(config.young_size).to_equal(4 * 1024)
expect(config.old_size).to_equal(16 * 1024)

val stats = GcStats.new()
expect(stats.collections).to_equal(0)
expect(stats.bytes_allocated).to_equal(0)
```

</details>

#### when using pointer handles

#### uses nogc_sync_mut pointer helpers as the sync backend

- uses nogc_sync_mut pointer helpers as the sync backend
   - Expected: handle_deref(handle) equals `99`
   - Expected: handle_free(handle) is true
   - Expected: handle_deref(handle) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses nogc_sync_mut pointer helpers as the sync backend")
handle_pool_new(2)
val handle = handle_alloc(99)
expect(handle_deref(handle)).to_equal(99)
expect(handle_free(handle)).to_equal(true)
expect(handle_deref(handle)).to_equal(-1)
```

</details>

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

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c1d087edca62a5f433016937eb06363b8dd1106039b739bbb56cc635751427ce`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c1d087edca62a5f433016937eb06363b8dd1106039b739bbb56cc635751427ce`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c1d087edca62a5f433016937eb06363b8dd1106039b739bbb56cc635751427ce`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/feature/lib/gc_parity/nogc_sync_mut_contract_spec.spl
mirror: doc/06_spec/feature/lib/gc_parity/nogc_sync_mut_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/lib/gc_parity/nogc_sync_mut_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/lib/gc_parity/nogc_sync_mut_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/lib/gc_parity/nogc_sync_mut_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/lib/gc_parity/nogc_sync_mut_contract_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses nogc_sync_mut for sync GC metadata' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/lib/gc_parity/nogc_sync_mut_contract_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses nogc_sync_mut pointer helpers as the sync backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
