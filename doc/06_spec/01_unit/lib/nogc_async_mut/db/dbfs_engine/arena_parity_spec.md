# Arena Parity Specification

> Tests covering nogc_async_mut DBFS arena facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Arena Parity Specification

## Scenarios

### nogc_async_mut DBFS arena facade

#### re-exports DBFS arena operations from the canonical backend

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports DBFS arena operations from the canonical backend
   - Expected: aid > 0 is true
   - Expected: arena_append_impl(aid, data, 0) equals `4`
   - Expected: arena_total_bytes_impl(aid) equals `4`
   - Expected: rd.len() as i64 equals `4`
   - Expected: rd[0] equals `0x64`
   - Expected: rd[3] equals `0x73`
   - Expected: arena_seal_impl(aid, 1) is true
   - Expected: arena_is_sealed_impl(aid) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports DBFS arena operations from the canonical backend")
val aid = arena_create_impl(0, 128)
expect(aid > 0).to_equal(true)
val data: [u8] = [0x64, 0x62, 0x66, 0x73]
expect(arena_append_impl(aid, data, 0)).to_equal(4)
expect(arena_total_bytes_impl(aid)).to_equal(4)
val rd = arena_readv_impl(aid, 0, 4)
expect(rd.len() as i64).to_equal(4)
expect(rd[0]).to_equal(0x64)
expect(rd[3]).to_equal(0x73)
expect(arena_seal_impl(aid, 1)).to_equal(true)
expect(arena_is_sealed_impl(aid)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/db/dbfs_engine/arena_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_async_mut DBFS arena facade.
- nogc_async_mut DBFS arena facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `7cb70d380bb4c798dad67c98e5e496cf651d62fcbcaa76c4aaebd11febbf9202`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7cb70d380bb4c798dad67c98e5e496cf651d62fcbcaa76c4aaebd11febbf9202`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7cb70d380bb4c798dad67c98e5e496cf651d62fcbcaa76c4aaebd11febbf9202`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/nogc_async_mut/db/dbfs_engine/arena_parity_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/db/dbfs_engine/arena_parity_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/db/dbfs_engine/arena_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/db/dbfs_engine/arena_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/db/dbfs_engine/arena_parity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/db/dbfs_engine/arena_parity_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports DBFS arena operations from the canonical backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
