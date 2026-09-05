# Storage Policy Facade Specification

> Tests covering gc_async_mut storage policy facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Storage Policy Facade Specification

## Scenarios

### gc_async_mut storage policy facade

#### re-exports storage classes, durability, arena handles, and NVMe policy

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports storage classes, durability, arena handles, and NVMe policy
   - Expected: StorageClass.DB_WAL.to_string() equals `DB_WAL`
   - Expected: StorageClass.DB_WAL.is_append_only() is true
   - Expected: DurabilityClass.FlushFua.to_string() equals `FlushFua`
   - Expected: h.is_null() is true
   - Expected: req.high_gen equals `2`
   - Expected: policy.io_unit_bytes equals `4096`
   - Expected: policy.batch_bytes equals `131072`
   - Expected: policy.uses_discard is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports storage classes, durability, arena handles, and NVMe policy")
expect(StorageClass.DB_WAL.to_string()).to_equal("DB_WAL")
expect(StorageClass.DB_WAL.is_append_only()).to_equal(true)
expect(DurabilityClass.FlushFua.to_string()).to_equal("FlushFua")
val h = ArenaHandle.null()
expect(h.is_null()).to_equal(true)
val req = FlushRequest(arena_id: 7, low_gen: 1, high_gen: 2, durability: DurabilityClass.Flush)
expect(req.high_gen).to_equal(2)
val facts = samsung_mzql2960hcjr_sysfs_facts()
val policy = nvme_policy_for_class(facts, StorageClass.DB_WAL)
expect(policy.io_unit_bytes).to_equal(4096)
expect(policy.batch_bytes).to_equal(131072)
expect(policy.uses_discard).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/storage/storage_policy_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut storage policy facade.
- gc_async_mut storage policy facade

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

- Canonical SPipe generation for source `fb27d0e2a1dd45e2e8c8c856f3ec23e4b168e6e6194dfae14d947f763d66645b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fb27d0e2a1dd45e2e8c8c856f3ec23e4b168e6e6194dfae14d947f763d66645b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fb27d0e2a1dd45e2e8c8c856f3ec23e4b168e6e6194dfae14d947f763d66645b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/lib/gc_async_mut/storage/storage_policy_facade_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/storage/storage_policy_facade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/storage/storage_policy_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/storage/storage_policy_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/storage/storage_policy_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/gc_async_mut/storage/storage_policy_facade_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports storage classes, durability, arena handles, and NVMe policy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
