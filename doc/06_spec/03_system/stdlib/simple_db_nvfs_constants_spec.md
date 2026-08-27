# simple_db_nvfs_constants_spec

> Root-level coverage for FR-SIMPLE_DB-M2-002 canonical NVFS constants.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_db_nvfs_constants_spec

Root-level coverage for FR-SIMPLE_DB-M2-002 canonical NVFS constants.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/stdlib/simple_db_nvfs_constants_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Root-level coverage for FR-SIMPLE_DB-M2-002 canonical NVFS constants.

## Scenarios

### NVFS shared constants

#### exports the canonical ordinals requested by FR-SIMPLE_DB-M2-002

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exports the canonical ordinals requested by FR-SIMPLE_DB-M2-002
   - Expected: STORAGE_CLASS_DB_WAL equals `1`
   - Expected: STORAGE_CLASS_META_DURABLE equals `2`
   - Expected: STORAGE_CLASS_DB_TEMP equals `3`
   - Expected: DURABILITY_DATA_DURABLE equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports the canonical ordinals requested by FR-SIMPLE_DB-M2-002")
expect(STORAGE_CLASS_DB_WAL).to_equal(1)
expect(STORAGE_CLASS_META_DURABLE).to_equal(2)
expect(STORAGE_CLASS_DB_TEMP).to_equal(3)
expect(DURABILITY_DATA_DURABLE).to_equal(1)
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `264b9d88bfc36cf170b43e6c8dbf4641c5eb152b66ab87f9c175252739459bc8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `264b9d88bfc36cf170b43e6c8dbf4641c5eb152b66ab87f9c175252739459bc8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `264b9d88bfc36cf170b43e6c8dbf4641c5eb152b66ab87f9c175252739459bc8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/stdlib/simple_db_nvfs_constants_spec.spl
mirror: doc/06_spec/03_system/stdlib/simple_db_nvfs_constants_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/stdlib/simple_db_nvfs_constants_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/stdlib/simple_db_nvfs_constants_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/stdlib/simple_db_nvfs_constants_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/stdlib/simple_db_nvfs_constants_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exports the canonical ordinals requested by FR-SIMPLE_DB-M2-002' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
