# Shb Mtime Specification

> Tests covering SHB source mtime header.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shb Mtime Specification

## Scenarios

### SHB source mtime header

#### round-trips source mtime through the real writer and reader

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trips source mtime through the real writer and reader
   - Expected: shb_write_with_source_mtime(iface, path, 333) is true
   - Expected: reader.is_valid() is true
   - Expected: reader.source_hash() equals `111`
   - Expected: reader.interface_hash() equals `222`
   - Expected: reader.source_mtime() equals `333`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips source mtime through the real writer and reader")
val path = "/tmp/simple_shb_mtime_spec.shb"
file_delete(path)

val iface = shb_module_interface_new(111, 222)

expect(shb_write_with_source_mtime(iface, path, 333)).to_equal(true)

val reader = ShbReader.open(path)
expect(reader.is_valid()).to_equal(true)
expect(reader.source_hash()).to_equal(111)
expect(reader.interface_hash()).to_equal(222)
expect(reader.source_mtime()).to_equal(333)

file_delete(path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/cache/shb_mtime_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SHB source mtime header.
- SHB source mtime header

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

- Canonical SPipe generation for source `6f30830ab6b7aa7fb75c7c57f138c956bf20492d620219dc8e2fc5e442f0057d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6f30830ab6b7aa7fb75c7c57f138c956bf20492d620219dc8e2fc5e442f0057d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6f30830ab6b7aa7fb75c7c57f138c956bf20492d620219dc8e2fc5e442f0057d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler/cache/shb_mtime_spec.spl
mirror: doc/06_spec/01_unit/compiler/cache/shb_mtime_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/cache/shb_mtime_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/cache/shb_mtime_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/cache/shb_mtime_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/cache/shb_mtime_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips source mtime through the real writer and reader' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
