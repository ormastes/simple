# shb_import_test_spec

> Purpose: Prove the compiler.shb.* modules import and execute: shb_source_hash is

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# shb_import_test_spec

Purpose: Prove the compiler.shb.* modules import and execute: shb_source_hash is

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/shb/shb_import_test_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove the compiler.shb.* modules import and execute: shb_source_hash is
deterministic for identical input and discriminates different inputs.
Audience: compiler driver engineers who own the shb module family.

## Scenarios

### SHB Import Test

#### loads without error

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- loads without error
   - Expected: h1 == h2 is true
   - Expected: h1 != h3 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("loads without error")
# evidence(protocol_json): hash determinism and discrimination below are the complete typed oracle
val h1 = shb_source_hash("shb import probe")
val h2 = shb_source_hash("shb import probe")
val h3 = shb_source_hash("shb import probe X")
expect(h1 == h2).to_equal(true)
expect(h1 != h3).to_equal(true)
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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d594472ff42c169ab5dcbc4186590bec553afdfa7d755ab81df4c77dbb40b225`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d594472ff42c169ab5dcbc4186590bec553afdfa7d755ab81df4c77dbb40b225`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d594472ff42c169ab5dcbc4186590bec553afdfa7d755ab81df4c77dbb40b225`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/01_unit/compiler/shb/shb_import_test_spec.spl
mirror: doc/06_spec/01_unit/compiler/shb/shb_import_test_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/shb/shb_import_test_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/shb/shb_import_test_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
