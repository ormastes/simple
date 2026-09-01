# Local Shadows Module Global Write Through Specification

> Tests covering interpreter: frame local sharing a module global's name.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Local Shadows Module Global Write Through Specification

## Scenarios

### interpreter: frame local sharing a module global's name

#### keeps the module global intact after pushing into the local

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the module global intact after pushing into the local
   - Expected: build_local_with_same_name(4) equals `4`
   - Expected: arena_len() equals `2`
   - Expected: arena_get(0) equals `1,2,3`
   - Expected: arena_get(1).split(",").len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the module global intact after pushing into the local")
arena_push("1,2,3")
arena_push("4,5")
expect(build_local_with_same_name(4)).to_equal(4)
expect(arena_len()).to_equal(2)
expect(arena_get(0)).to_equal("1,2,3")
expect(arena_get(1).split(",").len()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/local_shadows_module_global_write_through_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering interpreter: frame local sharing a module global's name.
- interpreter: frame local sharing a module global's name

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

- Canonical SPipe generation for source `1e3fca4d7e3ad9e44c6ef3299f3596db50aee0a7dc4045ee6802288fd4648d6a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1e3fca4d7e3ad9e44c6ef3299f3596db50aee0a7dc4045ee6802288fd4648d6a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1e3fca4d7e3ad9e44c6ef3299f3596db50aee0a7dc4045ee6802288fd4648d6a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/compiler/interpreter/local_shadows_module_global_write_through_spec.spl
mirror: doc/06_spec/01_unit/compiler/interpreter/local_shadows_module_global_write_through_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/interpreter/local_shadows_module_global_write_through_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/interpreter/local_shadows_module_global_write_through_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/interpreter/local_shadows_module_global_write_through_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/interpreter/local_shadows_module_global_write_through_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the module global intact after pushing into the local' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
