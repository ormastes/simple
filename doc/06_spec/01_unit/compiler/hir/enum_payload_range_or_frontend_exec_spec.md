# Enum Payload Range Or Frontend Exec Specification

> Tests covering pure-Simple frontend: or/range enum payload sub-patterns.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enum Payload Range Or Frontend Exec Specification

## Scenarios

### pure-Simple frontend: or/range enum payload sub-patterns

#### lowers an Or payload sub-pattern without errors

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lowers an Or payload sub-pattern without errors
   - Expected: hl.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers an Or payload sub-pattern without errors")
val src = "enum Shape:\n    Square(i64)\n\npub fn f(s: Shape) -> i64:\n    match s:\n        case Shape.Square(2 | 3): 100\n        case _: 0\n"
val parsed = parse_full_frontend(src, "testdata/or.spl", "or", Logger(level: 0))
var hl = HirLowering.with_filename("testdata/or.spl")
val hir = hl.lower_module(parsed)
for err in hl.errors:
    print("ERR: " + err.message)
expect(hl.errors.len()).to_equal(0)
```

</details>

#### lowers a Range payload sub-pattern without errors

- lowers a Range payload sub-pattern without errors
   - Expected: hl.errors.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lowers a Range payload sub-pattern without errors")
val src = "enum Shape:\n    Square(i64)\n\npub fn g(s: Shape) -> i64:\n    match s:\n        case Shape.Square(1..5): 100\n        case _: 0\n"
val parsed = parse_full_frontend(src, "testdata/rg.spl", "rg", Logger(level: 0))
var hl = HirLowering.with_filename("testdata/rg.spl")
val hir = hl.lower_module(parsed)
for err in hl.errors:
    print("ERR2: " + err.message)
expect(hl.errors.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/hir/enum_payload_range_or_frontend_exec_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering pure-Simple frontend: or/range enum payload sub-patterns.
- pure-Simple frontend: or/range enum payload sub-patterns

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6e283b07905bac62df245dfdec2350217a05d75d44a82605a4071f9e9249f3c7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6e283b07905bac62df245dfdec2350217a05d75d44a82605a4071f9e9249f3c7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6e283b07905bac62df245dfdec2350217a05d75d44a82605a4071f9e9249f3c7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/hir/enum_payload_range_or_frontend_exec_spec.spl
mirror: doc/06_spec/01_unit/compiler/hir/enum_payload_range_or_frontend_exec_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/hir/enum_payload_range_or_frontend_exec_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/hir/enum_payload_range_or_frontend_exec_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/hir/enum_payload_range_or_frontend_exec_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/hir/enum_payload_range_or_frontend_exec_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers an Or payload sub-pattern without errors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/hir/enum_payload_range_or_frontend_exec_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lowers a Range payload sub-pattern without errors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
