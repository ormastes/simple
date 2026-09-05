# Generic Dict Struct Adjacency Specification

> Tests covering generic dictionary field declaration boundaries.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generic Dict Struct Adjacency Specification

## Scenarios

### generic dictionary field declaration boundaries

#### parses a following top-level struct outside the prior owner

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses a following top-level struct outside the prior owner
   - Expected: parser_has_errors() is false
   - Expected: parser_get_errors().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses a following top-level struct outside the prior owner")
val source = (
    "type CaptureMap = {text: i64}\n" +
    "struct ClosureValue:\n" +
    "    captures: CaptureMap\n" +
    "\n" +
    "struct ObjectValue:\n" +
    "    class_name: text\n" +
    "    handle: i64\n"
)

parse_module(source, "generic_dict_struct_adjacency_spec.spl")
expect(parser_has_errors()).to_equal(false)
expect(parser_get_errors().len()).to_equal(0)
```

</details>

#### keeps HIR template maps behind the bootstrap-safe named boundary

- keeps HIR template maps behind the bootstrap-safe named boundary
   - Expected: source does not contain `type_bindings: Dict<text, HirType>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps HIR template maps behind the bootstrap-safe named boundary")
val source = file_read("src/compiler/20.hir/hir_definitions.spl")

expect(source).to_contain("type HirTypeBindings = {text: HirType}")
expect(source).to_contain("type_bindings: HirTypeBindings")
expect(source.contains("type_bindings: Dict<text, HirType>")).to_equal(false)
```

</details>

#### keeps backend symbol-name maps behind the bootstrap-safe named boundary

- keeps backend symbol-name maps behind the bootstrap-safe named boundary
   - Expected: source does not contain `names: Dict<i64, text>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps backend symbol-name maps behind the bootstrap-safe named boundary")
val source = file_read("src/compiler/70.backend/backend/env.spl")

expect(source).to_contain("type SymbolNameMap = {i64: text}")
expect(source).to_contain("names: SymbolNameMap")
expect(source.contains("names: Dict<i64, text>")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/generic_dict_struct_adjacency_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering generic dictionary field declaration boundaries.
- generic dictionary field declaration boundaries

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `71ece2ea045908f18b0d2d686010f616a1cd8def6449d135b6018b27e7db3493`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `71ece2ea045908f18b0d2d686010f616a1cd8def6449d135b6018b27e7db3493`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `71ece2ea045908f18b0d2d686010f616a1cd8def6449d135b6018b27e7db3493`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/parser/generic_dict_struct_adjacency_spec.spl
mirror: doc/06_spec/01_unit/compiler/parser/generic_dict_struct_adjacency_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=40
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/parser/generic_dict_struct_adjacency_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/parser/generic_dict_struct_adjacency_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/parser/generic_dict_struct_adjacency_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/parser/generic_dict_struct_adjacency_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/parser/generic_dict_struct_adjacency_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses a following top-level struct outside the prior owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/generic_dict_struct_adjacency_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps HIR template maps behind the bootstrap-safe named boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/parser/generic_dict_struct_adjacency_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps backend symbol-name maps behind the bootstrap-safe named boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
