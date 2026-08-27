# Driver Collect Sources Single Definition Specification

> Tests covering driver source collection has exactly one definition.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Driver Collect Sources Single Definition Specification

## Scenarios

### driver source collection has exactly one definition

#### collapses driver_helpers.spl so only one collector definition remains

- collapses driver_helpers.spl so only one collector definition remains
- Read both driver source-collection modules
- The canonical collector lives in driver_source_loading.spl
- driver_helpers.spl declares no competing definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("collapses driver_helpers.spl so only one collector definition remains")
step("Read both driver source-collection modules")
val loading = rt_file_read_text(LOADING) ?? ""
val helpers = rt_file_read_text(HELPERS) ?? ""
expect(loading).to_not_equal("")
expect(helpers).to_not_equal("")

step("The canonical collector lives in driver_source_loading.spl")
expect(loading).to_contain("pub fn _driver_collect_sources(p: text) -> [SourceFile]:")
expect(loading).to_contain("pub fn _driver_collect_sources_via_find(paths: [text]) -> [SourceFile]:")

step("driver_helpers.spl declares no competing definition")
expect(helpers).to_not_contain("fn _driver_collect_sources(p: text) -> [SourceFile]:")
expect(helpers).to_not_contain("fn _driver_collect_sources_via_find(paths: [text]) -> [SourceFile]:")
```

</details>

#### applies the four lane exclusions that only the winning copy carries

- applies the four lane exclusions that only the winning copy carries
- Interpreter, parser, treesitter and async-lowering paths are dropped
   - Expected: _driver_collect_sources("src/compiler/10.frontend/core/interpreter/hashmap.spl").len() equals `0`
- A positive control from the same layer is still collected


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies the four lane exclusions that only the winning copy carries")
step("Interpreter, parser, treesitter and async-lowering paths are dropped")
expect(_driver_collect_sources("src/compiler/10.frontend/core/interpreter/hashmap.spl").len()).to_equal(0)

step("A positive control from the same layer is still collected")
val control = _driver_collect_sources("src/compiler/10.frontend/core/lexer.spl")
expect(control.len()).to_be_greater_than(0)
```

</details>

#### keeps the exclusion list intact in the definition that actually answers

- keeps the exclusion list intact in the definition that actually answers
- Both collector branches carry all four excluded path fragments


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the exclusion list intact in the definition that actually answers")
step("Both collector branches carry all four excluded path fragments")
val loading = rt_file_read_text(LOADING) ?? ""
expect(loading).to_contain("/core/interpreter/")
expect(loading).to_contain("/10.frontend/parser/")
expect(loading).to_contain("/10.frontend/treesitter")
expect(loading).to_contain("/hir_lowering/async")
```

</details>

#### routes the bulk find collector through the same single definition

- routes the bulk find collector through the same single definition
- via_find delegates rather than re-implementing the filter
- Delegation is observable: an excluded path yields nothing
   - Expected: _driver_collect_sources_via_find(["src/compiler/10.frontend/core/interpreter"]).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes the bulk find collector through the same single definition")
step("via_find delegates rather than re-implementing the filter")
val loading = rt_file_read_text(LOADING) ?? ""
expect(loading).to_contain("for path in paths:\n        val loaded = _driver_collect_sources(path)")

step("Delegation is observable: an excluded path yields nothing")
expect(_driver_collect_sources_via_find(["src/compiler/10.frontend/core/interpreter"]).len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/driver/driver_collect_sources_single_definition_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering driver source collection has exactly one definition.
- driver source collection has exactly one definition

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `8ccbe9acd06528f8be6131530b6f07f503316ecd9f15a92c6b61e682b00f9c32`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8ccbe9acd06528f8be6131530b6f07f503316ecd9f15a92c6b61e682b00f9c32`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8ccbe9acd06528f8be6131530b6f07f503316ecd9f15a92c6b61e682b00f9c32`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/compiler/driver/driver_collect_sources_single_definition_spec.spl
mirror: doc/06_spec/unit/compiler/driver/driver_collect_sources_single_definition_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/driver/driver_collect_sources_single_definition_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/driver/driver_collect_sources_single_definition_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/driver/driver_collect_sources_single_definition_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/driver/driver_collect_sources_single_definition_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collapses driver_helpers.spl so only one collector definition remains' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/driver/driver_collect_sources_single_definition_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies the four lane exclusions that only the winning copy carries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/driver/driver_collect_sources_single_definition_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the exclusion list intact in the definition that actually answers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
