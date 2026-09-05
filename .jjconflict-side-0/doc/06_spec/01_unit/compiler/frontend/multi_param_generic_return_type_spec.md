# Multi-Parameter Generic Return Type

> A generic return annotation with multiple type parameters, e.g.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multi-Parameter Generic Return Type

A generic return annotation with multiple type parameters, e.g.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/multi_param_generic_return_type_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

A generic return annotation with multiple type parameters, e.g.
`-> Result<i64, text>`, parses like any other type annotation. Filed as an
open defect 2026-08-11 ("expected expression, found Lt") but did not
reproduce against a fresh seed build off that day's origin tip — see
doc/08_tracking/bug/generic_return_type_annotation_rejected_2026-08-11.md.
This spec pins the parsed shape so a future regression is caught here.

## Scenarios

### multi-parameter generic return annotations

#### preserves a Result<T, E> return annotation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves a Result<T, E> return annotation
- Parse a function returning Result<i64, text>
- Confirm the return annotation survived parsing
   - Expected: module.functions.contains_key("f") is true
   - Expected: module.functions["f"].has_return_type is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves a Result<T, E> return annotation")
step("Parse a function returning Result<i64, text>")
val module = parse_full_frontend(
    "fn f() -> Result<i64, text>:\n    return Ok(1)",
    "multi_param_generic_return",
    "multi_param_generic_return",
    Logger(level: 0)
)

step("Confirm the return annotation survived parsing")
expect(module.functions.contains_key("f")).to_equal(true)
expect(module.functions["f"].has_return_type).to_equal(true)
```

</details>

#### preserves a nested Result<List<i64>, text> return annotation

- preserves a nested Result<List<i64>, text> return annotation
- Parse a function returning a nested generic Result
- Confirm the nested return annotation survived parsing
   - Expected: module.functions.contains_key("g") is true
   - Expected: module.functions["g"].has_return_type is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves a nested Result<List<i64>, text> return annotation")
step("Parse a function returning a nested generic Result")
val module = parse_full_frontend(
    "fn g() -> Result<List<i64>, text>:\n    return Ok([1])",
    "multi_param_generic_return_nested",
    "multi_param_generic_return_nested",
    Logger(level: 0)
)

step("Confirm the nested return annotation survived parsing")
expect(module.functions.contains_key("g")).to_equal(true)
expect(module.functions["g"].has_return_type).to_equal(true)
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ad4e4e725c1c4762e73323b13dfe7a6a82d7c1f950260cd25b73fe049279df8e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ad4e4e725c1c4762e73323b13dfe7a6a82d7c1f950260cd25b73fe049279df8e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ad4e4e725c1c4762e73323b13dfe7a6a82d7c1f950260cd25b73fe049279df8e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/compiler/frontend/multi_param_generic_return_type_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/multi_param_generic_return_type_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/multi_param_generic_return_type_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/multi_param_generic_return_type_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/multi_param_generic_return_type_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves a Result<T, E> return annotation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/multi_param_generic_return_type_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves a nested Result<List<i64>, text> return annotation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
