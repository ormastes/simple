# Driver Public Api Split Contract Specification

> Tests covering driver public API split.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Driver Public Api Split Contract Specification

## Scenarios

### driver public API split

#### keeps the compatibility facade bounded

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the compatibility facade bounded


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps the compatibility facade bounded")
val facade = file_read("src/compiler/80.driver/driver_public_api.spl")
val bridge = file_read("src/compiler/80.driver/driver_public_interpret_bridge.spl")
val parser = file_read("src/compiler/80.driver/driver_public_header_parse.spl")
val headers = file_read("src/compiler/80.driver/driver_public_headers.spl")

expect(facade.len()).to_be_less_than(500)
expect(facade).to_contain("driver_public_interpret_bridge")
expect(facade).to_contain("driver_public_headers")
expect(bridge.len()).to_be_less_than(3000)
expect(parser.len()).to_be_less_than(10000)
expect(headers.len()).to_be_less_than(22000)
```

</details>

#### parses exported functions through the extracted model

- parses exported functions through the extracted model
   - Expected: parsed.error equals ``
   - Expected: parsed.exported_functions.len() equals `1`
   - Expected: parsed.exported_functions[0].name equals `add`
   - Expected: parsed.exported_functions[0].params.len() equals `2`
   - Expected: parsed.exported_functions[0].return_type equals `i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses exported functions through the extracted model")
val source = "@export(\"C\")\nfn add(left: i64, right: i64) -> i64:\n    left + right\n"
val parsed = parse_public_exports(source)

expect(parsed.error).to_equal("")
expect(parsed.exported_functions.len()).to_equal(1)
expect(parsed.exported_functions[0].name).to_equal("add")
expect(parsed.exported_functions[0].params.len()).to_equal(2)
expect(parsed.exported_functions[0].return_type).to_equal("i64")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/driver_public_api_split_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering driver public API split.
- driver public API split

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

- Canonical SPipe generation for source `d4192214b04f9d3c17e8eab377507dad3272dff4ce2860078140584960f6ea4b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d4192214b04f9d3c17e8eab377507dad3272dff4ce2860078140584960f6ea4b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d4192214b04f9d3c17e8eab377507dad3272dff4ce2860078140584960f6ea4b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/driver/driver_public_api_split_contract_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/driver_public_api_split_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/driver_public_api_split_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/driver_public_api_split_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/driver_public_api_split_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/driver/driver_public_api_split_contract_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the compatibility facade bounded' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/driver_public_api_split_contract_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses exported functions through the extracted model' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
