# Query Visibility Domain Blocks Specification

> Tests covering query visibility domain blocks.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Query Visibility Domain Blocks Specification

## Scenarios

### query visibility domain blocks

#### exposes top-level domain blocks as LSP document symbols

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exposes top-level domain blocks as LSP document symbols
   - Expected: symbols.len() equals `3`
   - Expected: symbols[0].name equals `schema" + "{}`
   - Expected: symbols[0].kind equals `domain`
   - Expected: symbol_kind_number(symbols[0].kind) equals `2`
   - Expected: symbols[0].start_col equals `0`
   - Expected: symbols[0].end_col equals `6`
   - Expected: symbol_range_json(symbols[0]) equals `{"start":{"line":0,"character":0},"end":{"line":0,"character":6}}`
   - Expected: symbols[1].name equals `style" + "{}`
   - Expected: symbols[1].kind equals `domain`
   - Expected: symbols[1].start_col equals `0`
   - Expected: symbols[1].end_col equals `5`
   - Expected: symbols[2].name equals `schema`
   - Expected: symbols[2].kind equals `var`
   - Expected: symbols[2].start_col equals `4`
   - Expected: symbols[2].end_col equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes top-level domain blocks as LSP document symbols")
val fixture = domain_fixture()
expect(fixture).to_start_with(cwd() + "/test/fixtures/query/")
val symbols = parse_symbols_in_file(fixture)

expect(symbols.len()).to_equal(3)
expect(symbols[0].name).to_equal("schema" + "{}")
expect(symbols[0].kind).to_equal("domain")
expect(symbol_kind_number(symbols[0].kind)).to_equal(2)
expect(symbols[0].start_col).to_equal(0)
expect(symbols[0].end_col).to_equal(6)
expect(symbol_range_json(symbols[0])).to_equal("{\"start\":{\"line\":0,\"character\":0},\"end\":{\"line\":0,\"character\":6}}")
expect(symbols[1].name).to_equal("style" + "{}")
expect(symbols[1].kind).to_equal("domain")
expect(symbols[1].start_col).to_equal(0)
expect(symbols[1].end_col).to_equal(5)
expect(symbols[2].name).to_equal("schema")
expect(symbols[2].kind).to_equal("var")
expect(symbols[2].start_col).to_equal(4)
expect(symbols[2].end_col).to_equal(10)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/cli/query_visibility_domain_blocks_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering query visibility domain blocks.
- query visibility domain blocks

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

- Canonical SPipe generation for source `38d79325b7a30944d3f749ffe166df837692a7a464a950c3bf7a5bdb557a2a0e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `38d79325b7a30944d3f749ffe166df837692a7a464a950c3bf7a5bdb557a2a0e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `38d79325b7a30944d3f749ffe166df837692a7a464a950c3bf7a5bdb557a2a0e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/app/cli/query_visibility_domain_blocks_spec.spl
mirror: doc/06_spec/unit/app/cli/query_visibility_domain_blocks_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/cli/query_visibility_domain_blocks_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/cli/query_visibility_domain_blocks_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/cli/query_visibility_domain_blocks_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/cli/query_visibility_domain_blocks_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes top-level domain blocks as LSP document symbols' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
