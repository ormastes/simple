# Frontend Collection Desugar Start Specification

> Tests covering frontend collection desugar start index.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Frontend Collection Desugar Start Specification

## Scenarios

### frontend collection desugar start index

#### keeps parse_full_frontend domain-block receiver mutable

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps parse_full_frontend domain-block receiver mutable
   - Expected: source does not contain `val module = parse_and_build_module`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("keeps parse_full_frontend domain-block receiver mutable")
val source = file_read("src/compiler/10.frontend/frontend.spl")

expect(source.contains("val module = parse_and_build_module")).to_equal(false)
expect(source).to_contain("var module = parse_and_build_module")
expect(source).to_contain("module.domain_blocks = domain_blocks")
```

</details>

#### desugars collection patterns after a larger previous parse

- desugars collection patterns after a larger previous parse
   - Expected: large.functions contains `filler_11`
   - Expected: small.functions contains `append_one`
   - Expected: small.exports.len() equals `1`
   - Expected: small.exports[0].items equals `["append_one"]`
   - Expected: collection_desugar_rewrite_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("desugars collection patterns after a larger previous parse")
val log = frontend_desugar_start_logger()
val large = parse_full_frontend(frontend_desugar_large_source(), "large_frontend_desugar.spl", "large_frontend_desugar", log)
expect(large.functions.contains("filler_11")).to_equal(true)

val small_source = "fn append_one() -> [i64]:\n    var xs = [1]\n    xs = xs + [2]\n    xs\nexport append_one\n"
val small = parse_full_frontend(small_source, "small_frontend_desugar.spl", "small_frontend_desugar", log)

expect(small.functions.contains("append_one")).to_equal(true)
expect(small.exports.len()).to_equal(1)
expect(small.exports[0].items).to_equal(["append_one"])
expect(collection_desugar_rewrite_count()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/frontend_collection_desugar_start_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering frontend collection desugar start index.
- frontend collection desugar start index

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
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9e270992a9e7a97c91e53ae50c3b804370bc3e7f8c1d80f1ad0a8c8a917050bc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9e270992a9e7a97c91e53ae50c3b804370bc3e7f8c1d80f1ad0a8c8a917050bc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9e270992a9e7a97c91e53ae50c3b804370bc3e7f8c1d80f1ad0a8c8a917050bc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **74/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/frontend/frontend_collection_desugar_start_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/frontend_collection_desugar_start_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=30
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=74; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/frontend/frontend_collection_desugar_start_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/frontend_collection_desugar_start_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/frontend_collection_desugar_start_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/frontend/frontend_collection_desugar_start_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/frontend/frontend_collection_desugar_start_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/frontend/frontend_collection_desugar_start_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps parse_full_frontend domain-block receiver mutable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/frontend_collection_desugar_start_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'desugars collection patterns after a larger previous parse' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
