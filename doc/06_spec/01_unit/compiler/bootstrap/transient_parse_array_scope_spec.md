# Transient Parse Array Scope Specification

> Tests covering flat parser transient array scope.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Transient Parse Array Scope Specification

## Scenarios

### flat parser transient array scope

#### reclaims parse arrays only after owned module conversion starts

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reclaims parse arrays only after owned module conversion starts


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reclaims parse arrays only after owned module conversion starts")
val source = file_read("src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl")
val fn_pos = source.find("fn parse_and_build_module(source: text, path: text) -> Module:")
val body = if fn_pos >= 0: source.substring(fn_pos, source.len()) else: ""
val begin_pos = body.find("val transient_scope = rt_transient_array_scope_begin()")
val parse_pos = body.find("parse_module_body()", begin_pos)
val desugar_pos = body.find("desugar_collections(0, 0)", parse_pos)
val pause_pos = body.find("rt_transient_array_scope_pause()", desugar_pos)
val convert_pos = body.find("val built_module = flat_ast_to_module(path)", pause_pos)
val end_pos = body.find("rt_transient_array_scope_end()", convert_pos)

expect(fn_pos).to_be_greater_than(0)
expect(begin_pos).to_be_greater_than(0)
expect(parse_pos).to_be_greater_than(begin_pos)
expect(desugar_pos).to_be_greater_than(parse_pos)
expect(pause_pos).to_be_greater_than(desugar_pos)
expect(convert_pos).to_be_greater_than(pause_pos)
expect(end_pos).to_be_greater_than(convert_pos)
```

</details>

#### does not run the arena rewrite after transient arrays are reclaimed

- does not run the arena rewrite after transient arrays are reclaimed
   - Expected: source does not contain `desugar_collections(0, 0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not run the arena rewrite after transient arrays are reclaimed")
val source = file_read("src/compiler/10.frontend/frontend.spl")
expect(source.contains("desugar_collections(0, 0)")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/bootstrap/transient_parse_array_scope_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering flat parser transient array scope.
- flat parser transient array scope

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

- Canonical SPipe generation for source `2949df2598bdf197bfae38ede49f0960aaadfa36007ead9413246cd415c77098`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2949df2598bdf197bfae38ede49f0960aaadfa36007ead9413246cd415c77098`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2949df2598bdf197bfae38ede49f0960aaadfa36007ead9413246cd415c77098`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/bootstrap/transient_parse_array_scope_spec.spl
mirror: doc/06_spec/01_unit/compiler/bootstrap/transient_parse_array_scope_spec.md (current)
findings: 6 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/bootstrap/transient_parse_array_scope_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/bootstrap/transient_parse_array_scope_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/bootstrap/transient_parse_array_scope_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/bootstrap/transient_parse_array_scope_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/bootstrap/transient_parse_array_scope_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reclaims parse arrays only after owned module conversion starts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/bootstrap/transient_parse_array_scope_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not run the arena rewrite after transient arrays are reclaimed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
