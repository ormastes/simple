# Engine Scripting Facade Specification

> Tests covering gc_async_mut engine scripting facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Scripting Facade Specification

## Scenarios

### gc_async_mut engine scripting facade

#### re-exports visual graph node and connection helpers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports visual graph node and connection helpers
   - Expected: graph.node_count() equals `2`
   - Expected: graph.connect(start, "exec", branch, "exec") is true
   - Expected: graph.connection_count() equals `1`
   - Expected: graph.get_connections_to(branch).length() equals `1`
   - Expected: graph.disconnect(start, branch) is true
   - Expected: graph.connection_count() equals `0`
   - Expected: node.input_count() equals `1`
   - Expected: node.output_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports visual graph node and connection helpers")
var graph = VisualGraph.new("flow")
val start = graph.add_node("event", "Start")
val branch = graph.add_node("branch", "Branch")
expect(graph.node_count()).to_equal(2)
expect(graph.connect(start, "exec", branch, "exec")).to_equal(true)
expect(graph.connection_count()).to_equal(1)
expect(graph.get_connections_to(branch).length()).to_equal(1)
expect(graph.disconnect(start, branch)).to_equal(true)
expect(graph.connection_count()).to_equal(0)

var node = VisualNode.new(7, "custom", "Custom")
node.add_input("in", "float")
node.add_output("out", "float")
expect(node.input_count()).to_equal(1)
expect(node.output_count()).to_equal(1)
```

</details>

#### re-exports built-in node constructors

- re-exports built-in node constructors
   - Expected: event.output_count() equals `1`
   - Expected: branch.input_count() equals `2`
   - Expected: math.output_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports built-in node constructors")
val event = create_event_node(1, "Ready")
expect(event.output_count()).to_equal(1)
val branch = create_branch_node(2)
expect(branch.input_count()).to_equal(2)
val math = create_math_node(3, "add")
expect(math.output_count()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/engine/scripting/engine_scripting_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut engine scripting facade.
- gc_async_mut engine scripting facade

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

- Canonical SPipe generation for source `adb5405a5ec9f28ccb0812c7a98e180db025a7e0ce8247bca2c896924a6b3250`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `adb5405a5ec9f28ccb0812c7a98e180db025a7e0ce8247bca2c896924a6b3250`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `adb5405a5ec9f28ccb0812c7a98e180db025a7e0ce8247bca2c896924a6b3250`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/gc_async_mut/engine/scripting/engine_scripting_facade_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/engine/scripting/engine_scripting_facade_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/engine/scripting/engine_scripting_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/engine/scripting/engine_scripting_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/engine/scripting/engine_scripting_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/gc_async_mut/engine/scripting/engine_scripting_facade_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports visual graph node and connection helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/engine/scripting/engine_scripting_facade_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports built-in node constructors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
