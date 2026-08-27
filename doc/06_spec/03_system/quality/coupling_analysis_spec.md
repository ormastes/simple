# Coupling Analysis Specification

> Tests covering Coupling Analysis.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Coupling Analysis Specification

## Scenarios

### Coupling Analysis

#### computes coupling metrics for a dependency graph

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- computes coupling metrics for a dependency graph
   - Expected: metrics.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes coupling metrics for a dependency graph")
var edges: Dict<text, [text]> = {}
edges = edges.set("app", ["lib", "compiler"])
edges = edges.set("lib", [])
edges = edges.set("compiler", ["lib"])

val metrics = compute_all_metrics(graph(edges))

expect(metrics.len()).to_equal(3)
expect(metrics[0].module_name.len()).to_be_greater_than(0)
```

</details>

#### detects cohesion split with LCOM4

- detects cohesion split with LCOM4
   - Expected: result.method_count equals `3`
   - Expected: result.lcom4 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects cohesion split with LCOM4")
val methods = [
    method_access("read", ["path"], []),
    method_access("write", ["path"], []),
    method_access("render", ["canvas"], [])
]

val result = compute_lcom4("QualitySmoke", methods)

expect(result.method_count).to_equal(3)
expect(result.lcom4).to_equal(2)
```

</details>

#### flags lower layer importing a higher layer

- flags lower layer importing a higher layer
   - Expected: violations.len() equals `1`
   - Expected: violations[0].from_layer equals `10`
   - Expected: violations[0].to_layer equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("flags lower layer importing a higher layer")
var edges: Dict<text, [text]> = {}
edges = edges.set("compiler/10.frontend/parser", ["compiler/30.types/checker"])
edges = edges.set("compiler/30.types/checker", [])

val violations = find_layer_violations(graph(edges))

expect(violations.len()).to_equal(1)
expect(violations[0].from_layer).to_equal(10)
expect(violations[0].to_layer).to_equal(30)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/quality/coupling_analysis_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Coupling Analysis.
- Coupling Analysis

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

- `REQ-SSPEC-SYSTEM`
- `REQ-coupling-analysis`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `28161388033fffebc5632e049aa52f94eb2a3b905155b06e6e9a7917a43f9aa7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `28161388033fffebc5632e049aa52f94eb2a3b905155b06e6e9a7917a43f9aa7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `28161388033fffebc5632e049aa52f94eb2a3b905155b06e6e9a7917a43f9aa7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/quality/coupling_analysis_spec.spl
mirror: doc/06_spec/03_system/quality/coupling_analysis_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/quality/coupling_analysis_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/quality/coupling_analysis_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/quality/coupling_analysis_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/quality/coupling_analysis_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/quality/coupling_analysis_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes coupling metrics for a dependency graph' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/quality/coupling_analysis_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects cohesion split with LCOM4' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/quality/coupling_analysis_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags lower layer importing a higher layer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
