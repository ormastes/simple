# Claude Full Grove Component

> Checks modern SSpec parity for Grove tree state, rendering, and navigation helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Grove Component

Checks modern SSpec parity for Grove tree state, rendering, and navigation helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/grove_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for Grove tree state, rendering, and navigation helpers.

## Scenarios

### Claude full Grove component

#### should render sample grove rows and breadcrumbs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should render sample grove rows and breadcrumbs
- Create sample Grove model


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should render sample grove rows and breadcrumbs")
step("Create sample Grove model")
val roots = sampleGroveNodes()
val grove = createGrove(roots)
expect(grove.render()).to_contain("Grove")
expect(grove.activeBreadcrumbs().len()).to_be_greater_than(0)
```

</details>

#### should navigate and filter grove nodes

- should navigate and filter grove nodes
- Navigate visible rows
   - Expected: selectNextGroveNode(roots, state).activeId equals `workspace`
   - Expected: handleGroveKey(roots, state, "end").activeId equals `workspace`
- Filter by query


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should navigate and filter grove nodes")
step("Navigate visible rows")
val roots = sampleGroveNodes()
val state = GroveState.empty()
expect(selectNextGroveNode(roots, state).activeId).to_equal("workspace")
expect(handleGroveKey(roots, state, "end").activeId).to_equal("workspace")

step("Filter by query")
val filtered = GroveState.empty().withQuery("Grove")
expect(renderGrove(roots, filtered)).to_contain("Grove.spl")
```

</details>

#### should check modeled TypeScript source floor

- should check modeled TypeScript source floor
- Read Grove source helper
   - Expected: groveSourceLinesModeled() equals `462`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should check modeled TypeScript source floor")
step("Read Grove source helper")
expect(groveSourceLinesModeled()).to_equal(462)
```

</details>

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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `29fd7bd87c156abe2723b28f74a896b0aeb3c2658fb0cbf25277bc3bcf6738cb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `29fd7bd87c156abe2723b28f74a896b0aeb3c2658fb0cbf25277bc3bcf6738cb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `29fd7bd87c156abe2723b28f74a896b0aeb3c2658fb0cbf25277bc3bcf6738cb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/components/grove_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/components/grove_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/components/grove_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/components/grove_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/components/grove_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/components/grove_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should render sample grove rows and breadcrumbs' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/components/grove_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should render sample grove rows and breadcrumbs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/grove_spec.spl:27:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should navigate and filter grove nodes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/components/grove_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should navigate and filter grove nodes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/grove_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should check modeled TypeScript source floor' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/components/grove_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should check modeled TypeScript source floor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
