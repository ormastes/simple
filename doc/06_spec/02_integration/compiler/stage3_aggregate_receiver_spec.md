# Stage3 Aggregate Receiver Specification

> Tests covering Stage 3 aggregate method receivers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stage3 Aggregate Receiver Specification

## Scenarios

### Stage 3 aggregate method receivers

#### preserves CompileContext across error_count receiver calls

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves CompileContext across error_count receiver calls
   - Expected: ctx.error_count() equals `0`
   - Expected: ctx.error_count() equals `2`
   - Expected: ctx.error_count_value equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("preserves CompileContext across error_count receiver calls")
var ctx: CompileContext = CompileContext.create(driver_core_compile_options_default())
expect(ctx.error_count()).to_equal(0)
ctx.add_error("first")
ctx.add_error("second")
expect(ctx.error_count()).to_equal(2)
expect(ctx.error_count_value).to_equal(2)
```

</details>

#### preserves an adjacent array-of-aggregate push and field access

- preserves an adjacent array-of-aggregate push and field access
   - Expected: pending.len() equals `2`
   - Expected: selected.key equals `child`
   - Expected: selected.path equals `root.edge`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("preserves an adjacent array-of-aggregate push and field access")
var pending: [Stage3AggregateReceiverAdjacent] = []
pending.push(Stage3AggregateReceiverAdjacent(key: "root", path: ""))
pending.push(Stage3AggregateReceiverAdjacent(key: "child", path: "root.edge"))
val selected: Stage3AggregateReceiverAdjacent = pending[1]
expect(pending.len()).to_equal(2)
expect(selected.key).to_equal("child")
expect(selected.path).to_equal("root.edge")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/stage3_aggregate_receiver_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Stage 3 aggregate method receivers.
- Stage 3 aggregate method receivers

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `08bfd3f040ba6acfdd0c561a10104a6c546bce0a91c4966e616d77e2fb84c03a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `08bfd3f040ba6acfdd0c561a10104a6c546bce0a91c4966e616d77e2fb84c03a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `08bfd3f040ba6acfdd0c561a10104a6c546bce0a91c4966e616d77e2fb84c03a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/02_integration/compiler/stage3_aggregate_receiver_spec.spl
mirror: doc/06_spec/02_integration/compiler/stage3_aggregate_receiver_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/compiler/stage3_aggregate_receiver_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/compiler/stage3_aggregate_receiver_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/compiler/stage3_aggregate_receiver_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/compiler/stage3_aggregate_receiver_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves CompileContext across error_count receiver calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/compiler/stage3_aggregate_receiver_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves an adjacent array-of-aggregate push and field access' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
