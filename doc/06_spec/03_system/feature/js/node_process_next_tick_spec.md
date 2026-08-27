# Node Process Next Tick Specification

> Tests covering Node.js process.nextTick scheduling.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Node Process Next Tick Specification

## Scenarios

### Node.js process.nextTick scheduling

#### runs process.nextTick callbacks on the runtime drain

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- runs process.nextTick callbacks on the runtime drain
   - Expected: before equals `0`
   - Expected: runtime.drain_due_timers(0) equals `1`
   - Expected: _eval_text(runtime, "tickValue") equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs process.nextTick callbacks on the runtime drain")
var runtime = JsRuntime.new(Logger.new("node-next-tick", LogLevel.Error))
val before = _eval_text(runtime, "var tickValue = 0; process.nextTick(() => {{ tickValue = 7; }}); tickValue")
expect(before).to_equal("0")
expect(runtime.drain_due_timers(0)).to_equal(1)
expect(_eval_text(runtime, "tickValue")).to_equal("7")
```

</details>

#### runs require('process').nextTick callbacks on the runtime drain

- runs require('process').nextTick callbacks on the runtime drain
   - Expected: before equals `0`
   - Expected: runtime.drain_due_timers(0) equals `1`
   - Expected: _eval_text(runtime, "tickValue") equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("runs require('process').nextTick callbacks on the runtime drain")
var runtime = JsRuntime.new(Logger.new("node-next-tick", LogLevel.Error))
val before = _eval_text(runtime, "var tickValue = 0; require('process').nextTick(() => {{ tickValue = 9; }}); tickValue")
expect(before).to_equal("0")
expect(runtime.drain_due_timers(0)).to_equal(1)
expect(_eval_text(runtime, "tickValue")).to_equal("9")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/js/node_process_next_tick_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Node.js process.nextTick scheduling.
- Node.js process.nextTick scheduling

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7d3e85c17c2355463f26f390e5ff9104248f540adbc226813f99833172f30c56`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7d3e85c17c2355463f26f390e5ff9104248f540adbc226813f99833172f30c56`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7d3e85c17c2355463f26f390e5ff9104248f540adbc226813f99833172f30c56`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/feature/js/node_process_next_tick_spec.spl
mirror: doc/06_spec/03_system/feature/js/node_process_next_tick_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/js/node_process_next_tick_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/js/node_process_next_tick_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/js/node_process_next_tick_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/js/node_process_next_tick_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs process.nextTick callbacks on the runtime drain' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/js/node_process_next_tick_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs require('process').nextTick callbacks on the runtime drain' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
