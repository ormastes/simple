# Node Process Next Tick Specification

## Scenarios

### Node.js process.nextTick scheduling

#### runs process.nextTick callbacks on the runtime drain

1. var runtime = JsRuntime new
   - Expected: before equals `0`
   - Expected: runtime.drain_due_timers(0) equals `1`
   - Expected: _eval_text(runtime, "tickValue") equals `7`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var runtime = JsRuntime.new(Logger.new(LogLevel.Error))
val before = _eval_text(runtime, "var tickValue = 0; process.nextTick(() => { tickValue = 7; }); tickValue")
expect(before).to_equal("0")
expect(runtime.drain_due_timers(0)).to_equal(1)
expect(_eval_text(runtime, "tickValue")).to_equal("7")
```

</details>

#### runs require('process').nextTick callbacks on the runtime drain

1. var runtime = JsRuntime new
   - Expected: before equals `0`
   - Expected: runtime.drain_due_timers(0) equals `1`
   - Expected: _eval_text(runtime, "tickValue") equals `9`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var runtime = JsRuntime.new(Logger.new(LogLevel.Error))
val before = _eval_text(runtime, "var tickValue = 0; require('process').nextTick(() => { tickValue = 9; }); tickValue")
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
| Source | `test/feature/js/node_process_next_tick_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Node.js process.nextTick scheduling

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

