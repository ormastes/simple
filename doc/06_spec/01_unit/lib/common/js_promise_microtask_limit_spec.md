# Js Promise Microtask Limit Specification

> Tests covering JavaScript Promise microtask limits.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Js Promise Microtask Limit Specification

## Scenarios

### JavaScript Promise microtask limits

#### yields without discarding queued Promise callbacks

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- yields without discarding queued Promise callbacks
   - Expected: scheduled.is_ok() is true
   - Expected: resolved.is_ok() is true
   - Expected: runtime.drain_pending_microtasks() is true
   - Expected: runtime.interpreter.pending_promise_tasks.len() equals `1`
   - Expected: runtime.interpreter.pending_promise_task_head equals `0`
   - Expected: hits equals `1000.0`
   - Expected: runtime.drain_pending_microtasks() is true
   - Expected: runtime.interpreter.pending_promise_tasks.len() equals `0`
   - Expected: runtime.interpreter.pending_promise_task_head equals `0`
   - Expected: hits equals `1001.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("yields without discarding queued Promise callbacks")
var runtime = JsRuntime.new(Logger.new("promise-limit", LogLevel.Error))
val scheduled = runtime.eval(
    "var hits = 0; var pending = fetch('https://example.test/'); for (var i = 0; i < 1001; i = i + 1) { pending.then(function() { hits = hits + 1; }); }"
)
expect(scheduled.is_ok()).to_equal(true)

var interpreter = runtime.interpreter
val resolved = interpreter.resolve_async_fetch_response(
    "fetch-1", "https://example.test/", 200, "", "ok", ""
)
expect(resolved.is_ok()).to_equal(true)
runtime.interpreter = interpreter

expect(runtime.drain_pending_microtasks()).to_equal(true)
expect(runtime.interpreter.pending_promise_tasks.len()).to_equal(1)
expect(runtime.interpreter.pending_promise_task_head).to_equal(0)
match runtime.eval("hits"):
    Ok(JsValue.Number(hits)):
        expect(hits).to_equal(1000.0)
    _:
        fail("Expected first bounded Promise drain")

expect(runtime.drain_pending_microtasks()).to_equal(true)
expect(runtime.interpreter.pending_promise_tasks.len()).to_equal(0)
expect(runtime.interpreter.pending_promise_task_head).to_equal(0)
match runtime.eval("hits"):
    Ok(JsValue.Number(hits)):
        expect(hits).to_equal(1001.0)
    _:
        fail("Expected retained Promise callback")
```

</details>

#### bounds retained pending Promise handlers

- bounds retained pending Promise handlers
   - Expected: scheduled.is_ok() is true
   - Expected: runtime.interpreter.promise_handlers.len() equals `4096`
   - Expected: runtime.interpreter.promise_handler_registrations.len() equals `4096`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("bounds retained pending Promise handlers")
var runtime = JsRuntime.new(Logger.new("promise-limit", LogLevel.Error))
val scheduled = runtime.eval(
    "var pending = fetch('https://example.test/'); for (var i = 0; i < 4100; i = i + 1) { pending.then(function() {}); }"
)
expect(scheduled.is_ok()).to_equal(true)
expect(runtime.interpreter.promise_handlers.len()).to_equal(4096)
expect(runtime.interpreter.promise_handler_registrations.len()).to_equal(4096)
```

</details>

#### defers settled reactions then releases completed handler records

- defers settled reactions then releases completed handler records
   - Expected: completed.is_ok() is true
   - Expected: runtime.interpreter.promise_handlers.len() equals `8`
   - Expected: hits equals `0.0`
   - Expected: runtime.drain_pending_microtasks() is true
   - Expected: hits equals `8.0`
   - Expected: runtime.interpreter.promise_handlers.len() equals `0`
   - Expected: runtime.interpreter.promise_handler_registrations.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("defers settled reactions then releases completed handler records")
var runtime = JsRuntime.new(Logger.new("promise-limit", LogLevel.Error))
val completed = runtime.eval(
    "var hits = 0; for (var i = 0; i < 8; i = i + 1) { Promise.resolve(i).then(function() { hits = hits + 1; }); }"
)
expect(completed.is_ok()).to_equal(true)
expect(runtime.interpreter.promise_handlers.len()).to_equal(8)
match runtime.eval("hits"):
    Ok(JsValue.Number(hits)):
        expect(hits).to_equal(0.0)
    _:
        fail("Expected deferred Promise reactions")

expect(runtime.drain_pending_microtasks()).to_equal(true)
match runtime.eval("hits"):
    Ok(JsValue.Number(hits)):
        expect(hits).to_equal(8.0)
    _:
        fail("Expected drained Promise reactions")
expect(runtime.interpreter.promise_handlers.len()).to_equal(0)
expect(runtime.interpreter.promise_handler_registrations.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/js_promise_microtask_limit_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering JavaScript Promise microtask limits.
- JavaScript Promise microtask limits

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a8b7fdcff11e6d85e1213102f6937ca580dfd9e85ea289a55a0fbfbc3c66292d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a8b7fdcff11e6d85e1213102f6937ca580dfd9e85ea289a55a0fbfbc3c66292d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a8b7fdcff11e6d85e1213102f6937ca580dfd9e85ea289a55a0fbfbc3c66292d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/js_promise_microtask_limit_spec.spl
mirror: doc/06_spec/01_unit/lib/common/js_promise_microtask_limit_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/js_promise_microtask_limit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/js_promise_microtask_limit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/js_promise_microtask_limit_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 13 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/js_promise_microtask_limit_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'yields without discarding queued Promise callbacks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/js_promise_microtask_limit_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bounds retained pending Promise handlers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/js_promise_microtask_limit_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defers settled reactions then releases completed handler records' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
