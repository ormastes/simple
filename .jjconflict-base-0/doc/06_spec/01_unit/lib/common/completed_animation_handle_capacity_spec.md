# completed_animation_handle_capacity_spec

> Completed animation handles must not bypass the shared JS task bound.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# completed_animation_handle_capacity_spec

Completed animation handles must not bypass the shared JS task bound.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/completed_animation_handle_capacity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Completed animation handles must not bypass the shared JS task bound.

## Scenarios

### JavaScript completed animation handle capacity

#### should reject completed animation refresh when the task queue is full

- should reject completed animation refresh when the task queue is full
   - Text capture: after_step
- Complete one requestAnimationFrame handle
   - Text capture: after_step
   - Evidence: text output verified by 4 expected checks
   - Expected: runtime.drain_due_timers(16) equals `1`
   - Expected: runtime.interpreter.pending_timer_tasks.len() equals `0`
   - Expected: runtime.interpreter.timer_handle_ids.len() equals `0`
   - Expected: runtime.interpreter.timer_handle_object_ids.len() equals `0`
- Fill the canonical timer and animation task queue
   - Text capture: after_step
   - Evidence: text output verified by 3 expected checks
   - Expected: denied equals `0.0`
   - Expected: runtime.interpreter.pending_timer_tasks.len() equals `4096`
   - Expected: runtime.interpreter.timer_handle_ids.len() equals `4096`
- Refresh the completed animation handle without exceeding capacity
   - Text capture: after_step
   - Evidence: text output verified by 3 expected checks
   - Expected: runtime.interpreter.pending_timer_tasks.len() equals `4096`
   - Expected: runtime.interpreter.timer_handle_ids.len() equals `4096`
   - Expected: state equals `1:false:false:true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should reject completed animation refresh when the task queue is full")
step("Complete one requestAnimationFrame handle")
var runtime = JsRuntime.new(
    Logger.new("completed-animation-capacity", LogLevel.Error)
)
expect(runtime.eval(
    "var frames = 0; var completedFrame = " +
    "requestAnimationFrame(function() { frames = frames + 1; });"
).is_ok()).to_equal(true)
expect(runtime.drain_due_timers(16)).to_equal(1)
expect(runtime.interpreter.pending_timer_tasks.len()).to_equal(0)
expect(runtime.interpreter.timer_handle_ids.len()).to_equal(0)
expect(runtime.interpreter.timer_handle_object_ids.len()).to_equal(0)

step("Fill the canonical timer and animation task queue")
match runtime.eval(
    "var denied = 0; for (var i = 0; i < 4096; i = i + 1) {" +
    " if (setTimeout(function() {}, 1000) === undefined) {" +
    " denied = denied + 1; } } denied"
):
    Ok(JsValue.Number(denied)):
        expect(denied).to_equal(0.0)
    _:
        fail("Expected the canonical task queue to reach capacity")
expect(runtime.interpreter.pending_timer_tasks.len()).to_equal(4096)
expect(runtime.interpreter.timer_handle_ids.len()).to_equal(4096)
expect(
    runtime.interpreter.timer_handle_object_ids.len()
).to_equal(4096)

step("Refresh the completed animation handle without exceeding capacity")
expect(runtime.eval(
    "completedFrame.refresh() === completedFrame"
).is_ok()).to_equal(true)
expect(runtime.interpreter.pending_timer_tasks.len()).to_equal(4096)
expect(runtime.interpreter.timer_handle_ids.len()).to_equal(4096)
expect(
    runtime.interpreter.timer_handle_object_ids.len()
).to_equal(4096)
match runtime.eval(
    "frames + ':' + completedFrame.refreshed + ':' +" +
    " completedFrame.active + ':' + completedFrame.completed"
):
    Ok(JsValue.String(state)):
        expect(state).to_equal("1:false:false:true")
    _:
        fail("Expected the completed animation handle to remain retired")
```

</details>

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5f7aed9b706d5286962be5b98f78a86ced4d54b1efe6cf98dc506b18122bd543`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5f7aed9b706d5286962be5b98f78a86ced4d54b1efe6cf98dc506b18122bd543`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5f7aed9b706d5286962be5b98f78a86ced4d54b1efe6cf98dc506b18122bd543`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/completed_animation_handle_capacity_spec.spl
mirror: doc/06_spec/01_unit/lib/common/completed_animation_handle_capacity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=95 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/completed_animation_handle_capacity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/completed_animation_handle_capacity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/completed_animation_handle_capacity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/completed_animation_handle_capacity_spec.spl:22:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject completed animation refresh when the task queue is full' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/completed_animation_handle_capacity_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject completed animation refresh when the task queue is full' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
