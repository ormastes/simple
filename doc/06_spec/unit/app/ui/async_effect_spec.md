# Async Effect Specification

> Tests covering Effect types, EffectRunner channels, dispatch_effect, Timer effect processing, Log effect processing, UpdateProp effect processing, FetchData effect processing, EffectRunner clear.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Effect Specification

## Scenarios

### Effect types

#### creates a FetchData effect

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates a FetchData effect


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a FetchData effect")
val effect = Effect.FetchData(url: "https://example.com/api", callback_id: "eff_fetch_cb1")
val desc = describe_effect(effect)
expect desc to_contain "fetch"
expect desc to_contain "https://example.com/api"
expect desc to_contain "eff_fetch_cb1"
```

</details>

#### creates a Timer effect

- creates a Timer effect


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a Timer effect")
val effect = Effect.Timer(delay_ms: 500, callback_id: "eff_timer_cb1")
val desc = describe_effect(effect)
expect desc to_contain "timer"
expect desc to_contain "500"
expect desc to_contain "eff_timer_cb1"
```

</details>

#### creates a Log effect

- creates a Log effect


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a Log effect")
val effect = Effect.Log(message: "Widget mounted")
val desc = describe_effect(effect)
expect desc to_contain "log"
expect desc to_contain "Widget mounted"
```

</details>

#### creates an UpdateProp effect

- creates an UpdateProp effect


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates an UpdateProp effect")
val effect = Effect.UpdateProp(widget_id: "eff_upw1", key: "content", value: "Updated text")
val desc = describe_effect(effect)
expect desc to_contain "update_prop"
expect desc to_contain "eff_upw1"
expect desc to_contain "content"
expect desc to_contain "Updated text"
```

</details>

### EffectRunner channels

#### starts with empty pending and result queues

- starts with empty pending and result queues


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with empty pending and result queues")
val runner = new_effect_runner()
expect runner.pending_count() to_equal 0
expect runner.result_count() to_equal 0
```

</details>

#### tracks log messages separately

- tracks log messages separately


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks log messages separately")
val runner = new_effect_runner()
expect runner.log_count() to_equal 0
```

</details>

### dispatch_effect

#### adds effect to pending queue

- adds effect to pending queue


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds effect to pending queue")
val runner = new_effect_runner()
runner.dispatch_effect(Effect.Log(message: "eff_disp_test"))
expect runner.pending_count() to_equal 1
```

</details>

#### adds multiple effects

- adds multiple effects


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds multiple effects")
val runner = new_effect_runner()
runner.dispatch_effect(Effect.Log(message: "eff_disp_a"))
runner.dispatch_effect(Effect.Timer(delay_ms: 100, callback_id: "eff_disp_t"))
runner.dispatch_effect(Effect.FetchData(url: "http://test.com", callback_id: "eff_disp_f"))
expect runner.pending_count() to_equal 3
```

</details>

### Timer effect processing

#### processes timer and produces result

- processes timer and produces result


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("processes timer and produces result")
val runner = new_effect_runner()
runner.dispatch_effect(Effect.Timer(delay_ms: 250, callback_id: "eff_tmr_cb1"))
runner.process_effects()
expect runner.pending_count() to_equal 0
expect runner.result_count() to_equal 1
val result = runner.last_result()
expect result != nil to_equal true
```

</details>

### Log effect processing

#### processes log and records message

- processes log and records message


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("processes log and records message")
val runner = new_effect_runner()
runner.dispatch_effect(Effect.Log(message: "Hello from lifecycle"))
runner.process_effects()
expect runner.log_count() to_equal 1
expect runner.result_count() to_equal 1
```

</details>

#### processes multiple log effects in order

- processes multiple log effects in order


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("processes multiple log effects in order")
val runner = new_effect_runner()
runner.dispatch_effect(Effect.Log(message: "eff_log_first"))
runner.dispatch_effect(Effect.Log(message: "eff_log_second"))
runner.process_effects()
expect runner.log_count() to_equal 2
expect runner.result_count() to_equal 2
```

</details>

### UpdateProp effect processing

#### processes update_prop and produces result

- processes update_prop and produces result


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("processes update_prop and produces result")
val runner = new_effect_runner()
runner.dispatch_effect(Effect.UpdateProp(widget_id: "eff_up_w1", key: "label", value: "New Label"))
runner.process_effects()
expect runner.pending_count() to_equal 0
expect runner.result_count() to_equal 1
val result = runner.last_result()
expect result != nil to_equal true
```

</details>

### FetchData effect processing

#### processes fetch and produces result with url

- processes fetch and produces result with url


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("processes fetch and produces result with url")
val runner = new_effect_runner()
runner.dispatch_effect(Effect.FetchData(url: "https://api.example.com/data", callback_id: "eff_fd_cb1"))
runner.process_effects()
expect runner.pending_count() to_equal 0
expect runner.result_count() to_equal 1
```

</details>

### EffectRunner clear

#### clears results after processing

- clears results after processing


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears results after processing")
val runner = new_effect_runner()
runner.dispatch_effect(Effect.Log(message: "eff_clr_test"))
runner.process_effects()
expect runner.result_count() to_equal 1
runner.clear_results()
expect runner.result_count() to_equal 0
```

</details>

#### clears log messages

- clears log messages


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears log messages")
val runner = new_effect_runner()
runner.dispatch_effect(Effect.Log(message: "eff_clr_log"))
runner.process_effects()
expect runner.log_count() to_equal 1
runner.clear_log()
expect runner.log_count() to_equal 0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/async_effect_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Effect types, EffectRunner channels, dispatch_effect, Timer effect processing, Log effect processing, UpdateProp effect processing, FetchData effect processing, EffectRunner clear.
- Effect types
- EffectRunner channels
- dispatch_effect
- Timer effect processing
- Log effect processing
- UpdateProp effect processing
- FetchData effect processing
- EffectRunner clear

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `49e9dad1bdf1427a791ef81cd40c385943b555fe0abd4bc16d211373e44efd8b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `49e9dad1bdf1427a791ef81cd40c385943b555fe0abd4bc16d211373e44efd8b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `49e9dad1bdf1427a791ef81cd40c385943b555fe0abd4bc16d211373e44efd8b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/async_effect_spec.spl
mirror: doc/06_spec/unit/app/ui/async_effect_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/async_effect_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/async_effect_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/async_effect_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a FetchData effect' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/async_effect_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a Timer effect' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/async_effect_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a Log effect' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
