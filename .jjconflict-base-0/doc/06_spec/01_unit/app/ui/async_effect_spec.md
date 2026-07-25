# Async Effect Specification

> <details>

<!-- sdn-diagram:id=async_effect_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_effect_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_effect_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_effect_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Effect Specification

## Scenarios

### Effect types

#### creates a FetchData effect

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val effect = Effect.FetchData(url: "https://example.com/api", callback_id: "eff_fetch_cb1")
val desc = describe_effect(effect)
expect desc to_contain "fetch"
expect desc to_contain "https://example.com/api"
expect desc to_contain "eff_fetch_cb1"
```

</details>

#### creates a Timer effect

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val effect = Effect.Timer(delay_ms: 500, callback_id: "eff_timer_cb1")
val desc = describe_effect(effect)
expect desc to_contain "timer"
expect desc to_contain "500"
expect desc to_contain "eff_timer_cb1"
```

</details>

#### creates a Log effect

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val effect = Effect.Log(message: "Widget mounted")
val desc = describe_effect(effect)
expect desc to_contain "log"
expect desc to_contain "Widget mounted"
```

</details>

#### creates an UpdateProp effect

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. expect runner pending count
2. expect runner result count


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runner = new_effect_runner()
expect runner.pending_count() to_equal 0
expect runner.result_count() to_equal 0
```

</details>

#### tracks log messages separately

1. expect runner log count


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runner = new_effect_runner()
expect runner.log_count() to_equal 0
```

</details>

### dispatch_effect

#### adds effect to pending queue

1. runner dispatch effect
2. expect runner pending count


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runner = new_effect_runner()
runner.dispatch_effect(Effect.Log(message: "eff_disp_test"))
expect runner.pending_count() to_equal 1
```

</details>

#### adds multiple effects

1. runner dispatch effect
2. runner dispatch effect
3. runner dispatch effect
4. expect runner pending count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runner = new_effect_runner()
runner.dispatch_effect(Effect.Log(message: "eff_disp_a"))
runner.dispatch_effect(Effect.Timer(delay_ms: 100, callback_id: "eff_disp_t"))
runner.dispatch_effect(Effect.FetchData(url: "http://test.com", callback_id: "eff_disp_f"))
expect runner.pending_count() to_equal 3
```

</details>

### Timer effect processing

#### processes timer and produces result

1. runner dispatch effect
2. runner process effects
3. expect runner pending count
4. expect runner result count


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. runner dispatch effect
2. runner process effects
3. expect runner log count
4. expect runner result count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runner = new_effect_runner()
runner.dispatch_effect(Effect.Log(message: "Hello from lifecycle"))
runner.process_effects()
expect runner.log_count() to_equal 1
expect runner.result_count() to_equal 1
```

</details>

#### processes multiple log effects in order

1. runner dispatch effect
2. runner dispatch effect
3. runner process effects
4. expect runner log count
5. expect runner result count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. runner dispatch effect
2. runner process effects
3. expect runner pending count
4. expect runner result count


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. runner dispatch effect
2. runner process effects
3. expect runner pending count
4. expect runner result count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runner = new_effect_runner()
runner.dispatch_effect(Effect.FetchData(url: "https://api.example.com/data", callback_id: "eff_fd_cb1"))
runner.process_effects()
expect runner.pending_count() to_equal 0
expect runner.result_count() to_equal 1
```

</details>

### EffectRunner clear

#### clears results after processing

1. runner dispatch effect
2. runner process effects
3. expect runner result count
4. runner clear results
5. expect runner result count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runner = new_effect_runner()
runner.dispatch_effect(Effect.Log(message: "eff_clr_test"))
runner.process_effects()
expect runner.result_count() to_equal 1
runner.clear_results()
expect runner.result_count() to_equal 0
```

</details>

#### clears log messages

1. runner dispatch effect
2. runner process effects
3. expect runner log count
4. runner clear log
5. expect runner log count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/app/ui/async_effect_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
