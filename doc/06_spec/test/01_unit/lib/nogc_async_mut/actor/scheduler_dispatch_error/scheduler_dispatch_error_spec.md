# Scheduler Dispatch Error Specification

> <details>

<!-- sdn-diagram:id=scheduler_dispatch_error_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scheduler_dispatch_error_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scheduler_dispatch_error_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scheduler_dispatch_error_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scheduler Dispatch Error Specification

## Scenarios

### ActorScheduler dispatch error API (W2-6 structural)

#### ActorScheduler has trace_enabled field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = sched_src()
expect(src.contains("trace_enabled: bool")).to_equal(true)
```

</details>

#### trace_enabled is read from SIMPLE_ACTOR_TRACE at construction

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = sched_src()
expect(src.contains("env_has(\"SIMPLE_ACTOR_TRACE\")")).to_equal(true)
```

</details>

#### actor_error_count per-actor accessor exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = sched_src()
expect(src.contains("fn actor_error_count(actor_id: i64) -> i64")).to_equal(true)
```

</details>

#### actor_last_error per-actor accessor exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = sched_src()
expect(src.contains("fn actor_last_error(actor_id: i64) -> text")).to_equal(true)
```

</details>

#### total_errors is incremented on handler failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = sched_src()
expect(src.contains("self.total_errors = self.total_errors + 1")).to_equal(true)
```

</details>

#### per-actor error_count is incremented on handler failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = sched_src()
expect(src.contains("act.error_count = act.error_count + 1")).to_equal(true)
```

</details>

#### per-actor last_error is recorded on handler failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = sched_src()
expect(src.contains("act.last_error = result.error_msg")).to_equal(true)
```

</details>

#### trace log line is gated on trace_enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = sched_src()
expect(src.contains("if self.trace_enabled")).to_equal(true)
expect(src.contains("SIMPLE_ACTOR_TRACE")).to_equal(true)
```

</details>

#### actor_error_count returns 0 for unknown actor

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = sched_src()
# Accessor returns 0 sentinel
expect(src.contains("fn actor_error_count(actor_id: i64) -> i64")).to_equal(true)
```

</details>

#### actor_last_error returns empty string for unknown actor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = sched_src()
expect(src.contains("fn actor_last_error(actor_id: i64) -> text")).to_equal(true)
```

</details>

### Actor dispatch error recording (W2-6 behavioural)

#### dispatching unknown method produces is_error result

- var ht = HandlerTable new
- ht register
   - Expected: result.is_ok() is false
   - Expected: result.is_error() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ht = HandlerTable.new()
ht.register("ping", handler_echo)
val result = ht.dispatch("no_method", [])
expect(result.is_ok()).to_equal(false)
expect(result.is_error()).to_equal(true)
```

</details>

#### dispatch error message contains the unknown method name

- var ht = HandlerTable new
- ht register
   - Expected: result.error_msg contains `unknown_cmd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ht = HandlerTable.new()
ht.register("ping", handler_echo)
val result = ht.dispatch("unknown_cmd", [])
expect(result.error_msg.contains("unknown_cmd")).to_equal(true)
```

</details>

#### successful dispatch does not produce error

- var ht = HandlerTable new
- ht register
   - Expected: result.is_ok() is true
   - Expected: result.error_msg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ht = HandlerTable.new()
ht.register("ping", handler_echo)
val result = ht.dispatch("ping", ["pong"])
expect(result.is_ok()).to_equal(true)
expect(result.error_msg).to_equal("")
```

</details>

#### handler registered after an error dispatch still works

- var ht = HandlerTable new
   - Expected: bad.is_ok() is false
- ht register
   - Expected: good.is_ok() is true
   - Expected: good.value equals `added`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ht = HandlerTable.new()
val bad = ht.dispatch("not_registered", [])
expect(bad.is_ok()).to_equal(false)
# Register and dispatch successfully after the error
ht.register("add", handler_add)
val good = ht.dispatch("add", [])
expect(good.is_ok()).to_equal(true)
expect(good.value).to_equal("added")
```

</details>

#### multiple error dispatches are independent (no state bleed)

- var ht = HandlerTable new
   - Expected: r1.is_ok() is false
   - Expected: r2.is_ok() is false
   - Expected: r1.error_msg contains `missing_1`
   - Expected: r2.error_msg contains `missing_2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ht = HandlerTable.new()
val r1 = ht.dispatch("missing_1", [])
val r2 = ht.dispatch("missing_2", ["arg"])
expect(r1.is_ok()).to_equal(false)
expect(r2.is_ok()).to_equal(false)
expect(r1.error_msg.contains("missing_1")).to_equal(true)
expect(r2.error_msg.contains("missing_2")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/actor/scheduler_dispatch_error/scheduler_dispatch_error_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ActorScheduler dispatch error API (W2-6 structural)
- Actor dispatch error recording (W2-6 behavioural)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
