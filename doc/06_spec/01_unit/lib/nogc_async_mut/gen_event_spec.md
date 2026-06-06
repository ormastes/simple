# Gen Event Specification

> <details>

<!-- sdn-diagram:id=gen_event_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gen_event_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gen_event_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gen_event_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gen Event Specification

## Scenarios

### Gen Event

#### defines GenEvent handler and manager state

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/lib/nogc_async_mut/gen_event.spl")

expect(src).to_contain("trait GenEventHandler:")
expect(src).to_contain("fn handle_event(event: text, state: text) -> text")
expect(src).to_contain("fn init(args: text) -> text:")
expect(src).to_contain("fn terminate(reason: text, state: text):")
expect(src).to_contain("struct GenEventManager:")
expect(src).to_contain("name: text")
expect(src).to_contain("handlers: [text]")
expect(src).to_contain("count: i64")
expect(src).to_contain("running: bool")
```

</details>

#### defines event lifecycle, handler registration, and dispatch

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/lib/nogc_async_mut/gen_event.spl")

expect(src).to_contain("fn gen_event_manager_new(name: text) -> GenEventManager:")
expect(src).to_contain("fn gen_event_start(mgr: GenEventManager):")
expect(src).to_contain("mgr.running = true")
expect(src).to_contain("fn gen_event_stop(mgr: GenEventManager):")
expect(src).to_contain("fn gen_event_add_handler(mgr: GenEventManager, handler_id: text):")
expect(src).to_contain("mgr.handlers.push(handler_id)")
expect(src).to_contain("fn gen_event_remove_handler(mgr: GenEventManager, handler_id: text):")
expect(src).to_contain("fn gen_event_handler_count(mgr: GenEventManager) -> i64:")
expect(src).to_contain("fn gen_event_notify(mgr: GenEventManager, event: text,")
expect(src).to_contain("fn gen_event_call(mgr: GenEventManager, event: text,")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/gen_event_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Gen Event

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
