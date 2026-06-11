# Gen Statem Specification

> <details>

<!-- sdn-diagram:id=gen_statem_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gen_statem_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gen_statem_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gen_statem_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gen Statem Specification

## Scenarios

### Gen Statem

#### defines GenStatem callback constants and required callbacks

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/lib/nogc_async_mut/gen_statem.spl")

expect(src).to_contain("val CALLBACK_STATE_FUNCTIONS = \"state_functions\"")
expect(src).to_contain("val CALLBACK_HANDLE_EVENT = \"handle_event\"")
expect(src).to_contain("trait GenStatem:")
expect(src).to_contain("fn init(args: text) -> text")
expect(src).to_contain("fn handle_event(event_type: text, event: text,")
expect(src).to_contain("state_name: text, data: text) -> text")
expect(src).to_contain("fn callback_mode() -> text:")
expect(src).to_contain("CALLBACK_HANDLE_EVENT")
```

</details>

#### defines runner lifecycle and event transition helper

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/lib/nogc_async_mut/gen_statem.spl")

expect(src).to_contain("struct GenStatemRunner:")
expect(src).to_contain("state_name: text")
expect(src).to_contain("data: text")
expect(src).to_contain("running: bool")
expect(src).to_contain("fn gen_statem_runner(name: text, initial_state: text, initial_data: text) -> GenStatemRunner:")
expect(src).to_contain("fn gen_statem_start(runner: GenStatemRunner):")
expect(src).to_contain("fn gen_statem_stop(runner: GenStatemRunner):")
expect(src).to_contain("fn gen_statem_current_state(runner: GenStatemRunner) -> text:")
expect(src).to_contain("fn gen_statem_send_event(runner: GenStatemRunner, event_type: text, event: text,")
expect(src).to_contain("runner.state_name = new_state")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/gen_statem_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Gen Statem

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
