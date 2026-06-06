# Gen Server Specification

> <details>

<!-- sdn-diagram:id=gen_server_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gen_server_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gen_server_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gen_server_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gen Server Specification

## Scenarios

### Gen Server

#### defines GenServer required and optional callbacks

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/lib/nogc_async_mut/gen_server.spl")

expect(src).to_contain("trait GenServer:")
expect(src).to_contain("fn init(args: text) -> text")
expect(src).to_contain("fn handle_call(request: text, state: text) -> text")
expect(src).to_contain("fn handle_cast(msg: text, state: text) -> text")
expect(src).to_contain("fn handle_info(msg: text, state: text) -> text:")
expect(src).to_contain("state")
expect(src).to_contain("fn terminate(reason: text, state: text):")
```

</details>

#### defines runner lifecycle and call/cast dispatch helpers

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/lib/nogc_async_mut/gen_server.spl")

expect(src).to_contain("struct GenServerRunner:")
expect(src).to_contain("state: text")
expect(src).to_contain("name: text")
expect(src).to_contain("running: bool")
expect(src).to_contain("fn gen_server_runner(name: text, initial_state: text) -> GenServerRunner:")
expect(src).to_contain("fn gen_server_start(runner: GenServerRunner):")
expect(src).to_contain("runner.running = true")
expect(src).to_contain("fn gen_server_stop(runner: GenServerRunner):")
expect(src).to_contain("fn gen_server_call(runner: GenServerRunner, request: text, handler: fn(text, text) -> text) -> text:")
expect(src).to_contain("fn gen_server_cast(runner: GenServerRunner, msg: text, handler: fn(text, text) -> text):")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/gen_server_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Gen Server

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
