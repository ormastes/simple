# Wine Async Gate Specification

> <details>

<!-- sdn-diagram:id=wine_async_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_async_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_async_gate_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_async_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Async Gate Specification

## Scenarios

### Wine async substrate gate

#### reports missing nogc future support first

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_async_gate("poll waker io-driver")).to_equal("missing-nogc-future")
```

</details>

#### accepts the full nogc async readiness set

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = "nogc-future poll waker io-driver submit-open submit-read submit-write submit-close " +
    "submit-timeout poll-completion event-loop register-fd deregister-fd wake noalloc-capability"
expect(wine_async_gate(features)).to_equal("ready")
```

</details>

#### requires completion-driver file operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = "io-driver submit-open submit-read submit-write submit-close submit-timeout"
expect(wine_async_io_gate(features)).to_equal("missing-poll-completion")
```

</details>

<details>
<summary>Advanced: requires event loop registration and wake support</summary>

#### requires event loop registration and wake support

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = "event-loop register-fd waker"
expect(wine_async_event_loop_gate(features)).to_equal("missing-deregister-fd")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_async_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine async substrate gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
