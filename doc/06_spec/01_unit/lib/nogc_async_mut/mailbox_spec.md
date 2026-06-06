# Mailbox Specification

> <details>

<!-- sdn-diagram:id=mailbox_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mailbox_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mailbox_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mailbox_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mailbox Specification

## Scenarios

### Mailbox

#### defines bounded mailbox state and send contract

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/lib/nogc_async_mut/mailbox.spl")

expect(src).to_contain("struct Mailbox:")
expect(src).to_contain("capacity: i64")
expect(src).to_contain("messages: [text]")
expect(src).to_contain("count: i64")
expect(src).to_contain("fn mailbox_new(capacity: i64) -> Mailbox:")
expect(src).to_contain("Mailbox(capacity: capacity, messages: [], count: 0)")
expect(src).to_contain("fn mailbox_send(mb: Mailbox, msg: text) -> bool:")
expect(src).to_contain("if mb.count >= mb.capacity:")
expect(src).to_contain("return false")
```

</details>

#### defines receive, status, and drain operations

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/lib/nogc_async_mut/mailbox.spl")

expect(src).to_contain("fn mailbox_receive(mb: Mailbox) -> text:")
expect(src).to_contain("val msg = mb.messages[0]")
expect(src).to_contain("fn mailbox_try_receive(mb: Mailbox) -> text:")
expect(src).to_contain("mailbox_receive(mb)")
expect(src).to_contain("fn mailbox_is_empty(mb: Mailbox) -> bool:")
expect(src).to_contain("fn mailbox_is_full(mb: Mailbox) -> bool:")
expect(src).to_contain("fn mailbox_size(mb: Mailbox) -> i64:")
expect(src).to_contain("fn mailbox_drain(mb: Mailbox) -> [text]:")
expect(src).to_contain("mb.messages = []")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/mailbox_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Mailbox

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
