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
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mailbox Specification

## Scenarios

### Mailbox

#### keeps bounded mailbox API available

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = mailbox_source()

expect(source).to_contain("struct Mailbox:")
expect(source).to_contain("fn mailbox_new(capacity: i64) -> Mailbox")
expect(source).to_contain("fn mailbox_send(mb: Mailbox, msg: text) -> bool")
expect(source).to_contain("fn mailbox_receive(mb: Mailbox) -> text")
expect(source).to_contain("fn mailbox_try_receive(mb: Mailbox) -> text")
expect(source).to_contain("fn mailbox_is_empty(mb: Mailbox) -> bool")
expect(source).to_contain("fn mailbox_is_full(mb: Mailbox) -> bool")
expect(source).to_contain("fn mailbox_drain(mb: Mailbox) -> [text]")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/interpreter/mailbox_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Mailbox

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
