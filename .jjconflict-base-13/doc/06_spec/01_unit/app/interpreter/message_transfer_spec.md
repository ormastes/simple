# Message Transfer Specification

> <details>

<!-- sdn-diagram:id=message_transfer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=message_transfer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

message_transfer_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=message_transfer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Message Transfer Specification

## Scenarios

### MessageTransfer

#### keeps message transfer strategy and value wrappers available

<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = message_transfer_source()

expect(source).to_contain("enum TransferStrategy:")
expect(source).to_contain("enum ValueTag:")
expect(source).to_contain("enum TransferStatus:")
expect(source).to_contain("enum ValueKind:")
expect(source).to_contain("class ValueWrapper:")
expect(source).to_contain("fn copy_strategy_for(size: i64) -> TransferStrategy")
expect(source).to_contain("fn estimate_size(type_tag: ValueKind, raw_size: i64) -> i64")
```

</details>

#### keeps transfer result stats and send helpers available

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = message_transfer_source()

expect(source).to_contain("class TransferResult:")
expect(source).to_contain("class TransferStats:")
expect(source).to_contain("class MailboxMessage:")
expect(source).to_contain("class MessageTransfer:")
expect(source).to_contain("me wrap_for_send(process_id: i64, size: i64, type_tag: ValueKind) -> TransferResult")
expect(source).to_contain("fn send_value(process_id: i64, size: i64, type_tag: ValueKind) -> TransferResult")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/interpreter/message_transfer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MessageTransfer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
