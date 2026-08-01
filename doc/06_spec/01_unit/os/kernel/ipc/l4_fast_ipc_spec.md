# L4 Fast Ipc Specification

> <details>

<!-- sdn-diagram:id=l4_fast_ipc_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=l4_fast_ipc_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

l4_fast_ipc_spec -> std
l4_fast_ipc_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=l4_fast_ipc_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# L4 Fast Ipc Specification

## Scenarios

### L4 fast IPC pure Simple primitives

#### builds deterministic 32-bit register messages

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = l4_inline_message32_from_counter(5)
expect(msg.method_id).to_equal(5)
expect(msg.payload_len).to_equal(32)
expect(msg.r0).to_equal(5)
expect(msg.r7).to_equal(12)
expect(l4_inline_checksum32(msg)).to_equal(54)
expect(l4_inline_round_trip_32bit(5)).to_equal(54)
expect(l4_inline_round_trip_32bit_index(5)).to_equal(54)
```

</details>

#### builds deterministic 64-bit register messages

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = l4_inline_message64_from_counter(5)
expect(msg.method_id).to_equal(5)
expect(msg.payload_len).to_equal(32)
expect(msg.r0).to_equal(5)
expect(msg.r7).to_equal(12)
expect(l4_inline_checksum64(msg)).to_equal(86)
expect(l4_inline_round_trip_64bit(5)).to_equal(86)
expect(l4_inline_round_trip_64bit_index(5)).to_equal(86)
```

</details>

#### transfers a 4096-byte buffer slot and clears ownership

1. var pool = L4BufferPool new
   - Expected: checksum equals `4111`
   - Expected: pool.states[2] equals `0`
   - Expected: pool.owners[2] equals `0`
   - Expected: pool.msg_lens[2] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var pool = L4BufferPool.new(4)
val checksum = pool.transfer_4096(6, 11, 12)
expect(checksum).to_equal(4111)
expect(pool.states[2]).to_equal(0)
expect(pool.owners[2]).to_equal(0)
expect(pool.msg_lens[2]).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/ipc/l4_fast_ipc_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- L4 fast IPC pure Simple primitives

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
