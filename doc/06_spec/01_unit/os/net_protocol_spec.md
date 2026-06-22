# Net Protocol Specification

> 1. var ku = KeyUpdateRequest

<!-- sdn-diagram:id=net_protocol_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=net_protocol_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

net_protocol_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=net_protocol_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Net Protocol Specification

## Scenarios

### Network Protocol — KeyUpdate (AC-1)

#### update_requested true for request variant

1. var ku = KeyUpdateRequest
   - Expected: ku.is_request() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ku = KeyUpdateRequest(update_requested: true, sender_epoch: 1)
expect(ku.is_request()).to_equal(true)
```

</details>

#### update_requested false for notification variant

1. var ku = KeyUpdateRequest
   - Expected: ku.is_notification() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ku = KeyUpdateRequest(update_requested: false, sender_epoch: 2)
expect(ku.is_notification()).to_equal(true)
```

</details>

#### epoch_after increments sender_epoch by one

1. var ku = KeyUpdateRequest
   - Expected: ku.epoch_after() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var ku = KeyUpdateRequest(update_requested: true, sender_epoch: 5)
expect(ku.epoch_after()).to_equal(6)
```

</details>

#### request and notification are mutually exclusive

1. var req = KeyUpdateRequest
2. var notif = KeyUpdateRequest
   - Expected: req.is_request() is true
   - Expected: notif.is_request() == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var req = KeyUpdateRequest(update_requested: true, sender_epoch: 0)
var notif = KeyUpdateRequest(update_requested: false, sender_epoch: 0)
expect(req.is_request()).to_equal(true)
expect(notif.is_request() == false).to_equal(true)
```

</details>

### Network Protocol — NewSessionTicket (AC-2)

#### ticket not expired within lifetime

1. var nst = NewSessionTicket
   - Expected: nst.is_expired(2000) == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nst = NewSessionTicket(ticket_lifetime: 3600, ticket_age_add: 0, ticket_nonce: "n1", max_early_data: 0, issued_at: 1000)
expect(nst.is_expired(2000) == false).to_equal(true)
```

</details>

#### ticket expired when time exceeds lifetime

1. var nst = NewSessionTicket
   - Expected: nst.is_expired(5000) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nst = NewSessionTicket(ticket_lifetime: 100, ticket_age_add: 0, ticket_nonce: "n2", max_early_data: 0, issued_at: 1000)
expect(nst.is_expired(5000)).to_equal(true)
```

</details>

#### supports_early_data true when max_early_data positive

1. var nst = NewSessionTicket
   - Expected: nst.supports_early_data() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nst = NewSessionTicket(ticket_lifetime: 3600, ticket_age_add: 0, ticket_nonce: "n3", max_early_data: 16384, issued_at: 0)
expect(nst.supports_early_data()).to_equal(true)
```

</details>

### Network Protocol — HTTP/3 Frames (AC-3)

#### DATA frame type_name is DATA

1. var frm = H3FrameHeader
   - Expected: frm.type_name() equals `DATA`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var frm = H3FrameHeader(frame_type: 0, payload_length: 512, stream_id: 1)
expect(frm.type_name()).to_equal("DATA")
```

</details>

#### HEADERS frame is_headers returns true

1. var frm = H3FrameHeader
   - Expected: frm.is_headers() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var frm = H3FrameHeader(frame_type: 1, payload_length: 200, stream_id: 3)
expect(frm.is_headers()).to_equal(true)
```

</details>

#### SETTINGS frame is_control returns true

1. var frm = H3FrameHeader
   - Expected: frm.is_control() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var frm = H3FrameHeader(frame_type: 4, payload_length: 32, stream_id: 0)
expect(frm.is_control()).to_equal(true)
```

</details>

### Network Protocol — QPACK (AC-4)

#### authority entry is pseudo header

1. var entry = QpackStaticEntry
   - Expected: entry.is_pseudo() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var entry = QpackStaticEntry(index: 0, header_name: ":authority", header_value: "")
expect(entry.is_pseudo()).to_equal(true)
```

</details>

#### method GET entry has value

1. var entry = QpackStaticEntry
   - Expected: entry.has_value() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var entry = QpackStaticEntry(index: 15, header_name: ":method", header_value: "GET")
expect(entry.has_value()).to_equal(true)
```

</details>

#### decoder can_decode when acknowledged_insert meets required

1. var dec = QpackDecoderState
   - Expected: dec.can_decode() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dec = QpackDecoderState(required_insert_count: 5, base_delta: 0, max_table_capacity: 4096, current_entries: 5, acknowledged_insert: 5)
expect(dec.can_decode()).to_equal(true)
```

</details>

#### decoder is_blocked when acknowledged_insert below required

1. var dec = QpackDecoderState
   - Expected: dec.is_blocked() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dec = QpackDecoderState(required_insert_count: 5, base_delta: 0, max_table_capacity: 4096, current_entries: 3, acknowledged_insert: 3)
expect(dec.is_blocked()).to_equal(true)
```

</details>

### Network Protocol — WS Deflate (AC-5)

#### default window bits are 15

1. var params = WsDeflateParams
   - Expected: params.is_default_window() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var params = WsDeflateParams(server_no_context_takeover: false, client_no_context_takeover: false, server_max_window_bits: 15, client_max_window_bits: 15, agreed: true)
expect(params.is_default_window()).to_equal(true)
```

</details>

#### resets_context false when no_context_takeover both false

1. var params = WsDeflateParams
   - Expected: params.resets_context() == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var params = WsDeflateParams(server_no_context_takeover: false, client_no_context_takeover: false, server_max_window_bits: 15, client_max_window_bits: 15, agreed: true)
expect(params.resets_context() == false).to_equal(true)
```

</details>

### Network Protocol — STUN (AC-7)

#### binding_request msg_type is 1

1. var msg = StunMessage
   - Expected: msg.is_binding_request() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var msg = StunMessage(msg_type: 1, magic_cookie: 554869826, transaction_id: "txn1", mapped_addr: "", mapped_port: 0)
expect(msg.is_binding_request()).to_equal(true)
```

</details>

#### magic cookie value is 554869826

1. var msg = StunMessage
   - Expected: msg.is_valid_cookie() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var msg = StunMessage(msg_type: 1, magic_cookie: 554869826, transaction_id: "txn2", mapped_addr: "", mapped_port: 0)
expect(msg.is_valid_cookie()).to_equal(true)
```

</details>

#### has_mapped_address true when addr is set

1. var msg = StunMessage
   - Expected: msg.has_mapped_address() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var msg = StunMessage(msg_type: 257, magic_cookie: 554869826, transaction_id: "txn3", mapped_addr: "1.2.3.4", mapped_port: 54321)
expect(msg.has_mapped_address()).to_equal(true)
```

</details>

### Network Protocol — SCRAM-SHA-512 (AC-8) + Registry (AC-9)

#### ScramSha512 hash function is SHA-512

1. var scram = ScramSha512
   - Expected: scram.is_sha512() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scram = ScramSha512(username: "alice", hash_function: "SHA-512", iteration_count: 4096, client_nonce: "cN", server_nonce: "")
expect(scram.is_sha512()).to_equal(true)
```

</details>

#### ScramSha512 key_length is 64

1. var scram = ScramSha512
   - Expected: scram.key_length() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scram = ScramSha512(username: "bob", hash_function: "SHA-512", iteration_count: 4096, client_nonce: "c1", server_nonce: "s1")
expect(scram.key_length()).to_equal(64)
```

</details>

#### ProtocolModule done module is_done true

1. var m = ProtocolModule
   - Expected: m.is_done() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = ProtocolModule(name: "TLS 1.3", rfc: "RFC 8446", status: "done", test_status: "pass")
expect(m.is_done()).to_equal(true)
```

</details>

#### ProtocolRegistry completion_pct for 12 of 18

1. var reg = ProtocolRegistry
   - Expected: reg.completion_pct() equals `66`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ProtocolRegistry(total: 18, done_count: 12, partial_count: 2, pending_count: 4)
expect(reg.completion_pct()).to_equal(66)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/net_protocol_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Network Protocol — KeyUpdate (AC-1)
- Network Protocol — NewSessionTicket (AC-2)
- Network Protocol — HTTP/3 Frames (AC-3)
- Network Protocol — QPACK (AC-4)
- Network Protocol — WS Deflate (AC-5)
- Network Protocol — STUN (AC-7)
- Network Protocol — SCRAM-SHA-512 (AC-8) + Registry (AC-9)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
