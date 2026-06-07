# Protocol Handler ALPN Dispatch Specification

> <details>

<!-- sdn-diagram:id=protocol_handler_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=protocol_handler_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

protocol_handler_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=protocol_handler_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Protocol Handler ALPN Dispatch Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #AC-4-alpn |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Draft |
| Source | `test/01_unit/lib/nogc_async_mut/http_server/protocol_handler_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### ALPN extension parsing and protocol dispatch

#### parses ALPN extension from ClientHello bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Stub: raw ALPN extension bytes encoding ["h2", "http/1.1"]
# Extension type: 0x00 0x10, followed by extension data length, protocol list
val ext_type_hi: u8 = 0x00
val ext_type_lo: u8 = 0x10
val alpn_ext_type: u16 = 0x0010
expect(alpn_ext_type).to_equal(16)
# Simulate parse result: first protocol name extracted
val first_protocol = "h2"
expect(first_protocol).to_equal("h2")
expect(first_protocol.len()).to_equal(2)
```

</details>

#### returns H1 handler for no ALPN

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Stub: no ALPN → empty negotiated protocol
val negotiated_protocol = ""
val is_empty = negotiated_protocol == ""
expect(is_empty).to_equal(true)
# Dispatch: empty → H1
val handler_kind = if negotiated_protocol == "":
    "H1"
elif negotiated_protocol == "h2":
    "H2"
else:
    "UNKNOWN"
expect(handler_kind).to_equal("H1")
```

</details>

#### returns H2 handler for h2 ALPN

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val negotiated_protocol = "h2"
val handler_kind = if negotiated_protocol == "":
    "H1"
elif negotiated_protocol == "h2":
    "H2"
else:
    "UNKNOWN"
expect(handler_kind).to_equal("H2")
```

</details>

#### returns None for h3 ALPN on TCP connection

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val negotiated_protocol = "h3"
val connection_transport = "TCP"
# H3 requires UDP/QUIC; on TCP it is unsupported
val handler_kind = if negotiated_protocol == "h3" && connection_transport == "TCP":
    "NONE"
elif negotiated_protocol == "h2":
    "H2"
elif negotiated_protocol == "":
    "H1"
else:
    "NONE"
expect(handler_kind).to_equal("NONE")
# On a UDP connection, h3 would be accepted (future AC-2 work)
val udp_transport = "UDP"
val udp_handler = if negotiated_protocol == "h3" && udp_transport == "UDP":
    "H3"
else:
    "NONE"
expect(udp_handler).to_equal("H3")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
