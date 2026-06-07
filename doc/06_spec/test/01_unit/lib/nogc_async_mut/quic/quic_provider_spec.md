# Quic Provider Specification

> <details>

<!-- sdn-diagram:id=quic_provider_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=quic_provider_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

quic_provider_spec -> nogc_async_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=quic_provider_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Quic Provider Specification

## Scenarios

### QUIC Provider

#### Provider availability check

#### returns Unavailable in pure-Simple builds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = quic_provider_check()
val label = quic_provider_label(p)
expect label == "unavailable"
```

</details>

#### does not crash when checking availability

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = quic_provider_check()
val usable = quic_provider_is_usable(p)
expect usable == false
```

</details>

#### Available provider is usable

1. expect quic provider is usable


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = QuicProvider.Available
expect quic_provider_is_usable(p) == true
```

</details>

#### Stub provider is not usable

1. expect quic provider is usable


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = QuicProvider.Stub
expect quic_provider_is_usable(p) == false
```

</details>

#### labels Available correctly

1. expect quic provider label


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect quic_provider_label(QuicProvider.Available) == "available"
```

</details>

#### labels Stub correctly

1. expect quic provider label


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect quic_provider_label(QuicProvider.Stub) == "stub"
```

</details>

#### Provider gate

#### gates Unavailable with NativeUnavailable error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = quic_provider_gate(QuicProvider.Unavailable)
expect result.ok == false
```

</details>

#### gates Stub with StubOnly error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = quic_provider_gate(QuicProvider.Stub)
expect result.ok == false
```

</details>

#### passes Available provider

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = quic_provider_gate(QuicProvider.Available)
expect result.ok == true
```

</details>

#### returns the provider in the result

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = quic_provider_gate(QuicProvider.Unavailable)
val label = quic_provider_label(result.provider)
expect label == "unavailable"
```

</details>

#### QuicTransportParams

#### creates default params with RFC 9000 idle timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tp = quic_transport_params_default()
expect tp.max_idle_timeout == 30000
```

</details>

#### creates default params with 1200-byte UDP payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tp = quic_transport_params_default()
expect tp.max_udp_payload_size == 1200
```

</details>

#### creates default params with 100 bidi streams

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tp = quic_transport_params_default()
expect tp.initial_max_streams_bidi == 100
```

</details>

#### creates default params with 100 uni streams

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tp = quic_transport_params_default()
expect tp.initial_max_streams_uni == 100
```

</details>

#### creates default params with 1 MiB initial max data

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tp = quic_transport_params_default()
expect tp.initial_max_data == 1048576
```

</details>

#### creates custom transport params

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tp = QuicTransportParams {
    max_idle_timeout: 5000,
    max_udp_payload_size: 1452,
    initial_max_data: 524288,
    initial_max_stream_data_bidi_local: 131072,
    initial_max_stream_data_bidi_remote: 131072,
    initial_max_stream_data_uni: 131072,
    initial_max_streams_bidi: 50,
    initial_max_streams_uni: 25
}
expect tp.max_idle_timeout == 5000
expect tp.initial_max_streams_uni == 25
```

</details>

#### H3 frame type constants

#### DATA is 0x00

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect H3_PROVIDER_FRAME_DATA == 0
```

</details>

#### HEADERS is 0x01

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect H3_PROVIDER_FRAME_HEADERS == 1
```

</details>

#### CANCEL_PUSH is 0x03

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect H3_PROVIDER_FRAME_CANCEL_PUSH == 3
```

</details>

#### SETTINGS is 0x04

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect H3_PROVIDER_FRAME_SETTINGS == 4
```

</details>

#### PUSH_PROMISE is 0x05

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect H3_PROVIDER_FRAME_PUSH_PROMISE == 5
```

</details>

#### GOAWAY is 0x07

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect H3_PROVIDER_FRAME_GOAWAY == 7
```

</details>

#### MAX_PUSH_ID is 0x0d

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect H3_PROVIDER_FRAME_MAX_PUSH_ID == 13
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/quic/quic_provider_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- QUIC Provider

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
