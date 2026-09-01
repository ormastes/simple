# Quic Provider Specification

> Tests covering QUIC Provider.

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

- returns Unavailable in pure-Simple builds


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Unavailable in pure-Simple builds")
val p = quic_provider_check()
val label = quic_provider_label(p)
expect label == "unavailable"
```

</details>

#### does not crash when checking availability

- does not crash when checking availability


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not crash when checking availability")
val p = quic_provider_check()
val usable = quic_provider_is_usable(p)
expect usable == false
```

</details>

#### Available provider is usable

- Available provider is usable


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Available provider is usable")
val p = QuicProvider.Available
expect quic_provider_is_usable(p) == true
```

</details>

#### Stub provider is not usable

- Stub provider is not usable


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Stub provider is not usable")
val p = QuicProvider.Stub
expect quic_provider_is_usable(p) == false
```

</details>

#### labels Available correctly

- labels Available correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("labels Available correctly")
expect quic_provider_label(QuicProvider.Available) == "available"
```

</details>

#### labels Stub correctly

- labels Stub correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("labels Stub correctly")
expect quic_provider_label(QuicProvider.Stub) == "stub"
```

</details>

#### Provider gate

#### gates Unavailable with NativeUnavailable error

- gates Unavailable with NativeUnavailable error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gates Unavailable with NativeUnavailable error")
val result = quic_provider_gate(QuicProvider.Unavailable)
expect result.ok == false
```

</details>

#### gates Stub with StubOnly error

- gates Stub with StubOnly error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gates Stub with StubOnly error")
val result = quic_provider_gate(QuicProvider.Stub)
expect result.ok == false
```

</details>

#### passes Available provider

- passes Available provider


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes Available provider")
val result = quic_provider_gate(QuicProvider.Available)
expect result.ok == true
```

</details>

#### returns the provider in the result

- returns the provider in the result


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns the provider in the result")
val result = quic_provider_gate(QuicProvider.Unavailable)
val label = quic_provider_label(result.provider)
expect label == "unavailable"
```

</details>

#### QuicTransportParams

#### creates default params with RFC 9000 idle timeout

- creates default params with RFC 9000 idle timeout


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates default params with RFC 9000 idle timeout")
val tp = quic_transport_params_default()
expect tp.max_idle_timeout == 30000
```

</details>

#### creates default params with 1200-byte UDP payload

- creates default params with 1200-byte UDP payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates default params with 1200-byte UDP payload")
val tp = quic_transport_params_default()
expect tp.max_udp_payload_size == 1200
```

</details>

#### creates default params with 100 bidi streams

- creates default params with 100 bidi streams


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates default params with 100 bidi streams")
val tp = quic_transport_params_default()
expect tp.initial_max_streams_bidi == 100
```

</details>

#### creates default params with 100 uni streams

- creates default params with 100 uni streams


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates default params with 100 uni streams")
val tp = quic_transport_params_default()
expect tp.initial_max_streams_uni == 100
```

</details>

#### creates default params with 1 MiB initial max data

- creates default params with 1 MiB initial max data


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates default params with 1 MiB initial max data")
val tp = quic_transport_params_default()
expect tp.initial_max_data == 1048576
```

</details>

#### creates custom transport params

- creates custom transport params


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates custom transport params")
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

- DATA is 0x00


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DATA is 0x00")
expect H3_PROVIDER_FRAME_DATA == 0
```

</details>

#### HEADERS is 0x01

- HEADERS is 0x01


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("HEADERS is 0x01")
expect H3_PROVIDER_FRAME_HEADERS == 1
```

</details>

#### CANCEL_PUSH is 0x03

- CANCEL_PUSH is 0x03


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CANCEL_PUSH is 0x03")
expect H3_PROVIDER_FRAME_CANCEL_PUSH == 3
```

</details>

#### SETTINGS is 0x04

- SETTINGS is 0x04


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SETTINGS is 0x04")
expect H3_PROVIDER_FRAME_SETTINGS == 4
```

</details>

#### PUSH_PROMISE is 0x05

- PUSH_PROMISE is 0x05


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PUSH_PROMISE is 0x05")
expect H3_PROVIDER_FRAME_PUSH_PROMISE == 5
```

</details>

#### GOAWAY is 0x07

- GOAWAY is 0x07


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("GOAWAY is 0x07")
expect H3_PROVIDER_FRAME_GOAWAY == 7
```

</details>

#### MAX_PUSH_ID is 0x0d

- MAX_PUSH_ID is 0x0d


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("MAX_PUSH_ID is 0x0d")
expect H3_PROVIDER_FRAME_MAX_PUSH_ID == 13
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/quic/quic_provider_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering QUIC Provider.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0063c04cdab722816d4e280b4b56d95f8e6ea4fadea81a6bc1f42f2c7df0b8d6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0063c04cdab722816d4e280b4b56d95f8e6ea4fadea81a6bc1f42f2c7df0b8d6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0063c04cdab722816d4e280b4b56d95f8e6ea4fadea81a6bc1f42f2c7df0b8d6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut/quic/quic_provider_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/quic/quic_provider_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/quic/quic_provider_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/quic/quic_provider_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/quic/quic_provider_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns Unavailable in pure-Simple builds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/quic/quic_provider_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not crash when checking availability' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/quic/quic_provider_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Available provider is usable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
