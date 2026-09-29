# Ws Writer Opcode Emission Specification

> Tests covering WebSocket writer per-variant opcode emission.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ws Writer Opcode Emission Specification

## Scenarios

### WebSocket writer per-variant opcode emission

#### emits opcode 0x1 for a Text frame

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits opcode 0x1 for a Text frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits opcode 0x1 for a Text frame")
val f = WsFrame.Text(WsTextFrame(
    fin: true, rsv1: false, rsv2: false, rsv3: false, payload: _empty()))
assert_equal(_opcode_of(f), 0x1)
```

</details>

#### emits opcode 0x2 for a Binary frame

- emits opcode 0x2 for a Binary frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits opcode 0x2 for a Binary frame")
val f = WsFrame.Binary(WsBinaryFrame(
    fin: true, rsv1: false, rsv2: false, rsv3: false, payload: _empty()))
assert_equal(_opcode_of(f), 0x2)
```

</details>

#### emits opcode 0x0 for a Continuation frame

- emits opcode 0x0 for a Continuation frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits opcode 0x0 for a Continuation frame")
val f = WsFrame.Continuation(WsContinuationFrame(
    fin: true, rsv1: false, rsv2: false, rsv3: false, payload: _empty()))
assert_equal(_opcode_of(f), 0x0)
```

</details>

#### emits opcode 0x8 for a Close frame

- emits opcode 0x8 for a Close frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits opcode 0x8 for a Close frame")
val f = WsFrame.Close(WsCloseFrame(
    fin: true, has_status: false, code: 0, reason: _empty()))
assert_equal(_opcode_of(f), 0x8)
```

</details>

#### emits opcode 0x9 for a Ping frame

- emits opcode 0x9 for a Ping frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits opcode 0x9 for a Ping frame")
val f = WsFrame.Ping(WsPingFrame(fin: true, payload: _empty()))
assert_equal(_opcode_of(f), 0x9)
```

</details>

#### emits opcode 0xa for a Pong frame

- emits opcode 0xa for a Pong frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits opcode 0xa for a Pong frame")
val f = WsFrame.Pong(WsPongFrame(fin: true, payload: _empty()))
assert_equal(_opcode_of(f), 0xa)
```

</details>

#### emits a distinct opcode for every variant (not all Text)

- emits a distinct opcode for every variant (not all Text)


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits a distinct opcode for every variant (not all Text)")
val text = WsFrame.Text(WsTextFrame(
    fin: true, rsv1: false, rsv2: false, rsv3: false, payload: _empty()))
val binary = WsFrame.Binary(WsBinaryFrame(
    fin: true, rsv1: false, rsv2: false, rsv3: false, payload: _empty()))
val pong = WsFrame.Pong(WsPongFrame(fin: true, payload: _empty()))
assert_equal(_opcode_of(text) != _opcode_of(binary), true)
assert_equal(_opcode_of(binary) != _opcode_of(pong), true)
assert_equal(_opcode_of(text) != _opcode_of(pong), true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/http/ws/ws_writer_opcode_emission_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WebSocket writer per-variant opcode emission.
- WebSocket writer per-variant opcode emission

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `f4e7b1d8587bff803d35bc7e2e4699d117184e7c3477c94e2bd9a5fcebe97cbc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f4e7b1d8587bff803d35bc7e2e4699d117184e7c3477c94e2bd9a5fcebe97cbc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f4e7b1d8587bff803d35bc7e2e4699d117184e7c3477c94e2bd9a5fcebe97cbc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/http/ws/ws_writer_opcode_emission_spec.spl
mirror: doc/06_spec/01_unit/lib/http/ws/ws_writer_opcode_emission_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/http/ws/ws_writer_opcode_emission_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/http/ws/ws_writer_opcode_emission_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/http/ws/ws_writer_opcode_emission_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits opcode 0x1 for a Text frame' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/http/ws/ws_writer_opcode_emission_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits opcode 0x2 for a Binary frame' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/http/ws/ws_writer_opcode_emission_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits opcode 0x0 for a Continuation frame' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
