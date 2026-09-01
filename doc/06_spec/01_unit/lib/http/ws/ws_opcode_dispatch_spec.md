# Ws Opcode Dispatch Specification

> Tests covering WebSocket parser per-opcode dispatch.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ws Opcode Dispatch Specification

## Scenarios

### WebSocket parser per-opcode dispatch

#### parses a Text frame (opcode 0x1)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses a Text frame (opcode 0x1)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses a Text frame (opcode 0x1)")
assert_equal(_parses3(0x81, 0x01, 0x41), true)
```

</details>

#### parses a Binary frame (opcode 0x2)

- parses a Binary frame (opcode 0x2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses a Binary frame (opcode 0x2)")
assert_equal(_parses3(0x82, 0x01, 0x41), true)
```

</details>

#### parses a Continuation frame (opcode 0x0)

- parses a Continuation frame (opcode 0x0)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses a Continuation frame (opcode 0x0)")
assert_equal(_parses3(0x80, 0x01, 0x41), true)
```

</details>

#### parses a Ping frame (opcode 0x9)

- parses a Ping frame (opcode 0x9)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses a Ping frame (opcode 0x9)")
assert_equal(_parses3(0x89, 0x01, 0x41), true)
```

</details>

#### parses a Pong frame (opcode 0xa)

- parses a Pong frame (opcode 0xa)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses a Pong frame (opcode 0xa)")
assert_equal(_parses3(0x8a, 0x01, 0x41), true)
```

</details>

#### parses an empty Close frame (opcode 0x8)

- parses an empty Close frame (opcode 0x8)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses an empty Close frame (opcode 0x8)")
assert_equal(_parses2(0x88, 0x00), true)
```

</details>

#### rejects reserved non-control opcode 0x3

- rejects reserved non-control opcode 0x3


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects reserved non-control opcode 0x3")
assert_equal(_parses3(0x83, 0x01, 0x41), false)
```

</details>

#### rejects reserved non-control opcode 0x4

- rejects reserved non-control opcode 0x4


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects reserved non-control opcode 0x4")
assert_equal(_parses3(0x84, 0x01, 0x41), false)
```

</details>

#### rejects reserved control opcode 0xb

- rejects reserved control opcode 0xb


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects reserved control opcode 0xb")
assert_equal(_parses3(0x8b, 0x01, 0x41), false)
```

</details>

#### rejects reserved control opcode 0xf

- rejects reserved control opcode 0xf


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects reserved control opcode 0xf")
assert_equal(_parses3(0x8f, 0x01, 0x41), false)
```

</details>

#### rejects a Close frame with a 1-byte status payload

- rejects a Close frame with a 1-byte status payload


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a Close frame with a 1-byte status payload")
assert_equal(_parses3(0x88, 0x01, 0x41), false)
```

</details>

#### rejects a fragmented Close frame (FIN=0)

- rejects a fragmented Close frame (FIN=0)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a fragmented Close frame (FIN=0)")
assert_equal(_parses2(0x08, 0x00), false)
```

</details>

#### rejects a fragmented Ping frame (FIN=0)

- rejects a fragmented Ping frame (FIN=0)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a fragmented Ping frame (FIN=0)")
assert_equal(_parses3(0x09, 0x01, 0x41), false)
```

</details>

#### rejects a fragmented Pong frame (FIN=0)

- rejects a fragmented Pong frame (FIN=0)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a fragmented Pong frame (FIN=0)")
assert_equal(_parses3(0x0a, 0x01, 0x41), false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/http/ws/ws_opcode_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WebSocket parser per-opcode dispatch.
- WebSocket parser per-opcode dispatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `0c9c520197c41d8c3afd42ea26c7a9dd41f0f8db1d4976674ed130a232d92d94`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0c9c520197c41d8c3afd42ea26c7a9dd41f0f8db1d4976674ed130a232d92d94`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0c9c520197c41d8c3afd42ea26c7a9dd41f0f8db1d4976674ed130a232d92d94`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/http/ws/ws_opcode_dispatch_spec.spl
mirror: doc/06_spec/01_unit/lib/http/ws/ws_opcode_dispatch_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/http/ws/ws_opcode_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/http/ws/ws_opcode_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/http/ws/ws_opcode_dispatch_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses a Text frame (opcode 0x1)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/http/ws/ws_opcode_dispatch_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses a Binary frame (opcode 0x2)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/http/ws/ws_opcode_dispatch_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses a Continuation frame (opcode 0x0)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
