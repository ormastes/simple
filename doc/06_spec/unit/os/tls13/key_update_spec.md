# Key Update Specification

> Tests covering parse_key_update, emit_key_update wire format, KeyUpdate round-trip, derive_next_traffic_secret.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Key Update Specification

## Scenarios

### parse_key_update

#### returns UpdateNotRequested for byte value 0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns UpdateNotRequested for byte value 0
   - Expected: true is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns UpdateNotRequested for byte value 0")
val res = parse_key_update(_payload_not_requested())
if val KeyUpdateRequest.UpdateNotRequested(unused) = res:
    expect(true).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### returns UpdateRequested for byte value 1

- returns UpdateRequested for byte value 1
   - Expected: true is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns UpdateRequested for byte value 1")
val res = parse_key_update(_payload_requested())
if val KeyUpdateRequest.UpdateRequested(unused) = res:
    expect(true).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### returns Invalid for byte value 2

- returns Invalid for byte value 2
   - Expected: true is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Invalid for byte value 2")
val res = parse_key_update(_payload_invalid())
if val KeyUpdateRequest.Invalid(unused) = res:
    expect(true).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### returns Invalid for empty payload

- returns Invalid for empty payload
   - Expected: true is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Invalid for empty payload")
val res = parse_key_update(_payload_empty())
if val KeyUpdateRequest.Invalid(unused) = res:
    expect(true).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

### emit_key_update wire format

#### emits exactly 5 bytes

- emits exactly 5 bytes
   - Expected: msg.len().to_u64() equals `5u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits exactly 5 bytes")
val msg = emit_key_update(false)
expect(msg.len().to_u64()).to_equal(5u64)
```

</details>

#### first byte is HS_KEY_UPDATE (24 = 0x18)

- first byte is HS_KEY_UPDATE (24 = 0x18)
   - Expected: msg[0] equals `HS_KEY_UPDATE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("first byte is HS_KEY_UPDATE (24 = 0x18)")
val msg = emit_key_update(false)
expect(msg[0]).to_equal(HS_KEY_UPDATE)
```

</details>

#### length field is 0x000001 (bytes 1-3)

- length field is 0x000001 (bytes 1-3)
   - Expected: msg[1] equals `0x00u8`
   - Expected: msg[2] equals `0x00u8`
   - Expected: msg[3] equals `0x01u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("length field is 0x000001 (bytes 1-3)")
val msg = emit_key_update(false)
expect(msg[1]).to_equal(0x00u8)
expect(msg[2]).to_equal(0x00u8)
expect(msg[3]).to_equal(0x01u8)
```

</details>

#### body byte is 0x00 for request_update=false

- body byte is 0x00 for request_update=false
   - Expected: msg[4] equals `0x00u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("body byte is 0x00 for request_update=false")
val msg = emit_key_update(false)
expect(msg[4]).to_equal(0x00u8)
```

</details>

#### body byte is 0x01 for request_update=true

- body byte is 0x01 for request_update=true
   - Expected: msg[4] equals `0x01u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("body byte is 0x01 for request_update=true")
val msg = emit_key_update(true)
expect(msg[4]).to_equal(0x01u8)
```

</details>

### KeyUpdate round-trip

#### emit(false) round-trips to UpdateNotRequested

- emit(false) round-trips to UpdateNotRequested
   - Expected: true is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emit(false) round-trips to UpdateNotRequested")
val msg = emit_key_update(false)
val body = _strip_header(msg)
val res = parse_key_update(body)
if val KeyUpdateRequest.UpdateNotRequested(unused) = res:
    expect(true).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

#### emit(true) round-trips to UpdateRequested

- emit(true) round-trips to UpdateRequested
   - Expected: true is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emit(true) round-trips to UpdateRequested")
val msg = emit_key_update(true)
val body = _strip_header(msg)
val res = parse_key_update(body)
if val KeyUpdateRequest.UpdateRequested(unused) = res:
    expect(true).to_equal(true)
else:
    expect(false).to_equal(true)
```

</details>

### derive_next_traffic_secret

#### SHA-256 path returns exactly 32 bytes

- SHA-256 path returns exactly 32 bytes
   - Expected: next.len().to_u64() equals `32u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SHA-256 path returns exactly 32 bytes")
val secret = _zeros_32()
val next = derive_next_traffic_secret(secret, 32)
expect(next.len().to_u64()).to_equal(32u64)
```

</details>

#### SHA-384 path returns exactly 48 bytes

- SHA-384 path returns exactly 48 bytes
   - Expected: next.len().to_u64() equals `48u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SHA-384 path returns exactly 48 bytes")
val secret = _zeros_48()
val next = derive_next_traffic_secret(secret, 48)
expect(next.len().to_u64()).to_equal(48u64)
```

</details>

#### SHA-256 path is deterministic (same input gives same output)

- SHA-256 path is deterministic (same input gives same output)
   - Expected: a.len().to_u64() equals `b.len().to_u64()`
   - Expected: a[0] equals `b[0]`
   - Expected: a[31] equals `b[31]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SHA-256 path is deterministic (same input gives same output)")
val secret = _zeros_32()
val a = derive_next_traffic_secret(secret, 32)
val b = derive_next_traffic_secret(secret, 32)
expect(a.len().to_u64()).to_equal(b.len().to_u64())
expect(a[0]).to_equal(b[0])
expect(a[31]).to_equal(b[31])
```

</details>

#### SHA-256 path output differs from all-zero input

- SHA-256 path output differs from all-zero input
   - Expected: _is_all_zero(next, 32u64) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SHA-256 path output differs from all-zero input")
val secret = _zeros_32()
val next = derive_next_traffic_secret(secret, 32)
# The HKDF output is a pseudo-random function; all-zeros input won't
# produce all-zeros output for a well-formed label derivation.
# We check that at least one byte differs (conservative correctness check).
# Note: uses module-level helper to avoid interpreter var-mutation-in-loop bug.
expect(_is_all_zero(next, 32u64)).to_equal(false)
```

</details>

#### SHA-256 path: different secrets produce different outputs

- SHA-256 path: different secrets produce different outputs


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SHA-256 path: different secrets produce different outputs")
val s1 = _zeros_32()
val s2 = _ones_32()
val n1 = derive_next_traffic_secret(s1, 32)
val n2 = derive_next_traffic_secret(s2, 32)
# Check at least the first byte differs
expect(n1[0]).to_not_equal(n2[0])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/tls13/key_update_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering parse_key_update, emit_key_update wire format, KeyUpdate round-trip, derive_next_traffic_secret.
- parse_key_update
- emit_key_update wire format
- KeyUpdate round-trip
- derive_next_traffic_secret

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `9cc5bbe56071490498f8bae79414d7f3744ef15a799ef3a17cdeff1939082cac`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9cc5bbe56071490498f8bae79414d7f3744ef15a799ef3a17cdeff1939082cac`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9cc5bbe56071490498f8bae79414d7f3744ef15a799ef3a17cdeff1939082cac`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/tls13/key_update_spec.spl
mirror: doc/06_spec/unit/os/tls13/key_update_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/tls13/key_update_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/tls13/key_update_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/tls13/key_update_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns UpdateNotRequested for byte value 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/tls13/key_update_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns UpdateRequested for byte value 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/tls13/key_update_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns Invalid for byte value 2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
