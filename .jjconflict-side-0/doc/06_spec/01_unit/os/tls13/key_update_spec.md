# Key Update Specification

> 1. fail

<!-- sdn-diagram:id=key_update_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=key_update_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

key_update_spec -> std
key_update_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=key_update_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Key Update Specification

## Scenarios

### parse_key_update

#### returns UpdateNotRequested for byte value 0

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = parse_key_update(_payload_not_requested())
if val KeyUpdateRequest.UpdateNotRequested(unused) = res:
    expect(unused).to_equal(0x00u8)
else:
    fail("parse_key_update did not return UpdateNotRequested for byte value 0")
```

</details>

#### returns UpdateRequested for byte value 1

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = parse_key_update(_payload_requested())
if val KeyUpdateRequest.UpdateRequested(unused) = res:
    expect(unused).to_equal(0x00u8)
else:
    fail("parse_key_update did not return UpdateRequested for byte value 1")
```

</details>

#### returns Invalid for byte value 2

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = parse_key_update(_payload_invalid())
if val KeyUpdateRequest.Invalid(unused) = res:
    expect(unused).to_equal(0x02u8)
else:
    fail("parse_key_update did not return Invalid for byte value 2")
```

</details>

#### returns Invalid for empty payload

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = parse_key_update(_payload_empty())
if val KeyUpdateRequest.Invalid(unused) = res:
    expect(unused).to_equal(0x00u8)
else:
    fail("parse_key_update did not return Invalid for empty payload")
```

</details>

### emit_key_update wire format

#### emits exactly 5 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = emit_key_update(false)
expect(msg.len().to_u64()).to_equal(5u64)
```

</details>

#### first byte is HS_KEY_UPDATE (24 = 0x18)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = emit_key_update(false)
expect(msg[0]).to_equal(HS_KEY_UPDATE)
```

</details>

#### length field is 0x000001 (bytes 1-3)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = emit_key_update(false)
expect(msg[1]).to_equal(0x00u8)
expect(msg[2]).to_equal(0x00u8)
expect(msg[3]).to_equal(0x01u8)
```

</details>

#### body byte is 0x00 for request_update=false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = emit_key_update(false)
expect(msg[4]).to_equal(0x00u8)
```

</details>

#### body byte is 0x01 for request_update=true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = emit_key_update(true)
expect(msg[4]).to_equal(0x01u8)
```

</details>

### KeyUpdate round-trip

#### emit(false) round-trips to UpdateNotRequested

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = emit_key_update(false)
val body = _strip_header(msg)
val res = parse_key_update(body)
if val KeyUpdateRequest.UpdateNotRequested(unused) = res:
    expect(unused).to_equal(0x00u8)
else:
    fail("emit(false) did not round-trip to UpdateNotRequested")
```

</details>

#### emit(true) round-trips to UpdateRequested

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = emit_key_update(true)
val body = _strip_header(msg)
val res = parse_key_update(body)
if val KeyUpdateRequest.UpdateRequested(unused) = res:
    expect(unused).to_equal(0x00u8)
else:
    fail("emit(true) did not round-trip to UpdateRequested")
```

</details>

### derive_next_traffic_secret

#### SHA-256 path returns exactly 32 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val secret = _zeros_32()
val next = derive_next_traffic_secret(secret, 32)
expect(next.len().to_u64()).to_equal(32u64)
```

</details>

#### SHA-384 path returns exactly 48 bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val secret = _zeros_48()
val next = derive_next_traffic_secret(secret, 48)
expect(next.len().to_u64()).to_equal(48u64)
```

</details>

#### SHA-256 path is deterministic (same input gives same output)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val secret = _zeros_32()
val a = derive_next_traffic_secret(secret, 32)
val b = derive_next_traffic_secret(secret, 32)
expect(a.len().to_u64()).to_equal(b.len().to_u64())
expect(a[0]).to_equal(b[0])
expect(a[31]).to_equal(b[31])
```

</details>

#### SHA-256 path output differs from all-zero input

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = _zeros_32()
val s2 = _ones_32()
val n1 = derive_next_traffic_secret(s1, 32)
val n2 = derive_next_traffic_secret(s2, 32)
# Check at least the first byte differs
expect(n1[0] == n2[0]).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/tls13/key_update_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
