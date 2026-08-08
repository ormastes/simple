# X25519mlkem768 Hrr Specification

> Tests covering TLS 1.3 X25519MLKEM768 HelloRetryRequest.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Hrr Specification

## Scenarios

### TLS 1.3 X25519MLKEM768 HelloRetryRequest

#### should REQ-005 constructs CH2 from an exact fresh hybrid share

- Create fresh X25519MLKEM768 state for ClientHello2
-  hrr octets
- Parse the emitted hybrid key share through the server parser
   - Expected: parsed.key_share_groups.len() equals `1`
   - Expected: parsed.x25519_mlkem768_key_share.len() equals `1216`
   - Expected: parsed.x25519_mlkem768_key_share[0] equals `fresh_share[0]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create fresh X25519MLKEM768 state for ClientHello2")
val fresh_share = _hrr_octets(1216, 41)
val ch2 = match build_client_hello2_bytes_with_x25519_mlkem768(
        _hrr_octets(32, 7), fresh_share, "example.test", []):
    case Ok(value): value
    case Err(reason): fail(reason)
step("Parse the emitted hybrid key share through the server parser")
val parsed = process_client_hello(parse_handshake_header(ch2).body)
expect(parsed.key_share_groups.len()).to_equal(1)
expect(parsed.key_share_groups[0] == GROUP_X25519_MLKEM768).to_be(true)
expect(parsed.x25519_mlkem768_key_share.len()).to_equal(1216)
expect(parsed.x25519_mlkem768_key_share[0]).to_equal(fresh_share[0])
expect(parsed.x25519_mlkem768_key_share[1215]).to_equal(
    fresh_share[1215])
```

</details>

#### should REQ-004 rejects malformed hybrid CH2 material before encoding

- Reject a ClientHello2 hybrid share with the wrong length
-  hrr octets


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject a ClientHello2 hybrid share with the wrong length")
match build_client_hello2_bytes_with_x25519_mlkem768(
        _hrr_octets(32, 7), _hrr_octets(1215, 41),
        "example.test", []):
    case Ok(_): fail("malformed hybrid CH2 share was encoded")
    case Err(reason): expect(reason).to_contain("1216")
```

</details>

#### should REQ-005 rejects HRR selecting the hybrid share already sent in CH1

- Receive an HRR that repeats the CH1 hybrid key-share group
-  hybrid hrr handshake
-  hrr octets
-  hrr octets
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Receive an HRR that repeats the CH1 hybrid key-share group")
val body = _hybrid_hrr_body()
val result = process_hrr_after_serverhello_with_x25519_mlkem768(
    _hybrid_hrr_handshake(body), body,
    _hrr_octets(32, 7), _hrr_octets(32, 17),
    _hrr_octets(32, 29), _hrr_octets(32, 33), [], [],
    "example.test", false, true, false, true, true)
match result:
    case HrrFlowResult.Ok(_):
        fail("same-group X25519MLKEM768 HRR was accepted")
    case HrrFlowResult.Reject(reason):
        expect(reason).to_contain("equals CH1 key_share group")
```

</details>

#### should REQ-004 rejects a hybrid HRR when CH1 did not support the group

- Reject an HRR group that ClientHello1 did not advertise
-  hybrid hrr handshake
-  hrr octets
-  hrr octets
-  hrr octets


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject an HRR group that ClientHello1 did not advertise")
val body = _hybrid_hrr_body()
val result = process_hrr_after_serverhello_with_x25519_mlkem768(
    _hybrid_hrr_handshake(body), body,
    _hrr_octets(32, 7), _hrr_octets(32, 17),
    _hrr_octets(32, 29), _hrr_octets(32, 33), [],
    _hrr_octets(1216, 73), "example.test",
    false, true, false, false, false)
match result:
    case HrrFlowResult.Ok(_): fail("unoffered hybrid HRR was accepted")
    case HrrFlowResult.Reject(reason):
        expect(reason).to_contain("not in client supported_groups")
```

</details>

#### should REQ-005 accepts one hybrid HRR only with fresh 1216-byte state

- Accept one hybrid retry with a fresh exact-length key share
-  hybrid hrr handshake
-  hrr octets
-  hrr octets
   - Expected: value.transcript_seed.len() equals `expected_seed_len`
- parse handshake header
   - Expected: parsed.x25519_mlkem768_key_share.len() equals `1216`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Accept one hybrid retry with a fresh exact-length key share")
val body = _hybrid_hrr_body()
val fresh_share = _hrr_octets(1216, 73)
val result = process_hrr_after_serverhello_with_x25519_mlkem768(
    _hybrid_hrr_handshake(body), body,
    _hrr_octets(32, 7), _hrr_octets(32, 17),
    _hrr_octets(32, 29), _hrr_octets(32, 33), [], fresh_share,
    "example.test", false, true, false, true, false)
match result:
    case HrrFlowResult.Reject(reason): fail(reason)
    case HrrFlowResult.Ok(value):
        expect(value.selected_group == GROUP_X25519_MLKEM768).to_be(true)
        val expected_seed_len = 36u64 + _hybrid_hrr_handshake(body).len()
        expect(value.transcript_seed.len()).to_equal(expected_seed_len)
        val parsed = process_client_hello(
            parse_handshake_header(value.client_hello2_bytes).body)
        expect(parsed.x25519_mlkem768_key_share.len()).to_equal(1216)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/tls13/x25519mlkem768_hrr_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TLS 1.3 X25519MLKEM768 HelloRetryRequest.
- TLS 1.3 X25519MLKEM768 HelloRetryRequest

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
