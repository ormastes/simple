# Jwt Rfc7519 Kat Specification

> <details>

<!-- sdn-diagram:id=jwt_rfc7519_kat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=jwt_rfc7519_kat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

jwt_rfc7519_kat_spec -> std
jwt_rfc7519_kat_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=jwt_rfc7519_kat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Jwt Rfc7519 Kat Specification

## Scenarios

### JWT HS256 — RFC 7515 Appendix A.1 KAT

#### sign produces exact RFC 7515 A.1 compact JWT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jwt = jwt_sign_hs256(_hs256_header(), _hs256_payload(), _hs256_key())
expect(_u8_to_text(jwt)).to_equal(_hs256_expected_compact())
```

</details>

#### verify accepts the RFC 7515 A.1 compact JWT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jwt = _text_to_u8(_hs256_expected_compact())
expect(_hs256_verify_ok(jwt, _hs256_key())).to_equal(true)
```

</details>

### JWT HS256 — tamper rejection

#### tampered payload is rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Flip one character in the payload segment
val good = _hs256_expected_compact()
# Replace first char after first dot with 'X'
val dot1 = good.index_of(".")
val tampered = good.substring(0, dot1 + 1) + "X" + good.substring(dot1 + 2, good.length())
val jwt = _text_to_u8(tampered)
expect(_hs256_verify_err(jwt, _hs256_key())).to_equal(true)
```

</details>

#### tampered signature is rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Flip one character in the signature segment (last segment)
val good = _hs256_expected_compact()
val last_dot = good.last_index_of(".")
val tampered = good.substring(0, last_dot + 1) + "X" + good.substring(last_dot + 2, good.length())
val jwt = _text_to_u8(tampered)
expect(_hs256_verify_err(jwt, _hs256_key())).to_equal(true)
```

</details>

### JWT EdDSA — RFC 8037 round-trip

#### EdDSA sign then verify round-trip succeeds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jwt = jwt_sign_eddsa(_eddsa_header(), _eddsa_payload(), _eddsa_seed())
expect(_eddsa_verify_ok(jwt, _eddsa_pubkey())).to_equal(true)
```

</details>

#### EdDSA decoded payload matches original

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jwt = jwt_sign_eddsa(_eddsa_header(), _eddsa_payload(), _eddsa_seed())
val payload = _eddsa_verify_payload(jwt, _eddsa_pubkey())
expect(_u8_to_text(payload)).to_equal(
    "{\"iss\":\"joe\",\"exp\":1300819380,\"http://example.com/is_root\":true}"
)
```

</details>

### JWT security — alg=none unconditional rejection

#### jwt_verify_hs256 rejects alg=none token

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jwt = _alg_none_header_b64_jwt()
expect(_hs256_verify_err(jwt, _hs256_key())).to_equal(true)
```

</details>

#### jwt_verify_eddsa rejects alg=none token

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val jwt = _alg_none_header_b64_jwt()
expect(_eddsa_verify_err(jwt, _eddsa_pubkey())).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `/home/ormastes/dev/pub/simple/test/01_unit/lib/crypto/jwt_rfc7519_kat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- JWT HS256 — RFC 7515 Appendix A.1 KAT
- JWT HS256 — tamper rejection
- JWT EdDSA — RFC 8037 round-trip
- JWT security — alg=none unconditional rejection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
