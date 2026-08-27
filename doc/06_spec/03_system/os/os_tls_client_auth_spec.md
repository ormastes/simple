# TLS 1.3 Client Authentication Codec Specification

> Exercises the pure handshake helpers added for TLS 1.3 client authentication:

<!-- sdn-diagram:id=os_tls_client_auth_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=os_tls_client_auth_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

os_tls_client_auth_spec -> std
os_tls_client_auth_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=os_tls_client_auth_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TLS 1.3 Client Authentication Codec Specification

Exercises the pure handshake helpers added for TLS 1.3 client authentication:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/os_tls_client_auth_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises the pure handshake helpers added for TLS 1.3 client authentication:
- CertificateRequest parsing
- client Certificate encoding
- client CertificateVerify encoding

tag: slow, system, tls

## Scenarios

### tls13 client auth handshake helpers

#### parses CertificateRequest signature_algorithms

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = [
    0x00u8,
    0x00, 0x08,
    0x00, 0x0d,
    0x00, 0x04,
    0x00, 0x02,
    0x08, 0x07
]
val req = parse_certificate_request(body)
expect(req.request_context.len()).to_equal(0)
expect(req.sig_algs.len()).to_equal(1)
expect(req.sig_algs[0]).to_equal(0x0807)
```

</details>

#### builds an empty client Certificate message

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = build_certificate_bytes([], [])
val parsed = parse_handshake_header(msg)
expect(parsed.msg_type).to_equal(11)
expect(parsed.body[0]).to_equal(0x00)
expect(parsed.body[1]).to_equal(0x00)
expect(parsed.body[2]).to_equal(0x00)
expect(parsed.body[3]).to_equal(0x00)
```

</details>

#### builds a non-empty client CertificateVerify message

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig = [0xAAu8, 0xBB, 0xCC, 0xDD]
val msg = build_certificate_verify_bytes(0x0807, sig)
val parsed = parse_handshake_header(msg)
expect(parsed.msg_type).to_equal(15)
expect(parsed.body[0]).to_equal(0x08)
expect(parsed.body[1]).to_equal(0x07)
expect(parsed.body[2]).to_equal(0x00)
expect(parsed.body[3]).to_equal(0x04)
expect(parsed.body[4]).to_equal(0xAA)
expect(parsed.body[7]).to_equal(0xDD)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
