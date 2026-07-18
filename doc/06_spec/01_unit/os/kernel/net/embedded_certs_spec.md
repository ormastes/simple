# Embedded Certs Specification

> <details>

<!-- sdn-diagram:id=embedded_certs_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=embedded_certs_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

embedded_certs_spec -> std
embedded_certs_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=embedded_certs_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Embedded Certs Specification

## Scenarios

### baremetal TLS material gate

#### advertises offline-generated certificate material as available

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(has_embedded_certs()).to_equal(true)
```

</details>

#### returns non-empty DER certificate and key bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cert = get_embedded_cert_der()
val key = get_embedded_key_der()
expect(cert.len().to_u64()).to_be_greater_than(256u64)
expect(key.len().to_u64()).to_equal(48u64)
expect(cert[0u64]).to_equal(0x30u8)
expect(key[0u64]).to_equal(0x30u8)
```

</details>

#### reports TLS info available with embedded bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info = get_baremetal_tls_info()
expect(info.available).to_equal(true)
expect(info.cert_der.len().to_u64()).to_be_greater_than(256u64)
expect(info.key_der.len().to_u64()).to_equal(48u64)
expect(info.production_ready).to_equal(false)
expect(info.blocker).to_equal("placeholder_entropy")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/net/embedded_certs_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- baremetal TLS material gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
