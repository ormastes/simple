# Simpleos Tls Embedded Material Specification

> <details>

<!-- sdn-diagram:id=simpleos_tls_embedded_material_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_tls_embedded_material_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_tls_embedded_material_spec -> std
simpleos_tls_embedded_material_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_tls_embedded_material_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Tls Embedded Material Specification

## Scenarios

### SimpleOS embedded TLS material

#### builds Certificate and Ed25519 CertificateVerify with embedded DER

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cert_msg = build_certificate([get_embedded_cert_der()])
expect(cert_msg[0u64]).to_equal(0x0Bu8)

val cv = build_certificate_verify(_transcript_hash_32(), get_embedded_key_der(), 0x0807u16)
expect(cv[0u64]).to_equal(0x0Fu8)
val sig_len = (cv[6u64].to_u64() << 8) | cv[7u64].to_u64()
expect(sig_len).to_equal(64u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_tls_embedded_material_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS embedded TLS material

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
