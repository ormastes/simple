# Simpleos Tls Baremetal Gate Specification

> <details>

<!-- sdn-diagram:id=simpleos_tls_baremetal_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_tls_baremetal_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_tls_baremetal_gate_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_tls_baremetal_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Tls Baremetal Gate Specification

## Scenarios

### SimpleOS baremetal TLS gate

#### reports embedded certificate material once real DER is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(has_embedded_certs()).to_equal(true)
expect(get_embedded_cert_der().len().to_u64()).to_be_greater_than(256u64)
expect(get_embedded_key_der().len().to_u64()).to_equal(48u64)
```

</details>

#### exposes baremetal TLS info for embedded DER material

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
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

#### keeps TLS production readiness blocked while platform shims are placeholders

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(baremetal_tls_platform_ready()).to_equal(false)
expect(baremetal_tls_blocker()).to_equal("placeholder_entropy")
```

</details>

#### keeps tls13_accept fail-closed without a ClientHello record

1. cert chain: [ sample cert der
2. server pkcs8:  sample key der
3. Tls13AcceptResult Accepted
   - Expected: "accepted-before-record-io" equals ``
4. Tls13AcceptResult Failed
   - Expected: reason equals `no_client_hello_record`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = Tls13ServerConfig(
    cert_chain: [_sample_cert_der()],
    server_pkcs8: _sample_key_der(),
    server_sig_scheme: 0x0807u16,
    alpn_protocols: []
)

match tls13_accept_client_hello_record_for_test([], config):
    Tls13AcceptResult.Accepted(_ctx):
        expect("accepted-before-record-io").to_equal("")
    Tls13AcceptResult.Failed(reason):
        expect(reason).to_equal("no_client_hello_record")
```

</details>

#### keeps the boot plan explicit about TLS production blockers

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = rt_file_read_text("doc/plans/riscv_rtl_simpleos_boot.md")

expect(plan).to_contain("TLS Baremetal")
expect(plan).to_contain("Blocked, not complete")
expect(plan).to_contain("ClientHello record")
expect(plan).to_contain("offline-generated")
expect(plan).to_contain("deterministic placeholder")
expect(plan).to_contain("placeholder_entropy")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_tls_baremetal_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS baremetal TLS gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
