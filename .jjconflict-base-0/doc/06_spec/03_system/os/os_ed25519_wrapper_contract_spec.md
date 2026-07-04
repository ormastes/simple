# Os Ed25519 Wrapper Contract Specification

> <details>

<!-- sdn-diagram:id=os_ed25519_wrapper_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=os_ed25519_wrapper_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

os_ed25519_wrapper_contract_spec -> std
os_ed25519_wrapper_contract_spec -> os
os_ed25519_wrapper_contract_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=os_ed25519_wrapper_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Os Ed25519 Wrapper Contract Specification

## Scenarios

### os.crypto.ed25519 verify wrapper contract

#### verifies the RFC 8032 empty-message signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pubkey = hex_to_bytes(RFC8032_PUBKEY_HEX)
val sig = hex_to_bytes(RFC8032_SIG_EMPTY_HEX)
expect(ed25519_verify(pubkey, [], sig)).to_equal(true)
```

</details>

#### rejects the RFC 8032 signature if the message changes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pubkey = hex_to_bytes(RFC8032_PUBKEY_HEX)
val sig = hex_to_bytes(RFC8032_SIG_EMPTY_HEX)
expect(ed25519_verify(pubkey, [0x01u8], sig)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/os_ed25519_wrapper_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- os.crypto.ed25519 verify wrapper contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
