# X25519mlkem768 Core Provider Negative Specification

> Tests covering X25519MLKEM768 core provider negative branches.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Core Provider Negative Specification

## Scenarios

### X25519MLKEM768 core provider negative branches

#### should propagate a deterministic forward-provider failure from key generation

- Inject an explicit forward NTT error before polynomial splitting
-  core zero32


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Inject an explicit forward NTT error before polynomial splitting")
val provider = DeterministicFaultNttProvider.create(
    "fixture-forward-failure", "", false)
match ml_kem_keygen_checked_provider(
        _core_zero32(), _core_zero32(), provider):
    case Ok(_): fail("key generation swallowed the provider failure")
    case Err(reason): expect(reason).to_equal("fixture-forward-failure")
```

</details>

#### should reject a deterministic short accelerator output

- Return an empty forward batch for a nonempty polynomial request
-  core zero32


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Return an empty forward batch for a nonempty polynomial request")
val provider = DeterministicFaultNttProvider.create("", "", true)
match ml_kem_keygen_checked_provider(
        _core_zero32(), _core_zero32(), provider):
    case Ok(_): fail("key generation accepted a short provider output")
    case Err(reason): expect(reason).to_equal(
        "ml-kem-accelerator-output-size-invalid")
```

</details>

#### should propagate a deterministic inverse-provider failure from encapsulation

- Use valid scalar key material and fail the provider inverse batch


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use valid scalar key material and fail the provider inverse batch")
val (ek, _, _, message) = _core_valid_material()
val provider = DeterministicFaultNttProvider.create(
    "", "fixture-inverse-failure", false)
match ml_kem_encaps_checked_provider(ek, message, provider):
    case Ok(_): fail("encapsulation swallowed the provider failure")
    case Err(reason): expect(reason).to_equal("fixture-inverse-failure")
```

</details>

#### should propagate a deterministic inverse-provider failure from decapsulation

- Use valid scalar ciphertext and fail the provider inverse batch


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use valid scalar ciphertext and fail the provider inverse batch")
val (_, dk, ciphertext, _) = _core_valid_material()
val provider = DeterministicFaultNttProvider.create(
    "", "fixture-inverse-failure", false)
match ml_kem_decaps_checked_provider(dk, ciphertext, provider):
    case Ok(_): fail("decapsulation swallowed the provider failure")
    case Err(reason): expect(reason).to_equal("fixture-inverse-failure")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_core_provider_negative_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 core provider negative branches.
- X25519MLKEM768 core provider negative branches

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
