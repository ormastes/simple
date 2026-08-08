# X25519mlkem768 Metal Binary Fail Closed Specification

> Tests covering X25519MLKEM768 Metal binary fail-closed admission.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Metal Binary Fail Closed Specification

## Scenarios

### X25519MLKEM768 Metal binary fail-closed admission

#### should reject a nonempty metallib image when its digest is unpinned

- Submit a nonempty fake metallib without a digest pin
- executor,  metal negative fixture
- executor shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit a nonempty fake metallib without a digest pin")
var executor = X25519MlKem768MetalNttExecutor.create_binary(
    _NEGATIVE_METALLIB, "")
match x25519_mlkem768_metal_ntt_execute(
        executor, _metal_negative_fixture()):
    case Ok(_): fail("Metal accepted an unpinned metallib")
    case Err(reason): expect(reason).to_equal(
        "metal-ntt-binary-digest-mismatch")
executor.shutdown()
```

</details>

#### should reject a nonempty metallib image when its digest differs

- Submit a nonempty fake metallib with a mismatched digest
- executor,  metal negative fixture
- executor shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Submit a nonempty fake metallib with a mismatched digest")
var executor = X25519MlKem768MetalNttExecutor.create_binary(
    _NEGATIVE_METALLIB,
    "0000000000000000000000000000000000000000000000000000000000000000")
match x25519_mlkem768_metal_ntt_execute(
        executor, _metal_negative_fixture()):
    case Ok(_): fail("Metal accepted a digest-mismatched metallib")
    case Err(reason): expect(reason).to_equal(
        "metal-ntt-binary-digest-mismatch")
executor.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_metal_binary_fail_closed_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 Metal binary fail-closed admission.
- X25519MLKEM768 Metal binary fail-closed admission

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
