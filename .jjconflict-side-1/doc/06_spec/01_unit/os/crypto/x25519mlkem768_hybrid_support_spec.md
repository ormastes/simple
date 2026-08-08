# X25519mlkem768 Hybrid Support Specification

> Tests covering X25519MLKEM768 hybrid support behavior.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Hybrid Support Specification

## Scenarios

### X25519MLKEM768 hybrid support behavior

#### wipes every owned list and byte-array element including empty inputs

- var bytes: [u8] = [1 to u8
- x25519 mlkem768 wipe owned
- x25519 mlkem768 wipe owned bytes
- x25519 mlkem768 wipe owned
- x25519 mlkem768 wipe owned bytes
   - Expected: values equals `[0, 0, 0]`
   - Expected: bytes equals `[0.to_u8(), 0.to_u8(), 0.to_u8()]`
   - Expected: empty.len() equals `0`
   - Expected: empty_bytes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var values = [7, 8, 9]
var bytes: [u8] = [1.to_u8(), 2.to_u8(), 255.to_u8()]
var empty: list = []
var empty_bytes: [u8] = []
x25519_mlkem768_wipe_owned(values)
x25519_mlkem768_wipe_owned_bytes(bytes)
x25519_mlkem768_wipe_owned(empty)
x25519_mlkem768_wipe_owned_bytes(empty_bytes)
expect(values).to_equal([0, 0, 0])
expect(bytes).to_equal([0.to_u8(), 0.to_u8(), 0.to_u8()])
expect(empty.len()).to_equal(0)
expect(empty_bytes.len()).to_equal(0)
```

</details>

#### slices list and byte views at interior and zero-length boundaries

- expect list slice
- x25519 mlkem768 slice list
- expect byte slice
- [30 to u8
- x25519 mlkem768 slice bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [10, 20, 30, 40]
val empty_list: list = []
val empty_bytes: [u8] = []
expect_list_slice(x25519_mlkem768_slice_list(values, 1, 2), [20, 30])
expect_list_slice(
    x25519_mlkem768_slice_list(values, 4, 0), empty_list)
expect_byte_slice(x25519_mlkem768_slice_bytes(values, 2, 2),
    [30.to_u8(), 40.to_u8()])
expect_byte_slice(
    x25519_mlkem768_slice_bytes(values, 0, 0), empty_bytes)
```

</details>

#### returns exact structured errors for every list slice bound

- x25519 mlkem768 slice list
- x25519 mlkem768 slice list
- x25519 mlkem768 slice list
- x25519 mlkem768 slice list


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [10, 20, 30, 40]
expect_list_slice_error(
    x25519_mlkem768_slice_list(values, -1, 1),
    "negative slice start -1 for buffer length 4")
expect_list_slice_error(
    x25519_mlkem768_slice_list(values, 0, -2),
    "negative slice count -2 for buffer length 4")
expect_list_slice_error(
    x25519_mlkem768_slice_list(values, 5, 0),
    "slice start 5 is past buffer length 4")
expect_list_slice_error(
    x25519_mlkem768_slice_list(values, 3, 2),
    "slice range start 3 count 2 exceeds buffer length 4")
```

</details>

#### returns exact structured errors for byte bounds and non-byte values

- x25519 mlkem768 slice bytes
- x25519 mlkem768 slice bytes
- x25519 mlkem768 slice bytes
- x25519 mlkem768 slice bytes
- x25519 mlkem768 slice bytes
- x25519 mlkem768 slice bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [10, 20, 30, 40]
expect_byte_slice_error(
    x25519_mlkem768_slice_bytes(values, -3, 1),
    "negative slice start -3 for buffer length 4")
expect_byte_slice_error(
    x25519_mlkem768_slice_bytes(values, 0, -4),
    "negative slice count -4 for buffer length 4")
expect_byte_slice_error(
    x25519_mlkem768_slice_bytes(values, 6, 0),
    "slice start 6 is past buffer length 4")
expect_byte_slice_error(
    x25519_mlkem768_slice_bytes(values, 2, 3),
    "slice range start 2 count 3 exceeds buffer length 4")
expect_byte_slice_error(
    x25519_mlkem768_slice_bytes([7, 256, 9], 1, 1),
    "buffer value at index 1 is not a byte: 256")
expect_byte_slice_error(
    x25519_mlkem768_slice_bytes([7, -1, 9], 0, 3),
    "buffer value at index 1 is not a byte: -1")
```

</details>

#### matches known SHA-256 bytes and keeps all operation aliases identical

- expect digest
- expect digest
- expect digest
- expect digest
- expect digest


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [0, 1, 2, 255]
val expected = "3d1f57c984978ef98a18378c8166c1cb8ede02c03eeb6aee7e2f121dfeee3e56"
expect_digest(x25519_mlkem768_digest(values), expected)
expect_digest(x25519_mlkem768_keygen_fixture_digest(values), expected)
expect_digest(x25519_mlkem768_encapsulate_fixture_digest(values), expected)
expect_digest(x25519_mlkem768_decapsulate_fixture_digest(values), expected)
val empty: list = []
expect_digest(x25519_mlkem768_digest(empty),
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
```

</details>

#### propagates exact non-byte errors through digest and all aliases

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val invalid = [1, 300, 2]
val expected = "buffer value at index 1 is not a byte: 300"
match x25519_mlkem768_digest(invalid):
    case Ok(_): assert(false)
    case Err(error):
        expect(x25519_mlkem768_buffer_error_text(error)).to_equal(expected)
match x25519_mlkem768_keygen_fixture_digest(invalid):
    case Ok(_): assert(false)
    case Err(error):
        expect(x25519_mlkem768_buffer_error_text(error)).to_equal(expected)
match x25519_mlkem768_encapsulate_fixture_digest(invalid):
    case Ok(_): assert(false)
    case Err(error):
        expect(x25519_mlkem768_buffer_error_text(error)).to_equal(expected)
match x25519_mlkem768_decapsulate_fixture_digest(invalid):
    case Ok(_): assert(false)
    case Err(error):
        expect(x25519_mlkem768_buffer_error_text(error)).to_equal(expected)
```

</details>

#### appends typed bytes without changing their numeric values

- [1, 2], [3 to u8
   - Expected: joined equals `[1, 2, 3, 255]`
   - Expected: x25519_mlkem768_append_bytes([1, 2], empty) equals `[1, 2]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val joined = x25519_mlkem768_append_bytes(
    [1, 2], [3.to_u8(), 255.to_u8()])
expect(joined).to_equal([1, 2, 3, 255])
val empty: [u8] = []
expect(x25519_mlkem768_append_bytes([1, 2], empty)).to_equal([1, 2])
```

</details>

#### compares equal, unequal, shorter-left, and shorter-right lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: list = []
expect(x25519_mlkem768_lists_equal(empty, empty)).to_be(true)
expect(x25519_mlkem768_lists_equal([1, 2], [1, 2])).to_be(true)
expect(x25519_mlkem768_lists_equal([1, 2], [1, 3])).to_be(false)
expect(x25519_mlkem768_lists_equal([1], [1, 2])).to_be(false)
expect(x25519_mlkem768_lists_equal([1, 2], [1])).to_be(false)
```

</details>

#### accepts byte boundaries and rejects both underflow and overflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: list = []
expect(x25519_mlkem768_bytes_valid(empty)).to_be(true)
expect(x25519_mlkem768_bytes_valid([0, 1, 254, 255])).to_be(true)
expect(x25519_mlkem768_bytes_valid([-1])).to_be(false)
expect(x25519_mlkem768_bytes_valid([256])).to_be(false)
```

</details>

#### aggregates all-zero status across empty, first, middle, and last positions

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
expect(x25519_mlkem768_bytes_all_zero(empty)).to_be(true)
expect(x25519_mlkem768_bytes_all_zero(
    [0.to_u8(), 0.to_u8(), 0.to_u8()])).to_be(true)
expect(x25519_mlkem768_bytes_all_zero(
    [1.to_u8(), 0.to_u8(), 0.to_u8()])).to_be(false)
expect(x25519_mlkem768_bytes_all_zero(
    [0.to_u8(), 1.to_u8(), 0.to_u8()])).to_be(false)
expect(x25519_mlkem768_bytes_all_zero(
    [0.to_u8(), 0.to_u8(), 1.to_u8()])).to_be(false)
```

</details>

#### fails closed when SIMD admission has no Stage-4 provenance

- avx2 required config
- assert


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val admission = X25519MlKem768SimdAdmission(
    encoded_provenance: "",
    actual_binary_sha256: "",
    actual_provenance_sha256: "")
match x25519_mlkem768_resolve_simd_candidate_with_stage4_provenance_for_test(
        avx2_required_config(), "keygen", 1,
        admission.encoded_provenance,
        admission.actual_binary_sha256,
        admission.actual_provenance_sha256):
    case Err(reason):
        expect(reason).to_contain("stage4-source-roots-invalid")
    case Ok(_):
        assert(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/crypto/x25519mlkem768_hybrid_support_spec.spl` |
| Updated | 2026-08-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering X25519MLKEM768 hybrid support behavior.
- X25519MLKEM768 hybrid support behavior

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
