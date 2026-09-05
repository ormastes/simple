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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- wipes every owned list and byte-array element including empty inputs
   - Expected: values equals `[0, 0, 0]`
   - Expected: bytes equals `[0.to_u8(), 0.to_u8(), 0.to_u8()]`
   - Expected: empty.len() equals `0`
   - Expected: empty_bytes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("wipes every owned list and byte-array element including empty inputs")
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

- slices list and byte views at interior and zero-length boundaries


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("slices list and byte views at interior and zero-length boundaries")
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

- returns exact structured errors for every list slice bound


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns exact structured errors for every list slice bound")
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

- returns exact structured errors for byte bounds and non-byte values


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns exact structured errors for byte bounds and non-byte values")
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

- matches known SHA-256 bytes and keeps all operation aliases identical


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("matches known SHA-256 bytes and keeps all operation aliases identical")
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

- propagates exact non-byte errors through digest and all aliases
   - Expected: x25519_mlkem768_buffer_error_text(error) equals `expected`
   - Expected: x25519_mlkem768_buffer_error_text(error) equals `expected`
   - Expected: x25519_mlkem768_buffer_error_text(error) equals `expected`
   - Expected: x25519_mlkem768_buffer_error_text(error) equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("propagates exact non-byte errors through digest and all aliases")
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

- appends typed bytes without changing their numeric values
   - Expected: joined equals `[1, 2, 3, 255]`
   - Expected: x25519_mlkem768_append_bytes([1, 2], empty) equals `[1, 2]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("appends typed bytes without changing their numeric values")
val joined = x25519_mlkem768_append_bytes(
    [1, 2], [3.to_u8(), 255.to_u8()])
expect(joined).to_equal([1, 2, 3, 255])
val empty: [u8] = []
expect(x25519_mlkem768_append_bytes([1, 2], empty)).to_equal([1, 2])
```

</details>

#### compares equal, unequal, shorter-left, and shorter-right lists

- compares equal, unequal, shorter-left, and shorter-right lists


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("compares equal, unequal, shorter-left, and shorter-right lists")
val empty: list = []
expect(x25519_mlkem768_lists_equal(empty, empty)).to_be(true)
expect(x25519_mlkem768_lists_equal([1, 2], [1, 2])).to_be(true)
expect(x25519_mlkem768_lists_equal([1, 2], [1, 3])).to_be(false)
expect(x25519_mlkem768_lists_equal([1], [1, 2])).to_be(false)
expect(x25519_mlkem768_lists_equal([1, 2], [1])).to_be(false)
```

</details>

#### accepts byte boundaries and rejects both underflow and overflow

- accepts byte boundaries and rejects both underflow and overflow


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("accepts byte boundaries and rejects both underflow and overflow")
val empty: list = []
expect(x25519_mlkem768_bytes_valid(empty)).to_be(true)
expect(x25519_mlkem768_bytes_valid([0, 1, 254, 255])).to_be(true)
expect(x25519_mlkem768_bytes_valid([-1])).to_be(false)
expect(x25519_mlkem768_bytes_valid([256])).to_be(false)
```

</details>

#### aggregates all-zero status across empty, first, middle, and last positions

- aggregates all-zero status across empty, first, middle, and last positions


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("aggregates all-zero status across empty, first, middle, and last positions")
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

- fails closed when SIMD admission has no Stage-4 provenance


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails closed when SIMD admission has no Stage-4 provenance")
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
| Updated | 2026-08-26 |
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `aeb4710685ef634baa7a600d3aac8a3bb35e607b71c3326d860b1d176798907a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aeb4710685ef634baa7a600d3aac8a3bb35e607b71c3326d860b1d176798907a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aeb4710685ef634baa7a600d3aac8a3bb35e607b71c3326d860b1d176798907a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/os/crypto/x25519mlkem768_hybrid_support_spec.spl
mirror: doc/06_spec/01_unit/os/crypto/x25519mlkem768_hybrid_support_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/crypto/x25519mlkem768_hybrid_support_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/crypto/x25519mlkem768_hybrid_support_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/crypto/x25519mlkem768_hybrid_support_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/crypto/x25519mlkem768_hybrid_support_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wipes every owned list and byte-array element including empty inputs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_hybrid_support_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'slices list and byte views at interior and zero-length boundaries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/crypto/x25519mlkem768_hybrid_support_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns exact structured errors for every list slice bound' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
