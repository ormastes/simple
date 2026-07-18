# Simd Scan Specification

> <details>

<!-- sdn-diagram:id=simd_scan_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simd_scan_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simd_scan_spec -> std
simd_scan_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simd_scan_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simd Scan Specification

## Scenarios

### scan_byte_scalar absolute oracle (KNOWN positions)

#### finds 'a' in banana at exactly 1, 3, 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = scan_byte_scalar(banana(), 97u8)
val idx = indices_of(r)
expect(idx.len()).to_equal(3)
expect(idx[0]).to_equal(1)
expect(idx[1]).to_equal(3)
expect(idx[2]).to_equal(5)
```

</details>

#### finds 'b' only at index 0 (byte at index 0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = scan_byte_scalar(banana(), 98u8)
val idx = indices_of(r)
expect(idx.len()).to_equal(1)
expect(idx[0]).to_equal(0)
```

</details>

#### finds last byte 'a' includes the final index 5 (byte at last index)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = scan_byte_scalar(banana(), 97u8)
val idx = indices_of(r)
# last match is the final span position
expect(idx[idx.len() - 1]).to_equal(5)
```

</details>

#### finds 'n' at 2 and 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = scan_byte_scalar(banana(), 110u8)
val idx = indices_of(r)
expect(idx.len()).to_equal(2)
expect(idx[0]).to_equal(2)
expect(idx[1]).to_equal(4)
```

</details>

#### byte-not-present returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = scan_byte_scalar(banana(), 122u8)
expect(r.len()).to_equal(0)
```

</details>

#### empty span returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = scan_byte_scalar(ByteSpan.empty(), 97u8)
expect(r.len()).to_equal(0)
```

</details>

### scan_byte dispatch absolute oracle

#### dispatch finds 'a' at exactly 1, 3, 5 (not via self-comparison)

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = scan_byte(banana(), 97u8)
val idx = indices_of(r)
expect(idx.len()).to_equal(3)
expect(idx[0]).to_equal(1)
expect(idx[1]).to_equal(3)
expect(idx[2]).to_equal(5)
```

</details>

#### dispatch byte-not-present returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = scan_byte(banana(), 122u8)
expect(r.len()).to_equal(0)
```

</details>

#### dispatch empty span returns empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = scan_byte(ByteSpan.empty(), 98u8)
expect(r.len()).to_equal(0)
```

</details>

### PARITY SEAM: scan_byte (dispatch) === scan_byte_scalar (oracle)

#### matches the oracle byte-for-byte for 'a' in banana

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sp = banana()
assert_true(pos_list_equals(scan_byte(sp, 97u8), scan_byte_scalar(sp, 97u8)))
```

</details>

#### matches the oracle for 'b' (single, index 0)

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sp = banana()
assert_true(pos_list_equals(scan_byte(sp, 98u8), scan_byte_scalar(sp, 98u8)))
```

</details>

#### matches the oracle for an absent byte (both empty)

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sp = banana()
assert_true(pos_list_equals(scan_byte(sp, 122u8), scan_byte_scalar(sp, 122u8)))
```

</details>

#### matches the oracle on an empty span

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sp = ByteSpan.empty()
assert_true(pos_list_equals(scan_byte(sp, 97u8), scan_byte_scalar(sp, 97u8)))
```

</details>

#### matches the oracle on a single-byte span (byte at index 0 == last index)

- assert true
   - Expected: scan_byte(sp, 42u8).len() equals `1`
   - Expected: scan_byte(sp, 42u8)[0].value() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sp = ByteSpan.new([42u8])
assert_true(pos_list_equals(scan_byte(sp, 42u8), scan_byte_scalar(sp, 42u8)))
expect(scan_byte(sp, 42u8).len()).to_equal(1)
expect(scan_byte(sp, 42u8)[0].value()).to_equal(0)
```

</details>

### active_tier reports the shipped backend honestly

#### is Scalar (no SIMD intrinsics wired this phase)

- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_true(active_tier().is_scalar())
assert_true(active_tier().equals(SimdTier.scalar()))
```

</details>

### scan_byte_haystack over a Haystack

#### finds 'a' at 1,3,5 through the Haystack wrapper

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hay = Haystack.new([98u8, 97u8, 110u8, 97u8, 110u8, 97u8])
val idx = indices_of(scan_byte_haystack(hay, 97u8))
expect(idx.len()).to_equal(3)
expect(idx[0]).to_equal(1)
expect(idx[2]).to_equal(5)
```

</details>

### first_last_byte_filter substring prefilter (absolute oracle)

#### needle 'ana' (first='a',last='a',len=3) yields candidate starts 1 and 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ABSOLUTE oracle: "banana" b[1]='a'&b[3]='a' -> 1; b[3]='a'&b[5]='a' -> 3.
# i=5 cannot fit (5+2=7 out of range), so exactly {1, 3}.
val r = first_last_byte_filter(banana(), 97u8, 97u8, 3)
val idx = indices_of(r)
expect(idx.len()).to_equal(2)
expect(idx[0]).to_equal(1)
expect(idx[1]).to_equal(3)
```

</details>

#### never drops a true match: real 'ana' occurrences (1,3) are both present

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Both candidate starts are genuine "ana" substrings -> no false negatives.
val r = first_last_byte_filter(banana(), 97u8, 97u8, 3)
val idx = indices_of(r)
expect(idx).to_contain(1)
expect(idx).to_contain(3)
```

</details>

#### needle 'ban' (first='b',last='n',len=3) yields candidate start 0 only

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# b[0]='b' & b[2]='n' -> 0. No other 'b'. Absolute oracle {0}.
val r = first_last_byte_filter(banana(), 98u8, 110u8, 3)
val idx = indices_of(r)
expect(idx.len()).to_equal(1)
expect(idx[0]).to_equal(0)
```

</details>

#### needle longer than span yields no candidates

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = first_last_byte_filter(banana(), 98u8, 97u8, 99)
expect(r.len()).to_equal(0)
```

</details>

#### zero-length needle yields no candidates

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = first_last_byte_filter(banana(), 97u8, 97u8, 0)
expect(r.len()).to_equal(0)
```

</details>

### PARITY SEAM: first_last_byte_filter === its scalar oracle

#### dispatch matches scalar for 'ana' in banana

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sp = banana()
val a = first_last_byte_filter(sp, 97u8, 97u8, 3)
val b = first_last_byte_filter_scalar(sp, 97u8, 97u8, 3)
assert_true(pos_list_equals(a, b))
```

</details>

#### dispatch matches scalar for 'ban' in banana

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sp = banana()
val a = first_last_byte_filter(sp, 98u8, 110u8, 3)
val b = first_last_byte_filter_scalar(sp, 98u8, 110u8, 3)
assert_true(pos_list_equals(a, b))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/search/simd_scan_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- scan_byte_scalar absolute oracle (KNOWN positions)
- scan_byte dispatch absolute oracle
- PARITY SEAM: scan_byte (dispatch) === scan_byte_scalar (oracle)
- active_tier reports the shipped backend honestly
- scan_byte_haystack over a Haystack
- first_last_byte_filter substring prefilter (absolute oracle)
- PARITY SEAM: first_last_byte_filter === its scalar oracle

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
