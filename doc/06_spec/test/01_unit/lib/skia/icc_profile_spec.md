# Skia ICC Profile Parser Specification

> Tests for parse_icc_header, parse_icc_tag_table, text2u32, and detect_named_space — the ICC v4 parsing helpers used to classify incoming ICC blobs into an SkColorSpaceKind.

<!-- sdn-diagram:id=icc_profile_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=icc_profile_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

icc_profile_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=icc_profile_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia ICC Profile Parser Specification

Tests for parse_icc_header, parse_icc_tag_table, text2u32, and detect_named_space — the ICC v4 parsing helpers used to classify incoming ICC blobs into an SkColorSpaceKind.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-012 |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/icc_profile_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for parse_icc_header, parse_icc_tag_table, text2u32, and
detect_named_space — the ICC v4 parsing helpers used to classify
incoming ICC blobs into an SkColorSpaceKind.

## Scenarios

### icc_profile

#### parse_icc_header: empty blob returns None

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [u8] = []
val result = parse_icc_header(empty)
expect(result).to_be_nil()
```

</details>

#### parse_icc_header: wrong magic returns None

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blob = _make_header_blob(128, false)
val result = parse_icc_header(blob)
expect(result).to_be_nil()
```

</details>

#### parse_icc_header: valid 128-byte blob with acsp magic returns Some with profile_size

1. Some
   - Expected: hdr.profile_size equals `12345`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blob = _make_header_blob(12345, true)
val result = parse_icc_header(blob)
match result:
    Some(hdr):
        expect(hdr.profile_size).to_equal(12345)
    None:
        expect(false).to_equal(true)
```

</details>

#### parse_icc_tag_table: zero-tag table returns empty list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blob = _make_tag_table_blob([])
val tags = parse_icc_tag_table(blob)
expect(tags.length()).to_equal(0)
```

</details>

#### parse_icc_tag_table: 2-tag table returns list of 2 with correct signatures

1.
2.
   - Expected: tags.length() equals `2`
3. Some
   - Expected: tag0.signature equals `sig_a`
   - Expected: false is true
4. Some
   - Expected: tag1.signature equals `sig_b`
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sig_a = text2u32("rXYZ")
val sig_b = text2u32("gXYZ")
val entries: [(i64, i64, i64)] = [
    (sig_a, 256, 20),
    (sig_b, 276, 20)
]
val blob = _make_tag_table_blob(entries)
val tags = parse_icc_tag_table(blob)
expect(tags.length()).to_equal(2)
val t0 = tags.at(0)
val t1 = tags.at(1)
match t0:
    Some(tag0):
        expect(tag0.signature).to_equal(sig_a)
    None:
        expect(false).to_equal(true)
match t1:
    Some(tag1):
        expect(tag1.signature).to_equal(sig_b)
    None:
        expect(false).to_equal(true)
```

</details>

#### text2u32: wtpt maps to 0x77747074 (2003789940)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = text2u32("wtpt")
expect(v).to_equal(2003789940)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
