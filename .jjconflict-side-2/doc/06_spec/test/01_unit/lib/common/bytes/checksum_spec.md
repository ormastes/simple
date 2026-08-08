# Checksum Specification

> <details>

<!-- sdn-diagram:id=checksum_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=checksum_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

checksum_spec -> std
checksum_spec -> lib
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=checksum_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Checksum Specification

## Scenarios

### Crc32

#### CRC32(\

- var c = Crc32 new
- c update
   - Expected: c.raw() equals `0xCBF43926`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = Crc32.new()
c.update(ByteSpan.new(check_input()))
expect(c.raw()).to_equal(0xCBF43926)
```

</details>

#### CRC32 of empty input == 0

- var c = Crc32 new
- c update
   - Expected: c.raw() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = Crc32.new()
c.update(ByteSpan.empty())
expect(c.raw()).to_equal(0)
```

</details>

#### incremental update matches single update

- var whole = Crc32 new
- whole update
- var parts = Crc32 new
- parts update
- parts update
   - Expected: parts.raw() equals `whole.raw()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = check_input()
var whole = Crc32.new()
whole.update(ByteSpan.new(data))
var parts = Crc32.new()
parts.update(ByteSpan.of(data, 0, 4))
parts.update(ByteSpan.of(data, 4, 5))
expect(parts.raw()).to_equal(whole.raw())
```

</details>

#### value() returns big-endian byte view of the CRC

- var c = Crc32 new
- c update
   - Expected: be.get(0).to_i64() equals `0xCB`
   - Expected: be.get(1).to_i64() equals `0xF4`
   - Expected: be.get(2).to_i64() equals `0x39`
   - Expected: be.get(3).to_i64() equals `0x26`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = Crc32.new()
c.update(ByteSpan.new(check_input()))
val be = c.value().to_span()
expect(be.get(0).to_i64()).to_equal(0xCB)
expect(be.get(1).to_i64()).to_equal(0xF4)
expect(be.get(2).to_i64()).to_equal(0x39)
expect(be.get(3).to_i64()).to_equal(0x26)
```

</details>

### Adler32

#### Adler32(\

- var a = Adler32 new
- a update
   - Expected: a.raw() equals `0x091E01DE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = Adler32.new()
a.update(ByteSpan.new(check_input()))
expect(a.raw()).to_equal(0x091E01DE)
```

</details>

#### Adler32 of empty input == 1

- var a = Adler32 new
- a update
   - Expected: a.raw() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = Adler32.new()
a.update(ByteSpan.empty())
expect(a.raw()).to_equal(1)
```

</details>

#### incremental update matches single update

- var whole = Adler32 new
- whole update
- var parts = Adler32 new
- parts update
- parts update
   - Expected: parts.raw() equals `whole.raw()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = check_input()
var whole = Adler32.new()
whole.update(ByteSpan.new(data))
var parts = Adler32.new()
parts.update(ByteSpan.of(data, 0, 3))
parts.update(ByteSpan.of(data, 3, 6))
expect(parts.raw()).to_equal(whole.raw())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/bytes/checksum_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Crc32
- Adler32

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
