# bitwise_byte_helpers_spec

> B4 (compiler_bugs_for_crypto_2026-04-25.md) — bitfield helpers.

<!-- sdn-diagram:id=bitwise_byte_helpers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bitwise_byte_helpers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bitwise_byte_helpers_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bitwise_byte_helpers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# bitwise_byte_helpers_spec

B4 (compiler_bugs_for_crypto_2026-04-25.md) — bitfield helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/bitwise_byte_helpers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

B4 (compiler_bugs_for_crypto_2026-04-25.md) — bitfield helpers.

The plan's "do this regardless" part: byte/bit slice helpers in stdlib
that crypto-port code can call directly instead of writing
shift-and-mask by hand. These already exist in bitwise_utils.spl —
this spec is the regression guard for the get/set/extract/insert
round-trips that B4's acceptance covers (slice get, slice set,
multi-slice set, aliasing).

The full `int.bits[lo..hi]` syntax sugar is deferred (separate task
B4-sugar — needs parser + HIR variant; helpers cover the semantics).

## Scenarios

### byte helpers (B4)

#### get_byte extracts each byte position

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = 0x1234567890ABCDEF
expect(get_byte(n, 0)).to_equal(0xEF)
expect(get_byte(n, 1)).to_equal(0xCD)
expect(get_byte(n, 2)).to_equal(0xAB)
expect(get_byte(n, 3)).to_equal(0x90)
expect(get_byte(n, 4)).to_equal(0x78)
expect(get_byte(n, 5)).to_equal(0x56)
expect(get_byte(n, 6)).to_equal(0x34)
expect(get_byte(n, 7)).to_equal(0x12)
```

</details>

#### set_byte writes each byte position

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = 0x0
expect(set_byte(n, 0, 0xAB)).to_equal(0xAB)
expect(set_byte(n, 1, 0xAB)).to_equal(0xAB00)
expect(set_byte(n, 3, 0xAB)).to_equal(0xAB000000)
expect(set_byte(n, 7, 0xAB)).to_equal(0xAB00000000000000)
```

</details>

#### set_byte clears the existing byte before writing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = 0xFF
expect(set_byte(n, 0, 0x12)).to_equal(0x12)
```

</details>

#### get/set round-trips for every byte position

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = 0x1234567890ABCDEF
var i = 0
while i < 8:
    val b = get_byte(n, i)
    val updated = set_byte(n, i, b)
    expect(updated).to_equal(n)
    i = i + 1
```

</details>

### bit slice helpers (B4)

#### extract_bits matches plan example

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# extract_bits(0b11010110, 2, 3) -> 0b101
expect(extract_bits(0b11010110, 2, 3)).to_equal(0b101)
```

</details>

#### insert_bits matches plan example

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# insert_bits(0b11110000, 0b101, 2, 3) -> 0b11110100
expect(insert_bits(0b11110000, 0b101, 2, 3)).to_equal(0b11110100)
```

</details>

#### extract/insert round-trip preserves the field

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = 0xDEAD_BEEF
val v = extract_bits(target, 8, 8)   # second-lowest byte
val rewritten = insert_bits(target, v, 8, 8)
expect(rewritten).to_equal(target)
```

</details>

#### multi-slice insert composes (independent fields, no aliasing)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = 0
val with_lo = insert_bits(base, 0xAB, 0, 8)
val with_hi = insert_bits(with_lo, 0xCD, 8, 8)
expect(with_hi).to_equal(0xCDAB)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
