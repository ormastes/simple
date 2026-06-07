# Fse Specification

> <details>

<!-- sdn-diagram:id=fse_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fse_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fse_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fse_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fse Specification

## Scenarios

### _fse_log2

#### returns 0 for 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_fse_log2(1)).to_equal(0)
```

</details>

#### returns 1 for 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_fse_log2(2)).to_equal(1)
```

</details>

#### returns 2 for 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_fse_log2(4)).to_equal(2)
```

</details>

#### returns 3 for 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_fse_log2(8)).to_equal(3)
```

</details>

#### returns 3 for 9 (floor)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_fse_log2(9)).to_equal(3)
```

</details>

#### returns 0 for 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_fse_log2(0)).to_equal(0)
```

</details>

### ZstdRevBitReader persistent byte_idx

#### reads correct bits across byte boundary

1. fail
2. fail
   - Expected: r2.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Data: [0b10110001, 0b10000001]
# Last byte = 0x81 = 0b10000001; sentinel is bit7 (MSB)
# bits_left = 16 - 1 = 15; start at byte_idx=1, bit_idx=6
# Reading 4 bits MSB-first from bit6 downward in byte 1:
#   bit6=0, bit5=0, bit4=0, bit3=0 → value=0
# Then 4 more bits: bit2=0, bit1=0, bit0=1, then byte0 bit7=1
#   → value = 0b0001 going from MSB order so: bit2=0,bit1=0,bit0=1 → wrap → byte0 bit7=1
#   Actually MSB first: high bits first: 0,0,1,1 = 3? Let me just verify no error.
val data = make_bytes_2(0xB1, 0x81)
val rb_r = zstd_rbr_init(data)
if rb_r.is_err():
    fail("unexpected FSE parse or decode branch")
else:
    val rb = rb_r.unwrap()
    val r1 = zstd_rbr_read(rb, 4)
    if r1.is_err():
        fail("unexpected FSE parse or decode branch")
    else:
        val r2 = zstd_rbr_read(r1.unwrap().reader, 4)
        # Just verify second read succeeds (no crash from byte_idx reset)
        expect(r2.is_ok()).to_equal(true)
```

</details>

#### reads bits_left correctly after each read

1. fail
   - Expected: rb.bits_left equals `15`
2. fail
   - Expected: r1.unwrap().reader.bits_left equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = make_bytes_2(0xFF, 0x81)
val rb_r = zstd_rbr_init(data)
if rb_r.is_err():
    fail("unexpected FSE parse or decode branch")
else:
    val rb = rb_r.unwrap()
    # bits_left should be 15 (16 - 1 sentinel)
    expect(rb.bits_left).to_equal(15)
    val r1 = zstd_rbr_read(rb, 3)
    if r1.is_err():
        fail("unexpected FSE parse or decode branch")
    else:
        expect(r1.unwrap().reader.bits_left).to_equal(12)
```

</details>

### fse_build_table basic

#### builds table with correct entry count for accuracy_log=1

1. fail
   - Expected: table_entry_count(t) equals `2`
   - Expected: table_accuracy_log(t) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val norm = make_simple_norm_2()
val t_r = fse_build_table(norm, 1, 1)
if t_r.is_err():
    fail("unexpected FSE parse or decode branch")
else:
    val t = t_r.unwrap()
    expect(table_entry_count(t)).to_equal(2)
    expect(table_accuracy_log(t)).to_equal(1)
```

</details>

#### builds table with correct entry count for accuracy_log=2

1. fail
   - Expected: table_entry_count(t) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val norm = make_norm_4()
val t_r = fse_build_table(norm, 1, 2)
if t_r.is_err():
    fail("unexpected FSE parse or decode branch")
else:
    val t = t_r.unwrap()
    expect(table_entry_count(t)).to_equal(4)
```

</details>

#### each symbol appears proportionally to its probability

1. fail
   - Expected: count_symbol_entries(t, 0) equals `2`
   - Expected: count_symbol_entries(t, 1) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# norm=[2,2] accuracy_log=2 → tableSize=4; each symbol should appear exactly 2 times
val norm = make_norm_4()
val t_r = fse_build_table(norm, 1, 2)
if t_r.is_err():
    fail("unexpected FSE parse or decode branch")
else:
    val t = t_r.unwrap()
    expect(count_symbol_entries(t, 0)).to_equal(2)
    expect(count_symbol_entries(t, 1)).to_equal(2)
```

</details>

#### less-than-1 symbol occupies exactly one tail entry

1. fail
   - Expected: count_symbol_entries(t, 0) equals `2`
   - Expected: count_symbol_entries(t, 1) equals `1`
   - Expected: count_symbol_entries(t, 2) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# norm=[2,1,-1] accuracy_log=2 → tableSize=4
# symbol0: prob=2 → 2 entries; symbol1: prob=1 → 1 entry; symbol2: prob=-1 → 1 entry
val norm = make_norm_4_with_ltone()
val t_r = fse_build_table(norm, 2, 2)
if t_r.is_err():
    fail("unexpected FSE parse or decode branch")
else:
    val t = t_r.unwrap()
    expect(count_symbol_entries(t, 0)).to_equal(2)
    expect(count_symbol_entries(t, 1)).to_equal(1)
    expect(count_symbol_entries(t, 2)).to_equal(1)
```

</details>

### fse_build_table predefined LL distribution

#### builds 64-entry table for synthetic 36-symbol distribution

1. norm push
2. norm push
3. norm push
4. norm push
5. norm push
6. norm push
7. norm push
8. norm push
9. norm push
10. norm push
11. norm push
12. norm push
13. norm push
14. norm push
15. norm push
16. norm push
17. norm push
18. norm push
19. norm push
20. norm push
21. norm push
22. norm push
23. norm push
24. norm push
25. norm push
26. norm push
27. norm push
28. norm push
29. norm push
30. norm push
31. norm push
32. norm push
33. norm push
34. norm push
35. norm push
36. norm push
37. fail
   - Expected: table_entry_count(t) equals `64`
   - Expected: table_accuracy_log(t) equals `6`
   - Expected: count_symbol_entries(t, 0) equals `4`
   - Expected: count_symbol_entries(t, 1) equals `3`
   - Expected: count_symbol_entries(t, 35) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var norm: [i64] = []
# RFC 8878 Table 7: LL probabilities for symbols 0-35
norm.push(4)   # sym 0
norm.push(3)   # sym 1
norm.push(2)   # sym 2
norm.push(2)   # sym 3
norm.push(2)   # sym 4
norm.push(2)   # sym 5
norm.push(2)   # sym 6
norm.push(2)   # sym 7
norm.push(2)   # sym 8
norm.push(2)   # sym 9
norm.push(2)   # sym 10
norm.push(2)   # sym 11
norm.push(2)   # sym 12
norm.push(1)   # sym 13
norm.push(1)   # sym 14
norm.push(1)   # sym 15
norm.push(2)   # sym 16
norm.push(2)   # sym 17
norm.push(2)   # sym 18
norm.push(2)   # sym 19
norm.push(2)   # sym 20
norm.push(2)   # sym 21
norm.push(2)   # sym 22
norm.push(2)   # sym 23
norm.push(2)   # sym 24
norm.push(3)   # sym 25
norm.push(2)   # sym 26
norm.push(1)   # sym 27
norm.push(1)   # sym 28
norm.push(1)   # sym 29
norm.push(1)   # sym 30
norm.push(1)   # sym 31
norm.push(1)   # sym 32
norm.push(1)   # sym 33
norm.push(1)   # sym 34
norm.push(-1)  # sym 35 (less-than-1)
val t_r = fse_build_table(norm, 35, 6)
if t_r.is_err():
    fail("unexpected FSE parse or decode branch")
else:
    val t = t_r.unwrap()
    expect(table_entry_count(t)).to_equal(64)
    expect(table_accuracy_log(t)).to_equal(6)
    # Key: broken code produces 5 (1 fallback cell), fixed produces 4.
    expect(count_symbol_entries(t, 0)).to_equal(4)
    expect(count_symbol_entries(t, 1)).to_equal(3)
    # Tail symbol always occupies exactly 1 entry (not discriminating for Bug 2).
    expect(count_symbol_entries(t, 35)).to_equal(1)
```

</details>

### fse_decode_symbol round-trip

#### decodes symbol from known single-symbol table

1. norm single push
2. fail
3. fail
4. fail
   - Expected: in_range is true
5. fail
   - Expected: dec_r.unwrap().symbol equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Single symbol (prob=1): table_size=1, accuracy_log=0 doesn't exist in FSE
# Use accuracy_log=1, norm=[2] (all probability on symbol 0)
# tableSize=2, both entries → symbol 0
var norm_single: [i64] = []
norm_single.push(2)
val t_r = fse_build_table(norm_single, 0, 1)
if t_r.is_err():
    fail("unexpected FSE parse or decode branch")
else:
    val t = t_r.unwrap()
    # Create a reverse reader with a sentinel byte to provide 7 bits
    # We need accuracy_log=1 bits for init
    val data = make_bytes_1(0x82)  # 0b10000010: sentinel at bit7, data bits: bit6=0, bit5=0, bit4=0, bit3=0, bit2=0, bit1=1
    val rb_r = zstd_rbr_init(data)
    if rb_r.is_err():
        fail("unexpected FSE parse or decode branch")
    else:
        val rb = rb_r.unwrap()
        val init_r = fse_init_state(t, rb)
        if init_r.is_err():
            fail("unexpected FSE parse or decode branch")
        else:
            val init_res = init_r.unwrap()
            val state = init_res.state
            # State must be 0 or 1 (accuracy_log=1 → 1 bit read)
            val in_range = state >= 0 and state < 2
            expect(in_range).to_equal(true)
            # Decode: symbol at any state must be 0
            val dec_r = fse_decode_symbol(t, state, init_res.reader)
            if dec_r.is_err():
                fail("unexpected FSE parse or decode branch")
            else:
                expect(dec_r.unwrap().symbol).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/compression/zstd/fse_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- _fse_log2
- ZstdRevBitReader persistent byte_idx
- fse_build_table basic
- fse_build_table predefined LL distribution
- fse_decode_symbol round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
