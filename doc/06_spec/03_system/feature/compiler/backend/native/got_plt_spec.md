# GOT/PLT Builder for Native Backend

> Tests the GOT (Global Offset Table) and PLT (Procedure Linkage Table) generation for the native backend. Verifies that dynamic symbol references are correctly resolved through GOT/PLT entries for position-independent executables.

<!-- sdn-diagram:id=got_plt_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=got_plt_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

got_plt_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=got_plt_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GOT/PLT Builder for Native Backend

Tests the GOT (Global Offset Table) and PLT (Procedure Linkage Table) generation for the native backend. Verifies that dynamic symbol references are correctly resolved through GOT/PLT entries for position-independent executables.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/compiler/backend/native/got_plt_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the GOT (Global Offset Table) and PLT (Procedure Linkage Table) generation
for the native backend. Verifies that dynamic symbol references are correctly
resolved through GOT/PLT entries for position-independent executables.

## Scenarios

### GOT/PLT Builder - Basic Structure

#### creates new builder with empty state

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = GotPltBuilder(
    got_entries: [],
    plt_entries: [],
    got_size: 0,
    plt_size: 0,
    next_got_offset: 0,
    next_plt_index: 0
)
expect(builder.got_entries.len()).to_equal(0)
expect(builder.plt_entries.len()).to_equal(0)
expect(builder.next_got_offset).to_equal(0)
expect(builder.next_plt_index).to_equal(0)
```

</details>

#### calculates GOT size correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = GotPltBuilder(
    got_entries: [],
    plt_entries: [],
    got_size: 0,
    plt_size: 0,
    next_got_offset: 24,  # 3 entries * 8 bytes
    next_plt_index: 0
)
expect(builder.get_got_size()).to_equal(24)
```

</details>

#### calculates PLT size correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val builder = GotPltBuilder(
    got_entries: [],
    plt_entries: [],
    got_size: 0,
    plt_size: 0,
    next_got_offset: 0,
    next_plt_index: 3  # 3 entries
)
expect(builder.get_plt_size()).to_equal(48)  # 3 * 16 bytes
```

</details>

### GOT/PLT Builder - PLT Stub Generation

#### generates valid x86_64 PLT stub

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stub = generate_plt_stub_x86_64(0, 0)
# Should be 16 bytes
expect(stub.len()).to_equal(16)
# First byte should be 0xFF (JMP opcode)
expect(stub[0]).to_equal(0xFF)
# Second byte should be 0x25 (ModRM for RIP-relative)
expect(stub[1]).to_equal(0x25)
```

</details>

#### includes PLT index in stub

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stub = generate_plt_stub_x86_64(42, 0)
# Byte 6 should be 0x68 (PUSH opcode)
expect(stub[6]).to_equal(0x68)
# Bytes 7-10 should encode 42 in little-endian
expect(stub[7]).to_equal(42)
expect(stub[8]).to_equal(0)
expect(stub[9]).to_equal(0)
expect(stub[10]).to_equal(0)
```

</details>

#### includes GOT offset in stub

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stub = generate_plt_stub_x86_64(0, 256)
# Bytes 2-5 encode GOT offset (256) in little-endian
expect(stub[2]).to_equal(0)
expect(stub[3]).to_equal(1)  # 256 = 0x0100
expect(stub[4]).to_equal(0)
expect(stub[5]).to_equal(0)
```

</details>

### GOT/PLT Builder - Symbol Management

#### adds first symbol correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = GotPltBuilder(
    got_entries: [],
    plt_entries: [],
    got_size: 0,
    plt_size: 0,
    next_got_offset: 0,
    next_plt_index: 0
)
val index = builder.add_symbol("printf")
expect(index).to_equal(0)
expect(builder.got_entries.len()).to_equal(1)
expect(builder.plt_entries.len()).to_equal(1)
```

</details>

#### allocates GOT entry with correct offset

1. builder add symbol
   - Expected: entry.symbol equals `malloc`
   - Expected: entry.offset equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = GotPltBuilder(
    got_entries: [],
    plt_entries: [],
    got_size: 0,
    plt_size: 0,
    next_got_offset: 0,
    next_plt_index: 0
)
builder.add_symbol("malloc")
val entry = builder.got_entries[0]
expect(entry.symbol).to_equal("malloc")
expect(entry.offset).to_equal(0)
```

</details>

#### increments GOT offset by 8 bytes per symbol

1. builder add symbol
2. builder add symbol
   - Expected: builder.next_got_offset equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = GotPltBuilder(
    got_entries: [],
    plt_entries: [],
    got_size: 0,
    plt_size: 0,
    next_got_offset: 0,
    next_plt_index: 0
)
builder.add_symbol("printf")
builder.add_symbol("malloc")
expect(builder.next_got_offset).to_equal(16)
```

</details>

#### reuses existing symbol without duplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = GotPltBuilder(
    got_entries: [],
    plt_entries: [],
    got_size: 0,
    plt_size: 0,
    next_got_offset: 0,
    next_plt_index: 0
)
val idx1 = builder.add_symbol("printf")
val idx2 = builder.add_symbol("printf")
expect(idx1).to_equal(idx2)
expect(builder.plt_entries.len()).to_equal(1)
expect(builder.got_entries.len()).to_equal(1)
```

</details>

### GOT/PLT Builder - Multiple Symbols

#### handles multiple unique symbols

1. builder add symbol
2. builder add symbol
3. builder add symbol
   - Expected: builder.plt_entries.len() equals `3`
   - Expected: builder.got_entries.len() equals `3`
   - Expected: builder.get_got_size() equals `24)  # 3 * 8 bytes`
   - Expected: builder.get_plt_size() equals `48)  # 3 * 16 bytes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = GotPltBuilder(
    got_entries: [],
    plt_entries: [],
    got_size: 0,
    plt_size: 0,
    next_got_offset: 0,
    next_plt_index: 0
)
builder.add_symbol("printf")
builder.add_symbol("malloc")
builder.add_symbol("free")
expect(builder.plt_entries.len()).to_equal(3)
expect(builder.got_entries.len()).to_equal(3)
expect(builder.get_got_size()).to_equal(24)  # 3 * 8 bytes
expect(builder.get_plt_size()).to_equal(48)  # 3 * 16 bytes
```

</details>

#### assigns sequential indices to symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = GotPltBuilder(
    got_entries: [],
    plt_entries: [],
    got_size: 0,
    plt_size: 0,
    next_got_offset: 0,
    next_plt_index: 0
)
val idx0 = builder.add_symbol("printf")
val idx1 = builder.add_symbol("malloc")
val idx2 = builder.add_symbol("free")
expect(idx0).to_equal(0)
expect(idx1).to_equal(1)
expect(idx2).to_equal(2)
```

</details>

#### assigns correct GOT offsets

1. builder add symbol
2. builder add symbol
3. builder add symbol
   - Expected: builder.got_entries[0].offset equals `0`
   - Expected: builder.got_entries[1].offset equals `8`
   - Expected: builder.got_entries[2].offset equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var builder = GotPltBuilder(
    got_entries: [],
    plt_entries: [],
    got_size: 0,
    plt_size: 0,
    next_got_offset: 0,
    next_plt_index: 0
)
builder.add_symbol("printf")
builder.add_symbol("malloc")
builder.add_symbol("free")
expect(builder.got_entries[0].offset).to_equal(0)
expect(builder.got_entries[1].offset).to_equal(8)
expect(builder.got_entries[2].offset).to_equal(16)
```

</details>

### GOT/PLT Builder - Helper Functions

#### encodes i32 in little-endian

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = encode_i32_le(0x12345678)
expect(bytes[0]).to_equal(0x78)
expect(bytes.len()).to_equal(4)
expect(bytes[1]).to_equal(0x56)
expect(bytes[2]).to_equal(0x34)
expect(bytes[3]).to_equal(0x12)
```

</details>

#### encodes zero correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = encode_i32_le(0)
expect(bytes[0]).to_equal(0)
expect(bytes.len()).to_equal(4)
expect(bytes[1]).to_equal(0)
expect(bytes[2]).to_equal(0)
expect(bytes[3]).to_equal(0)
```

</details>

#### encodes small positive number

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes = encode_i32_le(42)
expect(bytes[0]).to_equal(42)
expect(bytes.len()).to_equal(4)
expect(bytes[1]).to_equal(0)
expect(bytes[2]).to_equal(0)
expect(bytes[3]).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
