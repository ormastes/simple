# Archive Parser Specification

> _Tests for ar magic byte validation._

<!-- sdn-diagram:id=archive_parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=archive_parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

archive_parser_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=archive_parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Archive Parser Specification

## Scenarios

### ArParser - Magic
_Tests for ar magic byte validation._

#### accepts correct !<arch>\\n magic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0x21, 0x3C, 0x61, 0x72, 0x63, 0x68, 0x3E, 0x0A]
expect(ar_check_magic(bytes)).to_equal(true)
```

</details>

#### rejects wrong first byte

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0x00, 0x3C, 0x61, 0x72, 0x63, 0x68, 0x3E, 0x0A]
expect(ar_check_magic(bytes)).to_equal(false)
```

</details>

#### rejects truncated magic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0x21, 0x3C, 0x61]
expect(ar_check_magic(bytes)).to_equal(false)
```

</details>

#### rejects empty bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = []
expect(ar_check_magic(bytes)).to_equal(false)
```

</details>

#### rejects all-zero bytes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0, 0, 0, 0, 0, 0, 0, 0]
expect(ar_check_magic(bytes)).to_equal(false)
```

</details>

### ArParser - Size parsing
_Tests for decimal size field parsing._

#### parses a simple size 42

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "42        " → 42 (10 bytes, space-padded)
val bytes: [i64] = [
    0x34, 0x32, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20,
]
expect(ar_parse_size(bytes, 0)).to_equal(42)
```

</details>

#### parses size 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [
    0x30, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20,
]
expect(ar_parse_size(bytes, 0)).to_equal(0)
```

</details>

#### parses large size 1024

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "1024      "
val bytes: [i64] = [
    0x31, 0x30, 0x32, 0x34, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20,
]
expect(ar_parse_size(bytes, 0)).to_equal(1024)
```

</details>

#### strips trailing spaces from size field

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "7         " → 7
val bytes: [i64] = [
    0x37, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20,
]
expect(ar_parse_size(bytes, 0)).to_equal(7)
```

</details>

### ArParser - Minimal archive
_Tests parsing a minimal archive with one member._

#### parses member name

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [i64] = [0x41, 0x42, 0x43]  # "ABC"
val archive = make_one_member_archive("foo.o", data)
val result = ar_parse(archive)
expect(result.is_ok()).to_equal(true)
val reader = result.unwrap()
expect(reader.members.len()).to_equal(1)
expect(reader.members[0].name).to_equal("foo.o")
```

</details>

#### parses member size

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [i64] = [0x41, 0x42, 0x43]  # 3 bytes
val archive = make_one_member_archive("foo.o", data)
val result = ar_parse(archive)
expect(result.is_ok()).to_equal(true)
val reader = result.unwrap()
expect(reader.members[0].size).to_equal(3)
```

</details>

#### parses member data_offset correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [i64] = [0x41, 0x42, 0x43]
val archive = make_one_member_archive("foo.o", data)
val result = ar_parse(archive)
expect(result.is_ok()).to_equal(true)
val reader = result.unwrap()
# data_offset = magic(8) + header(60) = 68
expect(reader.members[0].data_offset).to_equal(68)
```

</details>

#### sets is_valid true for a valid archive

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [i64] = [1, 2, 3]
val archive = make_one_member_archive("a.o", data)
val result = ar_parse(archive)
expect(result.is_ok()).to_equal(true)
expect(result.unwrap().is_valid).to_equal(true)
```

</details>

### ArParser - Member count
_Tests ar_member_count._

#### counts one member

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val archive = make_one_member_archive("a.o", [1, 2])
val reader = ar_parse(archive).unwrap()
expect(ar_member_count(reader)).to_equal(1)
```

</details>

#### counts two members

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val archive = make_two_member_archive_count()
val reader = ar_parse(archive).unwrap()
expect(ar_member_count(reader)).to_equal(2)
```

</details>

### ArParser - Name stripping
_Tests that trailing spaces and slashes are stripped from names._

#### strips trailing spaces from plain name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val archive = make_one_member_archive("foo.o", [1])
val reader = ar_parse(archive).unwrap()
expect(reader.members[0].name).to_equal("foo.o")
```

</details>

#### preserves special name /

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val archive = make_one_member_archive("/", [1, 2, 3, 4])
val reader = ar_parse(archive).unwrap()
expect(reader.members[0].name).to_equal("/")
```

</details>

#### preserves special name //

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val archive = make_one_member_archive("//", [0x20])
val reader = ar_parse(archive).unwrap()
expect(reader.members[0].name).to_equal("//")
```

</details>

### ArParser - Find member
_Tests ar_find_member._

#### finds member by name

- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val archive = make_find_member_archive()
val reader = ar_parse(archive).unwrap()
val found = ar_find_member(reader, "beta.o")
match found:
    case Some(m):
        expect(m.name).to_equal("beta.o")
    case nil:
        fail("expected archive member beta.o")
```

</details>

#### returns nil for missing member

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val archive = make_one_member_archive("foo.o", [1])
val reader = ar_parse(archive).unwrap()
val found = ar_find_member(reader, "missing.o")
# Hoisted: the runner rewrites `expect(found == nil).to_equal(true)` into
# an ambiguous chained `expect found == nil == true` it mis-evaluates.
# Comparing a precomputed bool is the identical assertion and rewrites cleanly.
val found_is_nil = found == nil
expect(found_is_nil).to_equal(true)
```

</details>

### ArParser - List names
_Tests ar_list_names._

#### lists all member names in order

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val archive = make_list_names_archive()
val reader = ar_parse(archive).unwrap()
val names = ar_list_names(reader)
expect(names.len()).to_equal(2)
expect(names[0]).to_equal("first.o")
expect(names[1]).to_equal("second.o")
```

</details>

#### returns empty list for archive with no members

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val archive = ar_magic()
val reader = ar_parse(archive).unwrap()
val names = ar_list_names(reader)
expect(names.len()).to_equal(0)
```

</details>

### ArParser - Error cases
_Tests error handling for malformed archives._

#### errors on archive too short for magic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0x21, 0x3C]
val result = ar_parse(bytes)
expect(result.is_err()).to_equal(true)
```

</details>

#### errors on wrong magic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bytes: [i64] = [0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
val result = ar_parse(bytes)
expect(result.is_err()).to_equal(true)
```

</details>

#### handles archive with truncated header gracefully

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Valid magic + 30 bytes (less than 60-byte header): no valid fmag present
val bytes: [i64] = [
    0x21, 0x3C, 0x61, 0x72, 0x63, 0x68, 0x3E, 0x0A,
    0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20,
    0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20,
    0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20, 0x20,
    0x20, 0x20, 0x20, 0x20, 0x20, 0x20,
]
# Truncated header: parser stops with 0 members (header loop condition fails)
val result = ar_parse(bytes)
if result.is_ok():
    expect(result.unwrap().members.len()).to_equal(0)
else:
    expect(result.is_err()).to_equal(true)
```

</details>

### ArParser - Member data extraction
_Tests ar_member_data._

#### extracts correct data bytes for a single member

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data: [i64] = [0x7F, 0x45, 0x4C, 0x46]  # ELF magic bytes
val archive = make_one_member_archive("obj.o", data)
val reader = ar_parse(archive).unwrap()
val extracted = ar_member_data(reader, reader.members[0])
expect(extracted.len()).to_equal(4)
expect(extracted[0]).to_equal(0x7F)
expect(extracted[1]).to_equal(0x45)
expect(extracted[2]).to_equal(0x4C)
expect(extracted[3]).to_equal(0x46)
```

</details>

### ArParser - Odd-size padding
_Tests that 1-byte padding after odd-size members is handled correctly._

#### parses two members when first has odd size

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val archive = make_odd_padding_archive()
val reader = ar_parse(archive).unwrap()
expect(ar_member_count(reader)).to_equal(2)
expect(reader.members[0].name).to_equal("a.o")
expect(reader.members[1].name).to_equal("b.o")
val d2 = ar_member_data(reader, reader.members[1])
expect(d2[0]).to_equal(0x04)
expect(d2[1]).to_equal(0x05)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/linker/archive_parser_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ArParser - Magic
- ArParser - Size parsing
- ArParser - Minimal archive
- ArParser - Member count
- ArParser - Name stripping
- ArParser - Find member
- ArParser - List names
- ArParser - Error cases
- ArParser - Member data extraction
- ArParser - Odd-size padding

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
