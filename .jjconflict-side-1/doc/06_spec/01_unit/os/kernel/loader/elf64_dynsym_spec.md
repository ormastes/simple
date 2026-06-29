# ELF64 dynamic symbol resolution

> Verifies section header parsing and .dynsym/.symtab symbol lookup

<!-- sdn-diagram:id=elf64_dynsym_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=elf64_dynsym_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

elf64_dynsym_spec -> std
elf64_dynsym_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=elf64_dynsym_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ELF64 dynamic symbol resolution

Verifies section header parsing and .dynsym/.symtab symbol lookup

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #WAVE2-G10-DYNSYM |
| Category | Kernel loader |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/elf64_dynsym_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies section header parsing and .dynsym/.symtab symbol lookup
from a minimal hand-crafted ELF64 binary with embedded symbol tables.

## Scenarios

### elf64_has_magic

#### detects ELF magic at offset 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _make_elf64_with_dynsym()
expect(elf64_has_magic(data)).to_equal(true)
```

</details>

#### rejects non-ELF bytes

1. data push
2. data push
3. data push
4. data push
   - Expected: elf64_has_magic(data) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data: [u8] = []
data.push(0.to_u8())
data.push(0.to_u8())
data.push(0.to_u8())
data.push(0.to_u8())
expect(elf64_has_magic(data)).to_equal(false)
```

</details>

### elf64_parse_section_headers

#### parses section headers from minimal ELF64

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _make_elf64_with_dynsym()
val hdr_opt = elf64_parse_header(data)
val hdr = hdr_opt.unwrap()
val shdrs = elf64_parse_section_headers(data, hdr)
expect(shdrs.len()).to_equal(3)
```

</details>

#### finds .dynsym section by type

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _make_elf64_with_dynsym()
val hdr = elf64_parse_header(data).unwrap()
val shdrs = elf64_parse_section_headers(data, hdr)
val dynsym_opt = elf64_find_section_by_type(shdrs, 11)
val dynsym = dynsym_opt.unwrap()
expect(dynsym.sh_type).to_equal(11)
```

</details>

### elf64_dynsym_lookup

#### resolves a known symbol from .dynsym

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _make_elf64_with_dynsym()
val hdr = elf64_parse_header(data).unwrap()
val shdrs = elf64_parse_section_headers(data, hdr)
val result = elf64_dynsym_lookup(data, shdrs, "hello")
val addr = result.unwrap()
expect(addr).to_equal(0xDEAD.to_u64())
```

</details>

#### returns nil for an unknown symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = _make_elf64_with_dynsym()
val hdr = elf64_parse_header(data).unwrap()
val shdrs = elf64_parse_section_headers(data, hdr)
val result = elf64_dynsym_lookup(data, shdrs, "nonexistent")
expect(result == nil).to_equal(true)
```

</details>

### elf64_strtab_get

#### extracts NUL-terminated strings from strtab

1. strtab push
2. strtab push
3. strtab push
4. strtab push
   - Expected: elf64_strtab_get(strtab, 0) equals ``
   - Expected: elf64_strtab_get(strtab, 1) equals `AB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var strtab: [u8] = []
strtab.push(0.to_u8())       # index 0: empty
strtab.push(0x41.to_u8())    # index 1: "AB"
strtab.push(0x42.to_u8())
strtab.push(0.to_u8())
expect(elf64_strtab_get(strtab, 0)).to_equal("")
expect(elf64_strtab_get(strtab, 1)).to_equal("AB")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
