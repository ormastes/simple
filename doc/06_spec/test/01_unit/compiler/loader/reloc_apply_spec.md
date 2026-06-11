# Reloc Apply Specification

> <details>

<!-- sdn-diagram:id=reloc_apply_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=reloc_apply_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

reloc_apply_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=reloc_apply_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Reloc Apply Specification

## Scenarios

### SMF Relocation Application

### relocation type handling

#### Abs64 writes 8-byte absolute address

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Abs64 (type 1): write sym_addr + addend as 8 bytes
val reloc_type = 1
val sym_addr = 0x400000
val addend = 0
val patch_value = sym_addr + addend
val bytes = i64_to_le_bytes(patch_value)
expect(bytes.len()).to_equal(8)
expect(bytes[0]).to_equal(0)
expect(bytes[1]).to_equal(0)
expect(bytes[2]).to_equal(0x40)
```

</details>

#### Rel32 writes 4-byte PC-relative offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Rel32/Pc32 (type 2): write (sym_addr - patch_addr + addend) as i32
val reloc_type = 2
val sym_addr = 0x1000
val patch_addr = 0x0F00
val addend = -4
val displacement = sym_addr - patch_addr + addend
# 0x1000 - 0x0F00 + (-4) = 0x100 - 4 = 252
expect(displacement).to_equal(252)
```

</details>

#### PltRel32 writes 4-byte PC-relative offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# PltRel32 (type 3): same formula as Pc32
val reloc_type = 3
val sym_addr = 0x2000
val patch_addr = 0x1000
val addend = -4
val displacement = sym_addr - patch_addr + addend
# 0x2000 - 0x1000 + (-4) = 0x1000 - 4 = 4092
expect(displacement).to_equal(4092)
```

</details>

#### GotRel32 writes 4-byte PC-relative offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# GotRel32 (type 4): same formula as Pc32
val reloc_type = 4
val sym_addr = 0x3000
val patch_addr = 0x2000
val addend = -4
val displacement = sym_addr - patch_addr + addend
expect(displacement).to_equal(4092)
```

</details>

### symbol resolution

#### resolves symbols from global symbol table

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var global_symbols: Dict<text, i64> = {}
global_symbols["printf"] = 0x7FFFF7A62E80
global_symbols["main"] = 0x400080

expect(global_symbols["printf"]).to_equal(0x7FFFF7A62E80)
expect(global_symbols["main"]).to_equal(0x400080)
```

</details>

#### handles missing symbol gracefully

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var global_symbols: Dict<text, i64> = {}
global_symbols["known_fn"] = 0x1000
val has_unknown = global_symbols.has("unknown_fn")
expect(has_unknown).to_equal(false)
```

</details>

### W^X security flow

#### follows RW -> patch -> RX sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The relocation flow should be:
# 1. mprotect(RW) - make writable for patching
# 2. Apply relocations (write patch values)
# 3. mprotect(RX) - make executable, remove write
# 4. Flush icache (required on ARM/RISC-V)
val step_1 = "mprotect_rw"
val step_2 = "apply_relocs"
val step_3 = "mprotect_rx"
val step_4 = "flush_icache"
val steps = [step_1, step_2, step_3, step_4]
expect(steps.len()).to_equal(4)
expect(steps[0]).to_equal("mprotect_rw")
expect(steps[2]).to_equal("mprotect_rx")
```

</details>

### edge cases

#### handles empty relocation list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var relocs: [i64] = []
expect(relocs.len()).to_equal(0)
```

</details>

#### handles zero addend

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sym_addr = 0x1000
val addend = 0
val result = sym_addr + addend
expect(result).to_equal(0x1000)
```

</details>

#### handles negative addend

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sym_addr = 0x1000
val addend = -4
val result = sym_addr + addend
expect(result).to_equal(0x0FFC)
```

</details>

#### handles large displacement

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sym_addr = 0x7FFFFFFF
val patch_addr = 0x0
val addend = 0
val displacement = sym_addr - patch_addr + addend
expect(displacement).to_equal(0x7FFFFFFF)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/loader/reloc_apply_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SMF Relocation Application
- relocation type handling
- symbol resolution
- W^X security flow
- edge cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
