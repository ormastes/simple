# Sym Resolver Specification

> <details>

<!-- sdn-diagram:id=sym_resolver_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sym_resolver_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sym_resolver_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sym_resolver_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sym Resolver Specification

## Scenarios

### SymResolver - elf_binding_to_sym

#### STB_LOCAL maps to SymBinding.Local

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = elf_binding_to_sym(STB_LOCAL)
expect(b == SymBinding.Local).to_equal(true)
```

</details>

#### STB_GLOBAL maps to SymBinding.Global

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = elf_binding_to_sym(STB_GLOBAL)
expect(b == SymBinding.Global).to_equal(true)
```

</details>

#### STB_WEAK maps to SymBinding.Weak

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = elf_binding_to_sym(STB_WEAK)
expect(b == SymBinding.Weak).to_equal(true)
```

</details>

### SymResolver - sym_entry_from_elf

#### defined symbol has is_defined=true

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# st_info=16 = STB_GLOBAL<<4, st_shndx=1 (nonzero = defined)
val sym = ElfSymbol(st_name: 0, st_info: 16, st_other: 0, st_shndx: 1, st_value: 0x1000, st_size: 8, name: "main")
val entry = sym_entry_from_elf(sym, 0)
expect(entry.is_defined).to_equal(true)
expect(entry.name).to_equal("main")
expect(entry.offset).to_equal(0x1000)
```

</details>

#### undefined symbol has is_defined=false

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# st_shndx=0 = SHN_UNDEF
val sym = ElfSymbol(st_name: 0, st_info: 16, st_other: 0, st_shndx: 0, st_value: 0, st_size: 0, name: "printf")
val entry = sym_entry_from_elf(sym, 0)
expect(entry.is_defined).to_equal(false)
expect(entry.name).to_equal("printf")
```

</details>

### SymResolver - is_strong and is_weak

#### global binding entry is_strong=true, is_weak=false

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sym = ElfSymbol(st_name: 0, st_info: 16, st_other: 0, st_shndx: 1, st_value: 0x1000, st_size: 8, name: "foo")
val entry = sym_entry_from_elf(sym, 0)
expect(is_strong(entry)).to_equal(true)
expect(is_weak(entry)).to_equal(false)
```

</details>

#### weak binding entry is_weak=true, is_strong=false

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# st_info=32 = STB_WEAK<<4
val sym = ElfSymbol(st_name: 0, st_info: 32, st_other: 0, st_shndx: 1, st_value: 0x2000, st_size: 4, name: "weak_fn")
val entry = sym_entry_from_elf(sym, 0)
expect(is_weak(entry)).to_equal(true)
expect(is_strong(entry)).to_equal(false)
```

</details>

### SymResolver - empty resolution

#### sym_resolution_new has 0 defined, 0 undefined, 0 errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = sym_resolution_new()
expect(sym_defined_count(res)).to_equal(0)
expect(sym_undefined_count(res)).to_equal(0)
expect(sym_error_count(res)).to_equal(0)
```

</details>

#### sym_is_resolved on empty resolution returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val res = sym_resolution_new()
expect(sym_is_resolved(res)).to_equal(true)
```

</details>

### SymResolver - single object resolution

#### object with two globals results in both in defined table

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sym_main = ElfSymbol(st_name: 0, st_info: 16, st_other: 0, st_shndx: 1, st_value: 0x1000, st_size: 8, name: "main")
val sym_init = ElfSymbol(st_name: 0, st_info: 16, st_other: 0, st_shndx: 2, st_value: 0x2000, st_size: 4, name: "_init")
val obj = make_obj([sym_main, sym_init])
val res = sym_resolve_objects([obj])
expect(sym_defined_count(res)).to_equal(2)
expect(sym_has_symbol(res, "main")).to_equal(true)
expect(sym_has_symbol(res, "_init")).to_equal(true)
```

</details>

#### sym_get returns correct SymEntry for defined symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sym_main = ElfSymbol(st_name: 0, st_info: 16, st_other: 0, st_shndx: 1, st_value: 0x1000, st_size: 8, name: "main")
val obj = make_obj([sym_main])
val res = sym_resolve_objects([obj])
expect(sym_has_symbol(res, "main")).to_equal(true)
val e = res.defined["main"]
expect(e.name).to_equal("main")
expect(e.offset).to_equal(0x1000)
expect(e.size).to_equal(8)
```

</details>

#### sym_has_symbol returns false for absent symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sym_main = ElfSymbol(st_name: 0, st_info: 16, st_other: 0, st_shndx: 1, st_value: 0x1000, st_size: 8, name: "main")
val obj = make_obj([sym_main])
val res = sym_resolve_objects([obj])
expect(sym_has_symbol(res, "nonexistent")).to_equal(false)
```

</details>

### SymResolver - multi-object resolution

#### object A defines main, object B defines helper — both resolved

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sym_main = ElfSymbol(st_name: 0, st_info: 16, st_other: 0, st_shndx: 1, st_value: 0x1000, st_size: 8, name: "main")
val sym_helper = ElfSymbol(st_name: 0, st_info: 16, st_other: 0, st_shndx: 1, st_value: 0x3000, st_size: 16, name: "helper")
val obj_a = make_obj([sym_main])
val obj_b = make_obj([sym_helper])
val res = sym_resolve_objects([obj_a, obj_b])
expect(sym_defined_count(res)).to_equal(2)
expect(sym_has_symbol(res, "main")).to_equal(true)
expect(sym_has_symbol(res, "helper")).to_equal(true)
expect(sym_is_resolved(res)).to_equal(true)
```

</details>

#### object A defines foo, object B references foo — undefined list is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sym_foo_def = ElfSymbol(st_name: 0, st_info: 16, st_other: 0, st_shndx: 1, st_value: 0x100, st_size: 4, name: "foo")
val sym_foo_ref = ElfSymbol(st_name: 0, st_info: 16, st_other: 0, st_shndx: 0, st_value: 0, st_size: 0, name: "foo")
val obj_a = make_obj([sym_foo_def])
val obj_b = make_obj([sym_foo_ref])
val res = sym_resolve_objects([obj_a, obj_b])
expect(sym_undefined_count(res)).to_equal(0)
expect(sym_is_resolved(res)).to_equal(true)
```

</details>

#### unresolved reference produces non-empty undefined list

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sym_ref = ElfSymbol(st_name: 0, st_info: 16, st_other: 0, st_shndx: 0, st_value: 0, st_size: 0, name: "missing_fn")
val obj = make_obj([sym_ref])
val res = sym_resolve_objects([obj])
expect(sym_undefined_count(res)).to_equal(1)
expect(sym_is_resolved(res)).to_equal(false)
```

</details>

### SymResolver - strong vs weak

#### weak def + strong def of same name — strong wins

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Object A: weak definition of "data"
val sym_weak = ElfSymbol(st_name: 0, st_info: 32, st_other: 0, st_shndx: 1, st_value: 0x100, st_size: 4, name: "data")
# Object B: strong (global) definition of "data"
val sym_strong = ElfSymbol(st_name: 0, st_info: 16, st_other: 0, st_shndx: 1, st_value: 0x200, st_size: 8, name: "data")
val obj_a = make_obj([sym_weak])
val obj_b = make_obj([sym_strong])
val res = sym_resolve_objects([obj_a, obj_b])
expect(sym_error_count(res)).to_equal(0)
expect(sym_has_symbol(res, "data")).to_equal(true)
val e = res.defined["data"]
# Strong definition at 0x200 should win over weak at 0x100
expect(e.offset).to_equal(0x200)
expect(is_strong(e)).to_equal(true)
```

</details>

#### two strong defs of same name — error recorded

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sym_a = ElfSymbol(st_name: 0, st_info: 16, st_other: 0, st_shndx: 1, st_value: 0x100, st_size: 4, name: "conflict")
val sym_b = ElfSymbol(st_name: 0, st_info: 16, st_other: 0, st_shndx: 1, st_value: 0x200, st_size: 4, name: "conflict")
val obj_a = make_obj([sym_a])
val obj_b = make_obj([sym_b])
val res = sym_resolve_objects([obj_a, obj_b])
expect(sym_error_count(res)).to_equal(1)
```

</details>

### SymResolver - local symbols

#### local symbols do not enter the global defined table

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# st_info=0 = STB_LOCAL<<4 | 0
val sym_local = ElfSymbol(st_name: 0, st_info: 0, st_other: 0, st_shndx: 1, st_value: 0x100, st_size: 16, name: "local_helper")
val obj = make_obj([sym_local])
val res = sym_resolve_objects([obj])
expect(sym_has_symbol(res, "local_helper")).to_equal(false)
expect(sym_defined_count(res)).to_equal(0)
```

</details>

#### sym_local_count returns correct count per object

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sym_local1 = ElfSymbol(st_name: 0, st_info: 0, st_other: 0, st_shndx: 1, st_value: 0x100, st_size: 4, name: "lf1")
val sym_local2 = ElfSymbol(st_name: 0, st_info: 0, st_other: 0, st_shndx: 2, st_value: 0x200, st_size: 4, name: "lf2")
val sym_global = ElfSymbol(st_name: 0, st_info: 16, st_other: 0, st_shndx: 1, st_value: 0x300, st_size: 8, name: "gfn")
val obj = make_obj([sym_local1, sym_local2, sym_global])
val res = sym_resolve_objects([obj])
expect(sym_local_count(res, 0)).to_equal(2)
```

</details>

### SymResolver - empty-name symbols

#### symbols with empty name are skipped in the global table

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sym_empty = ElfSymbol(st_name: 0, st_info: 16, st_other: 0, st_shndx: 1, st_value: 0x500, st_size: 4, name: "")
val sym_named = ElfSymbol(st_name: 0, st_info: 16, st_other: 0, st_shndx: 1, st_value: 0x600, st_size: 8, name: "real_fn")
val obj = make_obj([sym_empty, sym_named])
val res = sym_resolve_objects([obj])
expect(sym_defined_count(res)).to_equal(1)
expect(sym_has_symbol(res, "real_fn")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/linker/sym_resolver_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SymResolver - elf_binding_to_sym
- SymResolver - sym_entry_from_elf
- SymResolver - is_strong and is_weak
- SymResolver - empty resolution
- SymResolver - single object resolution
- SymResolver - multi-object resolution
- SymResolver - strong vs weak
- SymResolver - local symbols
- SymResolver - empty-name symbols

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
