# Custom Primitive Sffi Specification

> <details>

<!-- sdn-diagram:id=custom_primitive_sffi_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=custom_primitive_sffi_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

custom_primitive_sffi_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=custom_primitive_sffi_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Custom Primitive Sffi Specification

## Scenarios

### Custom primitive SFFI metadata

#### maps u32 wrapper metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = PrimInfo.create("MyU32", "u32")
expect(p.signedness).to_equal("unsigned")
expect(p.bit_width).to_equal(32)
expect(p.byte_size).to_equal(4)
```

</details>

#### maps i64 wrapper metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = PrimInfo.create("MyI64", "i64")
expect(p.signedness).to_equal("signed")
expect(p.bit_width).to_equal(64)
```

</details>

#### maps bool wrapper as non-integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = PrimInfo.create("MyBool", "bool")
expect(p.bit_width).to_equal(8)
expect(p.is_integer()).to_equal(false)
```

</details>

#### marks wrapper as custom primitive

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = PrimInfo.create("Anything", "u32")
expect(p.is_custom()).to_equal(true)
```

</details>

#### returns underlying ABI type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = PrimInfo.create("Handle", "u64")
expect(p.abi_type()).to_equal("u64")
```

</details>

### Custom primitive SFFI ABI mapping

#### maps u32 to C ABI type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = AbiMap(dummy: 0)
expect(m.map_c("u32")).to_equal("uint32_t")
```

</details>

#### maps i64 to Rust ABI type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = AbiMap(dummy: 0)
expect(m.map_rust("i64")).to_equal("i64")
```

</details>

#### maps f64 to LLVM ABI type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = AbiMap(dummy: 0)
expect(m.map_llvm("f64")).to_equal("double")
```

</details>

### Custom primitive bitfield validation

#### accepts u32 backing

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(BitfieldCheck.check_backing("u32")).to_equal(true)
```

</details>

#### accepts u8 backing

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(BitfieldCheck.check_backing("u8")).to_equal(true)
```

</details>

#### rejects f32 backing

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(BitfieldCheck.check_backing("f32")).to_equal(false)
```

</details>

#### rejects bool backing

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(BitfieldCheck.check_backing("bool")).to_equal(false)
```

</details>

#### accepts bounded integer field

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(BitfieldCheck.check_field("u16", 4, 16)).to_equal(true)
```

</details>

#### rejects field overflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(BitfieldCheck.check_field("u8", 12, 8)).to_equal(false)
```

</details>

#### rejects float field

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(BitfieldCheck.check_field("f32", 8, 32)).to_equal(false)
```

</details>

#### accepts one-bit bool field

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(BitfieldCheck.check_field("bool", 1, 32)).to_equal(true)
```

</details>

### Custom primitive classification and domain wrappers

#### migrates convertible primitives

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = PrimClass(classification: "convertible")
expect(c.should_migrate()).to_equal(true)
```

</details>

#### does not migrate blocked primitives

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = PrimClass(classification: "blocked")
expect(c.should_migrate()).to_equal(false)
```

</details>

#### models file handle wrapper

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = PrimInfo.create("FileHandle", "u32")
expect(p.underlying).to_equal("u32")
```

</details>

#### models IRQ vector wrapper

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = PrimInfo.create("IrqVector", "u16")
expect(p.underlying).to_equal("u16")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/custom_primitive_sffi_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Custom primitive SFFI metadata
- Custom primitive SFFI ABI mapping
- Custom primitive bitfield validation
- Custom primitive classification and domain wrappers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
