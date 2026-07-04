# Unsafe Blocks Specification

> Unsafe blocks allow operations that bypass safety checks:

<!-- sdn-diagram:id=unsafe_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=unsafe_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

unsafe_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=unsafe_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unsafe Blocks Specification

Unsafe blocks allow operations that bypass safety checks:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BM-006 |
| Category | Language / Bare-Metal |
| Status | In Progress (unsafe syntax not supported by runtime parser) |
| Source | `test/03_system/feature/features/baremetal/unsafe_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Unsafe blocks allow operations that bypass safety checks:
- Raw pointer dereference
- Inline assembly
- FFI function calls
- Mutable static access
- Type transmutation

## Scenarios

### Unsafe Blocks

#### Basic Unsafe Block

#### allows operations inside modeled unsafe frame

1. check depth


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = UnsafeFrame.create("basic").enter()
check_depth(frame, 1)
```

</details>

#### keeps safe code outside the modeled frame

1. check depth


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = UnsafeFrame.create("basic")
check_depth(frame, 0)
```

</details>

#### Nested Unsafe

#### tracks nested unsafe frames

1. check depth


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = UnsafeFrame.create("nested").enter().enter()
check_depth(frame, 2)
```

</details>

#### exits nested unsafe frames in order

1. check depth


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = UnsafeFrame.create("nested").enter().enter().exit()
check_depth(frame, 1)
```

</details>

#### Unsafe Functions

#### models an unsafe function signature

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binding = FfiBinding.create("poke", 1, false)
expect(binding.name).to_equal("poke")
expect(binding.arity).to_equal(1)
```

</details>

#### models a safe wrapper over unsafe work

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binding = FfiBinding.create("poke_safe", 1, true)
expect(binding.is_safe_wrapper).to_equal(true)
```

</details>

### Raw Pointer Operations

#### Pointer Creation

#### casts integer to pointer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ptr = RawPointer.from_int(4096)
expect(ptr.address).to_equal(4096)
```

</details>

#### casts reference to pointer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = RawPointer.from_int(100)
val ptr = base.offset(0)
expect(ptr.address).to_equal(100)
```

</details>

#### Pointer Dereference

#### reads through pointer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ptr = RawPointer.from_int(64)
expect(ptr.address).to_equal(64)
```

</details>

#### writes through pointer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ptr = RawPointer.from_int(64).offset(4)
expect(ptr.address).to_equal(68)
```

</details>

#### Pointer Arithmetic

#### offsets pointer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ptr = RawPointer.from_int(10).offset(6)
expect(ptr.address).to_equal(16)
```

</details>

#### calculates pointer difference

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = RawPointer.from_int(32)
val b = RawPointer.from_int(12)
expect(a.diff(b)).to_equal(20)
```

</details>

### Inline Assembly

#### Basic Assembly

#### allows assembly in modeled unsafe block

1. check depth


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = UnsafeFrame.create("asm").enter()
check_depth(frame, 1)
```

</details>

#### allows assembly with inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val input = 7
expect(input + 1).to_equal(8)
```

</details>

#### allows assembly with outputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = 3 * 3
expect(output).to_equal(9)
```

</details>

### FFI Calls

#### Extern Functions

#### declares modeled extern function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binding = FfiBinding.create("extern_open", 2, false)
expect(binding.name).to_equal("extern_open")
```

</details>

#### requires wrapper to call modeled extern fn

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binding = FfiBinding.create("extern_open_safe", 2, true)
expect(binding.is_safe_wrapper).to_equal(true)
```

</details>

#### Safe Wrappers

#### creates safe wrapper

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binding = FfiBinding.create("safe_open", 2, true)
expect(binding.is_safe_wrapper).to_equal(true)
```

</details>

### Mutable Statics

#### Static Mut Access

#### requires modeled unsafe state to access static mut

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cell = StaticMutCell.create(1)
expect(cell.read()).to_equal(1)
```

</details>

#### documents data race risk with writes

1. cell write
2. cell write
   - Expected: cell.writes equals `2`
   - Expected: cell.read() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cell = StaticMutCell.create(1)
cell.write(2)
cell.write(3)
expect(cell.writes).to_equal(2)
expect(cell.read()).to_equal(3)
```

</details>

### Type Transmutation

#### transmute Function

#### transmutes between same-size types

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val record = BitCastRecord.create(0x3f800000, 1065353216)
expect(record.from_bits).to_equal(record.to_bits)
```

</details>

#### validates size equality

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val same = BitCastRecord.create(8, 8)
expect(same.from_bits).to_equal(same.to_bits)
```

</details>

### Use Cases

#### Memory-Mapped I/O

#### accesses MMIO register

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reg = RawPointer.from_int(0xFF00)
expect(reg.address).to_equal(0xFF00)
```

</details>

#### Zero-Copy Buffer

#### casts buffer to struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buffer = RawPointer.from_int(128)
expect(buffer.offset(0).address).to_equal(128)
```

</details>

#### Custom Allocator

#### implements custom allocator

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arena = RawPointer.from_int(256).offset(16)
expect(arena.address).to_equal(272)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
