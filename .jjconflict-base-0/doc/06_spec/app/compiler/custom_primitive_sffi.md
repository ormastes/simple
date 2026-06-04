# Custom Primitive SFFI

Custom primitives are newtypes over Simple's built-in primitives (`u8`..`u64`, `i8`..`i64`, `bool`, `f32`, `f64`). At the SFFI boundary they are passed **by value** using the underlying primitive's ABI — no boxing, no object handles.

## Metadata

`CustomPrimitiveInfo` stores the resolved layout for a wrapper type.

| Field | Type | Description |
|-------|------|-------------|
| `name` | `text` | Wrapper type name (e.g. `FileHandle`) |
| `underlying` | `text` | Backing primitive (`i32`, `u64`, ...) |
| `domain` | `text` | Semantic domain (`handle`, `id`, `size`, ...) |
| `signedness` | `text` | `"signed"`, `"unsigned"`, or `"none"` |
| `bit_width` | `i32` | 8, 16, 32, or 64 |
| `byte_size` | `i32` | Derived from bit_width |
| `is_integer` | `bool` | Integer family check |
| `is_float` | `bool` | Float family check |
| `is_bool` | `bool` | Bool check |

### Registry

`CustomPrimitiveRegistry` holds up to 16 registered custom primitives. Use `register(info) -> bool` and `lookup(name) -> CustomPrimitiveInfo`.

## ABI Mapping

`PrimitiveAbiNames` maps Simple primitives to their canonical ABI names:

| Simple | C | Rust | LLVM IR |
|--------|---|------|---------|
| `u8` | `uint8_t` | `u8` | `i8` |
| `u16` | `uint16_t` | `u16` | `i16` |
| `u32` | `uint32_t` | `u32` | `i32` |
| `u64` | `uint64_t` | `u64` | `i64` |
| `i8` | `int8_t` | `i8` | `i8` |
| `i16` | `int16_t` | `i16` | `i16` |
| `i32` | `int32_t` | `i32` | `i32` |
| `i64` | `int64_t` | `i64` | `i64` |
| `bool` | `bool` | `bool` | `i1` |
| `f32` | `float` | `f32` | `float` |
| `f64` | `double` | `f64` | `double` |

### SFFI Transparency Check

`SffiPrimitiveCheck` validates that a custom primitive is safe to pass across the FFI boundary:

- **transparent**: the wrapper adds no runtime overhead
- **value_type**: passed by value, not by object handle

Create via `sffi_primitive_check_from_info(name, underlying)` for defaults (both true) or `sffi_primitive_check_create(name, underlying, transparent, value_type)` for explicit control.

### ABI Mapper Functions

```
sffi_abi_map_to_c("u32")    // -> "uint32_t"
sffi_abi_map_to_rust("i64")  // -> "i64"
sffi_abi_map_to_llvm("f64")  // -> "double"
sffi_abi_map_all("u32")      // -> "c=uint32_t rust=u32 llvm=i32"
```

## Bitfield Support

Custom primitives backed by unsigned integers (`u8`, `u16`, `u32`, `u64`) can serve as bitfield backing types.

### Backing Validation

`BitfieldBackingCheck.check(name, underlying)` validates the backing type. Only `u8`/`u16`/`u32`/`u64` are accepted. `max_bits()` returns the bit capacity.

### Field Validation

`BitfieldFieldCheck.check(name, field_name, field_type, bits)` validates individual fields:
- Field type must be an integer or bool
- Bool fields use exactly 1 bit
- Bit count must not exceed the field type's width

### Layout

`BitfieldLayout.create(name, total_bits)` tracks field packing:

```
var layout = BitfieldLayout.create("StatusReg", 32)
layout.add_field("ready", 1)     // -> true, 31 remaining
layout.add_field("error", 1)     // -> true, 30 remaining
layout.add_field("count", 8)     // -> true, 22 remaining
layout.add_field("reserved", 22) // -> true, 0 remaining
layout.add_field("extra", 1)     // -> false, overflow
```

## Lint Classification

`PrimitiveClassification` categorizes each use of a raw primitive at an SFFI boundary:

| Category | `should_migrate()` | Use case |
|----------|-------------------|----------|
| `convertible` | true | Safe to wrap in a domain type |
| `blocked` | false | Depends on external ABI (cannot change) |
| `intentional` | false | Raw primitive by design (array index, math) |
| `exempt` | false | Legacy code, deferred migration |

### Domain Wrappers

`DomainWrapperCatalog` provides 12 predefined wrapper types for common OS/HAL patterns:

| Wrapper | Underlying | Domain |
|---------|-----------|--------|
| `FileHandle` | `i32` | `handle` |
| `ProcessId` | `i32` | `id` |
| `ThreadId` | `u64` | `id` |
| `IrqVector` | `u8` | `irq` |
| `PhysAddr` | `u64` | `address` |
| `VirtAddr` | `u64` | `address` |
| `MemSize` | `u64` | `size` |
| `MemOffset` | `i64` | `offset` |
| `FileMode` | `u32` | `mode` |
| `DeadlineMs` | `u64` | `deadline` |
| `ErrnoCode` | `i32` | `errno` |
| `PortNum` | `u16` | `port` |

### Audit Report

`PrimitiveAuditReport` accumulates classifications and reports migration readiness:
- **ready**: >80% convertible
- **partial**: 50-80% convertible
- **blocked**: <50% convertible

## Migration

`SffiMigrationHelper` tracks per-function migration status (`pending`, `blocked`, `migrated`). `SffiMigrationRegistry` holds up to 16 entries and generates summary reports via `sffi_registry_report(registry)`.

## Implementation Files

| File | Layer | Purpose |
|------|-------|---------|
| `src/compiler/30.types/custom_primitive_info.spl` | Types | Metadata, resolver, registry |
| `src/compiler/35.semantics/lint/sffi_custom_primitive.spl` | Lint | Transparency check, ABI mapper, migration |
| `src/compiler/50.mir/custom_primitive_bitfield.spl` | MIR | Bitfield validation and layout |
| `src/compiler/35.semantics/lint/primitive_classification.spl` | Lint | Classification, domain wrappers, audit |
| `src/compiler/90.tools/sffi_gen/type_mapping.spl` | Tools | `simple_to_rust`, `simple_to_c_abi` mappers |

## Tests

20 unit tests in `test/01_unit/compiler/custom_primitive_sffi_spec.spl` covering metadata, ABI mapping, bitfield backing/fields, and classification/domain wrappers.
