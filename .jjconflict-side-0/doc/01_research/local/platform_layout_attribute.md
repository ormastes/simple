# Platform Layout Attribute Local Research

Date: 2026-04-20

## Request

Add `@platform` for structs/classes/custom primitive types whose size, field offsets, or ABI representation can vary by CPU, OS, ABI, or pointer width. Emit diagnostics when layout can vary but is not tagged, and warn when the platform-dependent size is not explicit.

## Existing Local Infrastructure

- `src/compiler/common/attributes.spl` already parses layout attributes such as `@repr("C")`, `@repr("packed")`, and `@repr("transparent")`.
- `src/compiler/30.types/type_layout.spl` already computes target-aware primitive size and alignment using `TargetArch`.
- `src/lib/common/target.spl` defines `TargetArch`, `Endian`, and `PointerSize`, including architecture bit and pointer-byte logic.
- `src/compiler/linker/smf_enums.spl` defines SMF `Platform` and `Arch` enums.
- `src/compiler/80.driver/smf_binary_helpers.spl` maps text OS/arch names to SMF enums.
- Prior docs already prefer limiting conditional compilation to platform/FFI boundaries: `doc/01_research/domain/missing_language_features_2026-02-17.md`.

## Local Gap

Simple has target-aware layout computation, but there is no source-level marker for "this public layout intentionally varies by platform." That makes it hard to distinguish:

- accidental ABI drift,
- expected pointer-width-dependent fields,
- OS ABI variants,
- raw C layout imports that differ by target.

## Recommended Local Model

Add a typed platform-layout layer:

- `PlatformCpu`: backed by or mapped from `TargetArch`.
- `PlatformOs`: backed by or mapped from SMF `Platform`.
- `PlatformAbi`: new enum for `Any`, `C`, `Gnu`, `Musl`, `Msvc`, `Eabi`, `Eabihf`, `SimpleOs`, `None_`.
- `PlatformBit`: `Bits8`, `Bits16`, `Bits32`, `Bits64`, `Bits128`, `Pointer`.
- `PlatformEndian`: reuse `Endian`.

Do not use free-form strings in long-term HIR/MIR. Parser syntax may accept strings, but semantic lowering should normalize to enums and reject unknown values.

## Syntax Direction

Recommended forms:

```simple
@platform(bit)
newtype CLong = i64

@platform(default, bit=64)
@platform(os=windows, abi=msvc, bit=32)
struct CStat:
    ...

@platform(cpu=x86_64, os=linux, abi=gnu, bit=64)
class EpollEvent:
    ...
```

Meaning:

- `@platform(bit)` is shorthand for pointer-width-dependent size: `bit=ptr`.
- `@platform(default, bit=64)` is the fallback variant.
- `cpu`, `os`, `abi`, `bit`, and `endian` are enum-valued dimensions after semantic lowering.
- `bit=N` describes the layout-driving width for a platform-sensitive primitive/wrapper.

## Matching Rule

Use specificity selection, not first-match or last-match.

1. Filter variants whose predicates match the target.
2. Prefer the variant with the most constrained dimensions.
3. Error if two matching variants have equal specificity and different layout effects.
4. Use at most one `default` variant.
5. Error on duplicate exact predicates except repeated identical `default` is also an error.

Rationale: layout attributes should not depend on source ordering. Rust/Go-style target predicates are boolean constraints, and Rust's `cfg_select!` has an explicit fallback arm, but ABI layout selection should avoid order-dependent shadowing.

## Diagnostics

Errors:

- A public `@repr("C")`, `@export("C")`, SFFI, HAL, or OS ABI struct/class has platform-varying field size or offset without `@platform`.
- A field is platform-varying but neither the field nor enclosing type has `@platform`.
- Multiple platform variants match with equal specificity and different layout.
- Duplicate non-default match predicates.
- Unknown `cpu`, `os`, `abi`, `bit`, or `endian` value.

Warnings:

- `@platform` is present on a layout-affecting declaration but no explicit `bit`, `size`, or `align` is provided.
- A private/internal type appears platform-varying but is not part of an ABI boundary.
- A broad default exists but no target-specific variant covers the current compilation target.

## Implementation Surfaces

- Attribute parser: `src/compiler/common/attributes.spl`.
- Attribute/HIR model: `src/compiler/20.hir/hir_definitions.spl`, `src/compiler/20.hir/hir_types.spl`.
- Layout resolver: `src/compiler/30.types/type_layout.spl`.
- SFFI lint: `src/compiler/35.semantics/lint/sffi_lint.spl`.
- Backend/header/layout verification: `src/compiler/70.backend/**`, SFFI integration tests.

## Current Worktree Note

There is in-progress custom primitive work in compiler files. `@platform` should be designed to compose with that resolver, because custom primitive wrappers are one of the main places where platform-dependent size needs to be explicit.
