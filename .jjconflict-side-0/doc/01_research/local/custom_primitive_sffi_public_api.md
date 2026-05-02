# Custom Primitive SFFI and Public API Research

Date: 2026-04-20

## Scope

Research custom primitive applicability for SFFI, SFFI bitfields, and public primitive APIs across SimpleOS, HAL, SFFI, and adjacent system interfaces.

## Current Model

Simple has user-facing wrapper facilities, but the compiler does not yet carry a durable "custom primitive" concept through all ABI-sensitive phases.

- `src/compiler/10.frontend/core/parser_decls.spl` parses `newtype Name = Base` as a single-field struct named `Name` with field `value`.
- `src/compiler/20.hir/hir_types.spl` represents named types as `HirTypeKind.Named(symbol, args)`, with no distinct `CustomPrimitive` or `TransparentPrimitive` type kind.
- `src/compiler/30.types/type_layout.spl` supports `LayoutKind.Transparent`, but general size/alignment fallback for unresolved named types is still pointer-like/default-sized.
- Existing docs describe newtypes as zero-overhead wrappers, but the compiler pipeline currently treats them mostly as single-field structs.

## SFFI Findings

SFFI currently accepts raw primitives directly and rejects most named wrappers before layout can prove they are transparent.

Relevant files:

- `src/compiler/35.semantics/lint/sffi_lint.spl`
- `src/compiler/90.tools/ffi_gen/type_mapping.spl`
- `src/compiler/70.backend/backend/c_type_mapper.spl`
- `src/compiler/70.backend/backend/llvm_type_mapper.spl`

Blockers:

1. `sffi_lint._is_c_compatible_primitive` accepts `Int`, `Float`, `Bool`, `Char`, `Unit`, and pointers only. `Named` custom primitive wrappers are rejected by SFFI001.
2. `check_sffi003_repr_required` recognizes `LayoutKind.Transparent`, but SFFI001 can reject a named wrapper before transparent layout is useful.
3. `ffi_gen/type_mapping.spl` maps unknown named types as object handles, so a custom primitive wrapper can become `*mut Type` instead of its underlying ABI type.
4. Backend type mappers map MIR structs/named objects as pointer-like C/LLVM types unless registered as regular structs. They do not unwrap transparent primitive wrappers by value.

Conclusion: SFFI cannot safely migrate from raw primitives to custom primitives until the compiler can resolve `Named` wrapper -> transparent primitive ABI in lint, FFI generation, and backend type mapping.

## Bitfield Findings

SFFI bitfields and language bitfields only recognize raw primitive width names.

Relevant files:

- `src/compiler/10.frontend/core/parser_decls.spl`
- `src/compiler/20.hir/hir_lowering/items.spl`
- `src/compiler/70.backend/bitfield.spl`
- `src/compiler/50.mir/mir_bitfield.spl`
- `src/compiler/35.semantics/lint/sffi_lint.spl`

Blockers:

1. `bitfield_backing_bits_from_name` only accepts `u8`, `u16`, `u32`, `u64`.
2. `bitfield_field_bits_from_name` only accepts `bool`, `uN`, and `iN` textual names.
3. HIR lowering `infer_bit_width` hard-codes primitive names and returns `0` for unknown named types.
4. Backend `type_bit_width` and `backing_type_bits` inspect `HirType.to_text()` and do not resolve transparent underlying primitive width.
5. SFFI `_bit_capacity` returns capacity only for `Int` and `Bool`, so a named transparent integer wrapper cannot be used with `@bits`.

Conclusion: custom primitive bitfields require a shared width resolver. Duplicated textual width tables must be replaced or wrapped by a central `underlying_integer_bits` query.

## Public Primitive API Findings

The `primitive_api` lint and fix path detects raw primitive signatures, but it does not classify whether an occurrence is safe to migrate.

Relevant files:

- `src/compiler/35.semantics/lint/primitive_api.spl`
- `src/compiler/90.tools/fix/rules/impl/lint_primitive_api.spl`
- `test/integration/app/primitive_api_lint_spec.spl`

Observed hotspots from `src/os`, `src/lib`, compiler SFFI, and HAL-facing code:

- File descriptors, process IDs, handles, queue IDs, dataset IDs.
- Sizes, byte counts, offsets, timestamps, deadlines, durations.
- Physical/virtual addresses, IRQ vectors, register addresses, MMIO values.
- FAT32 and WinVFS on-disk / host-handle fields.
- SFFI extern declarations and generated ABI wrapper functions.

Likely good custom primitive candidates:

- `Fd`, `Pid`, `HandleId`, `Bytes`, `ByteOffset`, `FileMode`, `IrqVector`, `PhysAddr`, `VirtAddr`, `RegisterAddr`, `DeviceId`, `QueueId`, `DatasetId`, `EpochNs`, `DeadlineNs`, `Errno`.

Likely primitive exemptions:

- Pure math helpers.
- Byte buffers and byte slices.
- Exact C extern declarations until SFFI custom primitive ABI lowering is proven.
- On-disk and wire layout structs where the field must remain visibly primitive or use an explicitly transparent wrapper.
- Bootstrap compiler/core paths that operate on raw primitive type tags.
- Test fixtures and parser/token internals where primitives are the subject under test.

## Key Risk

Migrating public APIs before SFFI and backend ABI mapping understand custom primitives would improve source-level semantics but can silently change C signatures, bitfield packing, or generated handles. The implementation must make custom primitive ABI transparent first, then migrate OS/HAL/SFFI APIs.

## Research Conclusion

Use a compiler-wide custom primitive resolver:

1. Record newtype/custom primitive metadata at parse/HIR lowering time.
2. Resolve named transparent wrappers to underlying primitive type, size, align, signedness, and bit capacity.
3. Make SFFI lint, FFI generator, C/LLVM type mapping, and bitfield codegen call this resolver.
4. Only then migrate SimpleOS/HAL/SFFI public APIs from raw primitives to domain-specific custom primitives.
