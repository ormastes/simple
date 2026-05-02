# Custom Primitive SFFI and Public API Plan

Date: 2026-04-20

## Goal

Make custom primitive wrappers usable anywhere a raw ABI primitive is currently required, then migrate SimpleOS, HAL, and SFFI public interfaces where the migration is ABI-safe and semantically useful.

## Phase 1: Custom Primitive Metadata

- Record `newtype Name = Base` as a custom primitive/transparent wrapper, not only as a single-field struct.
- Preserve underlying type, signedness, bit width, size, alignment, and source span.
- Expose queries such as `is_custom_primitive`, `underlying_primitive`, `bit_capacity`, and `abi_type`.

Primary files:

- `src/compiler/10.frontend/core/parser_decls.spl`
- `src/compiler/20.hir/hir_types.spl`
- `src/compiler/20.hir/hir_definitions.spl`
- `src/compiler/30.types/type_layout.spl`

## Phase 2: SFFI Custom Primitive ABI

- Accept transparent custom primitives in SFFI001.
- Require transparent or newtype layout for named primitive wrappers in SFFI.
- Map custom primitives to their underlying C/Rust/LLVM ABI type in generated bindings.
- Add tests proving wrappers are passed by value, not as object handles.

Primary files:

- `src/compiler/35.semantics/lint/sffi_lint.spl`
- `src/compiler/90.tools/ffi_gen/type_mapping.spl`
- `src/compiler/70.backend/backend/c_type_mapper.spl`
- `src/compiler/70.backend/backend/llvm_type_mapper.spl`
- `test/unit/compiler/semantics/sffi_lint_spec.spl`
- `test/integration/sffi/*`

## Phase 3: SFFI and Language Bitfields

- Replace duplicated textual width tables with the shared custom primitive resolver.
- Allow custom primitive integer wrappers as bitfield backing types when their underlying type is `u8`, `u16`, `u32`, or `u64`.
- Allow custom primitive integer/bool wrappers as bitfield field types and `@bits` fields.
- Keep clear errors for non-integer wrappers, floats, text, and platform-dependent types.

Primary files:

- `src/compiler/10.frontend/core/parser_decls.spl`
- `src/compiler/20.hir/hir_lowering/items.spl`
- `src/compiler/70.backend/bitfield.spl`
- `src/compiler/50.mir/mir_bitfield.spl`
- `src/compiler/35.semantics/lint/sffi_lint.spl`
- `test/unit/compiler/parser/bitfield_pure_simple_spec.spl`
- `test/unit/compiler/native/bitfield_codegen_spec.spl`
- `test/integration/sffi/layout_verification_roundtrip_spec.spl`

## Phase 4: Public Primitive Audit

- Extend primitive API lint/fix tooling to classify each primitive as:
  - convertible
  - blocked by ABI/layout
  - intentionally primitive
  - pure math/bootstrap/test exemption
- Generate an audit report for `src/os`, `src/lib`, SFFI, and HAL-facing modules.
- Define domain wrappers for handles, IDs, sizes, offsets, addresses, IRQ vectors, file modes, deadlines, and errno-like values.

Primary files:

- `src/compiler/35.semantics/lint/primitive_api.spl`
- `src/compiler/90.tools/fix/rules/impl/lint_primitive_api.spl`
- `src/os/**`
- `src/lib/**`

## Phase 5: Staged API Migration

- Migrate SFFI-facing public functions and structs first after ABI tests pass.
- Migrate SimpleOS/SOSIX/POSIX wrappers and HAL APIs by domain wrapper groups.
- Keep raw primitives in exact C externs and on-disk/wire structs unless wrapped with explicit transparent layout and proven by tests.
- Add compatibility wrappers where public names would otherwise break.

## Phase 6: Verification

Run focused tests first:

- New custom primitive parser/layout tests.
- SFFI lint and FFI mapping tests.
- Bitfield parser/HIR/MIR/codegen tests.
- Primitive API audit tests.
- OS/HAL wrapper tests for migrated APIs.

Final gate:

- Core runtime smoke for affected runtime.
- MCP native smoke if compiler or `src/lib` language surface changed.
- Existing SFFI integration tests.
- Public API audit report with no unexplained raw primitive public APIs.
