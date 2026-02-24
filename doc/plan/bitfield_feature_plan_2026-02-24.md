# Bitfield Feature Plan (BM-004)

## Status
- Phase 1 is implemented in `compiler.core` parser/token pipeline.
- `bitfield` is recognized as a keyword and lowered through parser declarations.
- Parser-side validation now enforces backing type (`u8/u16/u32/u64`), field type (`bool/uN/iN`), duplicate names, and width overflow.
- Native C codegen path has executable regression coverage in `test/unit/compiler/native/bitfield_codegen_spec.spl`.
- Pure-Simple parser/token implementation is locked by `test/unit/compiler/parser/bitfield_pure_simple_spec.spl`.
- Runtime compatibility coverage is locked by `test/feature/usage/bitfield_runtime_compat_spec.spl`.

## Goal
Deliver end-to-end bitfield support for low-level and bare-metal workflows with predictable layout and safe semantic checks.

## Scope
- Syntax: `bitfield Name(u8|u16|u32|u64): ...`
- Fields: `bool`, `uN`, `iN`, and reserved `_` segments
- Placement: module-level declarations

## Non-Goals (Current Cycle)
- Bitfield declarations nested inside function bodies
- Dynamic-width fields
- Platform-specific packed ABI overrides

## Phases
1. Phase 1: Parser + AST lowering
- Parse module-level bitfield declarations.
- Lower into a dedicated AST/HIR node (not generic struct fallback).
- Preserve field order and explicit widths.

2. Phase 2: Semantic validation
- Enforce storage width exact match.
- Enforce field-name uniqueness except `_`.
- Validate signed/unsigned width bounds.
- Produce deterministic, human-readable diagnostics.

3. Phase 3: MIR lowering + layout mapping
- Compute bit offset/width map.
- Lower loads/stores to mask/shift MIR patterns.
- Ensure reserved fields are non-addressable.

4. Phase 4: Backend + runtime tests
- C/native backend emission for bit extraction/insertion.
- Add conformance tests for u8/u16/u32/u64 layouts.
- Add negative tests for width overflow and duplicate names.

## Exit Criteria
- `test/feature/usage/bitfield_spec.spl` plan-contract remains green.
- `test/unit/compiler/native/bitfield_codegen_spec.spl` validates real `bitfield` syntax against `build/simple_codegen`.
- `test/unit/compiler/parser/bitfield_pure_simple_spec.spl` validates pure-Simple token/parser wiring.
- `test/feature/usage/bitfield_runtime_compat_spec.spl` validates real feature-path runtime acceptance.
- Parser/semantic/MIR/backend tests cover happy/invalid paths.
- At least one end-to-end bare-metal style sample passes.
