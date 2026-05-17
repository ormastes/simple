# SStack State: custom-primitive-sffi-public-api

## User Request
> next task from the plan — custom_primitive_sffi_public_api (6 phases: metadata, SFFI ABI, bitfields, audit, migration, verification)

## Task Type
feature

## Refined Goal
> Implement custom primitive wrapper infrastructure: newtype metadata queries, SFFI transparent ABI mapping, bitfield backing/field support, primitive API lint classification, domain wrappers, staged API migration scaffolding, and verification specs.

## Acceptance Criteria
- [ ] AC-1: Custom primitive metadata — CustomPrimitiveInfo with is_custom_primitive, underlying_primitive, bit_capacity, abi_type queries
- [ ] AC-2: Custom primitive type layout — signedness, bit width, size, alignment, source span preservation
- [ ] AC-3: SFFI custom primitive ABI — transparent wrappers accepted in SFFI, mapped to underlying C/Rust/LLVM ABI type
- [ ] AC-4: SFFI pass-by-value verification — custom primitives passed by value not as object handles
- [ ] AC-5: Bitfield backing types — custom primitive integer wrappers as bitfield backing types (u8/u16/u32/u64)
- [ ] AC-6: Bitfield field types — custom primitive integer/bool wrappers as @bits fields with error on non-integer
- [ ] AC-7: Primitive API lint — classify each primitive as convertible/blocked/intentional/exempt
- [ ] AC-8: Domain wrapper definitions — handles, IDs, sizes, offsets, addresses, IRQ vectors, file modes, deadlines, errno
- [ ] AC-9: SFFI migration scaffolding — migration helper for SFFI-facing functions/structs with compatibility wrappers
- [ ] AC-10: Verification spec — 20 tests covering metadata, ABI, bitfields, lint, domain wrappers

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-17
- [x] 2-4 — skipped (plan doc comprehensive)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
10 ACs across 6 plan phases. 5 parallel agents (A-E). Existing: parser_decls.spl, hir_types.spl, type_layout.spl, sffi_lint.spl, bitfield.spl, primitive_api.spl, c_type_mapper.spl, llvm_type_mapper.spl, ffi_gen/type_mapping.spl.

### 5-implement
<pending>
