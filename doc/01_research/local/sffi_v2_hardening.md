<!-- codex-research -->
# Local Research: SFFI v2 Hardening

**Date:** 2026-08-21

**Baseline:** `2624da57f05e7ad1865b56493bbcb3a04e2b0dd3`
**Canonical synthesis:** `doc/01_research/platform/sffi_v2_hardening_2026-08-21.md`

This companion indexes the repository evidence behind the supplied assessment.
It does not replace or overwrite the combined research.

## Confirmed implementation seams

- `src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs`
  turns an execution with no value into `Value::Nil`.
- `src/compiler_rust/compiler/src/interpreter_call/core/macros.rs` contains the
  unit-only return guard; it is not total declared-return validation.
- `src/compiler_rust/compiler/src/interpreter_extern/dynamic_sffi.rs` owns the
  generic integer-shaped dynamic call path.
- `src/compiler_rust/compiler/src/interpreter_extern/mod.rs` and
  `signatures.rs` own seed extern dispatch and signature routing.
- `src/compiler/35.semantics/lint/sffi_lint.spl` and
  `src/compiler/90.tools/sffi_gen/` are existing self-hosted policy/generation
  seams, but are not one authoritative resolved ABI registry.
- `src/compiler/70.backend/sffi.spl`, native linker owners, and SimpleOS loader
  owners must agree with the interpreter rather than synthesize providers.
- `src/compiler/00.common/assurance/unsafe_capabilities.spl` contains the
  canonical `ffi` capability vocabulary; bug records show parsing/HIR carriage
  is not yet a complete lexical boundary.

## Reproduce-first evidence

| Defect | Existing evidence |
|---|---|
| Declared return mismatch/fallthrough | `test/01_unit/compiler/types/declared_return_type_enforced_spec.spl` |
| Missing extern fabricated by native link | `test/01_unit/compiler/linker/extern_unimplemented_weak_stub_fabrication_spec.spl` and its four fixture families |
| Plain `[u8]` versus `Option<[u8]>` transport | `test/01_unit/compiler/sffi_byte_array_return_not_option_spec.spl` |
| Cross-engine `[u8]` defect class | `test/01_unit/compiler/sffi_byte_array_return_class_spec.spl` |
| Unsafe capability vocabulary | `test/unit/compiler/common/assurance/unsafe_capabilities_spec.spl` |
| Resource ownership surface | `test/01_unit/compiler/resource/resource_sffi_pilot_spec.spl` |

Adjacent coverage includes backend null/layout/signature specs, hosted extern
mode agreement, SFFI lint/driver shim specs, and the C/C++/import/layout/callback
integration specs under `test/02_integration/sffi/`.

## Bug-record authority

P0 is directly supported by `declared_return_type_not_enforced_2026-08-09.md`,
`unregistered_extern_silent_nil_2026-08-01.md`,
`extern_unimplemented_links_weak_stub_fabricated_value_2026-08-18.md`,
`native_build_fabricates_weak_stub_for_unimplemented_extern_2026-08-18.md`,
`native_link_fabricates_weak_empty_extern_definitions_2026-08-01.md`, and
`sffi_u8_return_nil_and_cross_engine_len_2026-08-18.md` in
`doc/08_tracking/bug/`.

P1/P2/P4 are supported by the resource declaration, unsafe capability, and
artifact trust-anchor bug records named in the combined research. Those
records remain authoritative until implementation and verification close them.

## Local conclusion

P0 must repair each execution/link lane as one defect class. P1 must establish
one compiler-owned typed contract and generated lift path. A grep inventory,
per-lane registry, wrapper convention, or signature field alone cannot prove
the boundary.
