# Compiler loader packed-byte evidence gaps

Status: OPEN

This record tracks missing evidence, not a claim that the present implementation
is incorrect. It unblocks only when the named tests land, deliberately fail
against a disabled/broken implementation, and pass once in a fresh session.

| ID | Current code anchor | Missing fixed test | Unblock condition |
|---|---|---|---|
| PBL-01 | `src/compiler_rust/compiler/src/interpreter_extern/sffi_array.rs:101`, `src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs:175`, and the clone/equality owners `src/compiler_rust/compiler/src/value_pointers.rs:236` and `src/compiler_rust/compiler/src/value_pointers.rs:362` | Add `packed_byte_concat_preserves_storage`, `packed_byte_clone_preserves_cow_storage`, and `packed_byte_equality_is_value_based` to `src/compiler_rust/compiler/tests/packed_byte_interpreter_semantics.rs` | `cd src/compiler_rust && cargo test -p simple-compiler --test packed_byte_interpreter_semantics` passes after a retained deliberate-red receipt |
| PBL-02 | `src/compiler_rust/compiler/src/interpreter/place.rs:169` and `src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs:485` | Add `interpreter_byte_array_projected_place_mutators_write_back` to `src/compiler_rust/driver/tests/interpreter_extern.rs` | `cd src/compiler_rust && cargo test -p simple-driver --test interpreter_extern interpreter_byte_array_projected_place_mutators_write_back -- --test-threads=1` passes after a retained deliberate-red receipt |
| PBL-03 | The process-lifetime leaked byte boundary at `src/compiler_rust/compiler/src/interpreter_extern/sffi_array.rs:708` and the raw dynamic fallback at `src/compiler_rust/compiler/src/interpreter_extern/dynamic_sffi.rs:654` | Create `src/compiler_rust/compiler/tests/packed_byte_foreign_capability_lifetime.rs` with `packed_byte_foreign_capability_is_input_only`, `packed_byte_foreign_descriptor_rejects_out_of_bounds`, and `packed_byte_foreign_capability_cannot_escape_call` | `cd src/compiler_rust && cargo test -p simple-compiler --test packed_byte_foreign_capability_lifetime` passes after a retained deliberate-red receipt |

Owner: compiler interpreter/SFFI owner. Final reviewer: highest-capability
reviewer. The Rust seed may exercise these Rust tests but may not substitute for
the separate self-hosted Stage 4 admission and performance gates.

## 2026-08-14 post-sync regression repair

After rebasing onto `7ac900316dd5`, the existing focused semantic test exposed
that the general place route had started intercepting a bare mutable
`ByteArray`. Its empty projection could not be rebuilt by `updated_root`, so
`bytes.push(7u8)` returned the enlarged value while leaving the identifier at
length four. Bare mutable packed bytes now fall through to the identifier/COW
owner; projected places and bare frozen receivers retain the general place
route.

The driver tests named “interpreter” were also using `run_code`, which compiles
and executes SMF through `Runner` and therefore did not exercise the Rust
interpreter owner they claim to cover. Their packed-byte cases now use a focused
direct-interpreter helper that clears module/interpreter state for each source.
Fresh evidence: `packed_byte_interpreter_semantics` passed 1/1 and the four
`interpreter_byte_array_identifier_mutators` cases passed 4/4. PBL-01 remains
open for concat/clone/equality and PBL-02 remains open for projected-place
coverage; this repair does not promote either row.
