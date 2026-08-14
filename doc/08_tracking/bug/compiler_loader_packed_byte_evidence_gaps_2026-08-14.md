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
