# Rust seed enum runtime type identity

Status: open; bootstrap-only follow-up after the Pure implementation.

Rust bytecode, LLVM, and Cranelift constructor paths still emit custom enum ID
0, while the Rust structural runtime compares only discriminant and payload.
Changing equality alone would make hashing inconsistent and leave those
constructors broken, so the Pure fix deliberately does not partially alter the
seed runtime.

Owners to update together:

- `src/compiler_rust/runtime/src/bytecode/vm.rs`
- `src/compiler_rust/compiler/src/codegen/llvm/functions.rs`
- `src/compiler_rust/compiler/src/codegen/instr/calls.rs`
- `src/compiler_rust/compiler/src/codegen/instr/pattern.rs`
- `src/compiler_rust/runtime/src/value/sffi/equality.rs`

Acceptance: the same cross-type and cross-module enum identity fixture must
pass through both Rust-seed backends, and the Rust equality hash must include
the enum ID whenever equality does.
