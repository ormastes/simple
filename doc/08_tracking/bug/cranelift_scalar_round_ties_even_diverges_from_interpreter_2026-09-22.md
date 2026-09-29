# Cranelift scalar `round` uses ties to even

The Simple interpreter implements scalar `round` with Rust `f64::round()`
(`src/compiler_rust/compiler/src/interpreter_method/primitives.rs:292`), which
rounds halfway values away from zero: `2.5 -> 3.0` and `-2.5 -> -3.0`.

The Cranelift method lowering uses `builder.ins().nearest(receiver_val)` in
`src/compiler_rust/compiler/src/codegen/instr/methods.rs` and
`closures_structs.rs`. Cranelift `nearest` rounds halfway values to even, so
both examples produce magnitude 2. This is a preexisting backend semantic
divergence. The LLVM lowering now uses `llvm.round`, which follows the
interpreter's halfway rule.

Fix the Cranelift lowering and add executed halfway tests for both signs and
both float widths before closing this bug. Preserve NaN, infinities, signed
zero, and ordinary non-halfway results.
