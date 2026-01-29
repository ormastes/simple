//! MIR-walking interpreter backend implementing `CodegenEmitter`.
//!
//! Unlike the existing tree-walking interpreter (AST-based), this interpreter
//! operates on MIR instructions directly, using `CodegenEmitter` as its interface.
//! Value = `RuntimeValue` (i64 tagged pointer), same as the runtime.
//!
//! Currently a stub — the full implementation will map each MIR instruction
//! to the corresponding runtime FFI call.

// TODO: Implement MIR interpreter emitter.
//
// Implementation steps:
// 1. Create MirInterpreterEmitter struct with vreg_values HashMap
// 2. Each emit_* method calls the corresponding rt_* FFI function
// 3. This enables running MIR without native code generation
// 4. Useful for: debugging, portable execution, testing
