// Expression lowering modules
//
// This module contains the logic for lowering AST expressions to HIR.
// The code is organized into focused modules:
//
// - helpers.rs: Helper functions for builtin calls, GPU intrinsics, swizzle patterns
// - inference.rs: Type inference for expressions
// - lowering.rs: Main expression lowering logic (lower_expr)

mod helpers;
mod inference;
mod lowering;

// All functionality is implemented via impl blocks on Lowerer,
// so no explicit re-exports are needed.
