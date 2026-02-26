// Module lowering implementation split into focused sub-modules
//
// This module provides the `lower_module` function which converts an AST module
// into a HIR module through multiple passes:
//
// 1. Type and function declaration collection
// 2. Function body and method lowering
// 3. AOP construct lowering (advice, DI bindings, architecture rules, mocks)
// 4. Import statement processing
// 5. Sync/async call validation
// 6. Promise auto-wrapping for async functions

mod aop;
mod contract;
mod function;
mod import;
mod mock;
mod module_pass;
mod validation;

// Re-export the main entry point
pub use module_pass::*;
