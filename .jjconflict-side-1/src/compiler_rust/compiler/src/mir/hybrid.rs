//! Hybrid execution transformation pass.
//!
//! This module transforms MIR to support hybrid execution, where some functions
//! are compiled to native code and others fall back to the interpreter.
//!
//! The transformation:
//! 1. Analyzes which functions are compilable
//! 2. Replaces Call instructions to non-compilable functions with InterpCall

use std::collections::HashSet;

use super::{MirFunction, MirInst, MirModule};

/// Apply hybrid execution transformation to a MIR module.
///
/// This transforms Call instructions to non-compilable functions into InterpCall
/// instructions that will invoke the interpreter at runtime.
///
/// # Arguments
/// * `module` - The MIR module to transform
/// * `non_compilable_functions` - Set of function names that require interpreter fallback
/// * `boxed_return_functions` - Names whose declared return type is a heap/composite
///   value (tuple/text/array); their `InterpCall` keeps the boxed result instead of
///   unboxing to a raw i64.
///
/// # Returns
/// The transformed module
pub fn apply_hybrid_transform(
    module: &mut MirModule,
    non_compilable_functions: &HashSet<String>,
    boxed_return_functions: &HashSet<String>,
) {
    for func in &mut module.functions {
        transform_function(func, non_compilable_functions, boxed_return_functions);
    }
}

/// Transform a single function for hybrid execution.
fn transform_function(func: &mut MirFunction, non_compilable: &HashSet<String>, boxed_returns: &HashSet<String>) {
    for block in &mut func.blocks {
        let mut new_instructions = Vec::new();

        for inst in block.instructions.drain(..) {
            match inst {
                MirInst::Call { dest, target, args } => {
                    let func_name = target.name();
                    if non_compilable.contains(func_name) {
                        // Replace with InterpCall
                        new_instructions.push(MirInst::InterpCall {
                            boxed_result: boxed_returns.contains(func_name),
                            dest,
                            func_name: func_name.to_string(),
                            args,
                        });
                    } else {
                        // Keep original Call
                        new_instructions.push(MirInst::Call { dest, target, args });
                    }
                }
                other => new_instructions.push(other),
            }
        }

        block.instructions = new_instructions;
    }
}

/// Check if a function is in the non-compilable set or calls non-compilable functions.
///
/// This is a transitive check - if function A calls function B which is non-compilable,
/// then A effectively needs hybrid support (though A itself may still be compilable).
pub fn needs_hybrid_support(func: &MirFunction, non_compilable: &HashSet<String>) -> bool {
    for block in &func.blocks {
        for inst in &block.instructions {
            if let MirInst::Call { target, .. } = inst {
                if non_compilable.contains(target.name()) {
                    return true;
                }
            }
        }
    }
    false
}

/// Get statistics about hybrid execution in a module.
#[derive(Debug, Clone, Default)]
pub struct HybridStats {
    /// Total number of functions
    pub total_functions: usize,
    /// Number of fully compilable functions
    pub compilable_functions: usize,
    /// Number of functions requiring interpreter fallback
    pub interpreter_functions: usize,
    /// Total call sites
    pub total_calls: usize,
    /// Call sites that will use InterpCall
    pub interp_calls: usize,
}

impl HybridStats {
    /// Calculate hybrid execution statistics for a module.
    pub fn from_module(module: &MirModule, non_compilable: &HashSet<String>) -> Self {
        let mut stats = HybridStats {
            total_functions: module.functions.len(),
            ..HybridStats::default()
        };

        for func in &module.functions {
            if non_compilable.contains(&func.name) {
                stats.interpreter_functions += 1;
            } else {
                stats.compilable_functions += 1;
            }

            for block in &func.blocks {
                for inst in &block.instructions {
                    if let MirInst::Call { target, .. } = inst {
                        stats.total_calls += 1;
                        if non_compilable.contains(target.name()) {
                            stats.interp_calls += 1;
                        }
                    } else if let MirInst::InterpCall { .. } = inst {
                        stats.total_calls += 1;
                        stats.interp_calls += 1;
                    }
                }
            }
        }

        stats
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::TypeId;
    use crate::mir::{CallTarget, VReg};

    fn make_call(dest: u32, name: &str) -> MirInst {
        MirInst::Call {
            dest: Some(VReg(dest)),
            target: CallTarget::Pure(name.to_string()),
            args: vec![],
        }
    }

    fn make_test_function(name: &str, instructions: Vec<MirInst>) -> MirFunction {
        let mut func = MirFunction::new(name.to_string(), TypeId::I64, simple_parser::Visibility::Private);

        // Use the entry block (BlockId(0)) that was created by MirFunction::new
        let entry_block = func.entry_block;
        {
            let block = func.block_mut(entry_block).unwrap();
            block.instructions = instructions;
            block.terminator = crate::mir::Terminator::Return(Some(VReg(0)));
        }

        func
    }

    #[test]
    fn test_transform_replaces_non_compilable_calls() {
        let mut func = make_test_function(
            "test",
            vec![make_call(0, "compilable_fn"), make_call(1, "non_compilable_fn")],
        );

        let mut non_compilable = HashSet::new();
        non_compilable.insert("non_compilable_fn".to_string());

        transform_function(&mut func, &non_compilable, &HashSet::new());

        let instructions = &func.blocks[0].instructions;
        assert_eq!(instructions.len(), 2);

        // First call should remain as Call
        assert!(matches!(instructions[0], MirInst::Call { .. }));

        // Second call should be transformed to InterpCall
        assert!(matches!(instructions[1], MirInst::InterpCall { .. }));
        if let MirInst::InterpCall { func_name, .. } = &instructions[1] {
            assert_eq!(func_name, "non_compilable_fn");
        }
    }

    #[test]
    fn test_needs_hybrid_support() {
        let func = make_test_function("test", vec![make_call(0, "complex_fn")]);

        let mut non_compilable = HashSet::new();
        assert!(!needs_hybrid_support(&func, &non_compilable));

        non_compilable.insert("complex_fn".to_string());
        assert!(needs_hybrid_support(&func, &non_compilable));
    }

    /// Regression test for the seed cranelift Dict-return ABI miscompile
    /// (doc/08_tracking/bug/s59_cranelift_dict_return_abi_root_cause_2026-07-17.md).
    ///
    /// Reproduces the actual mechanism end to end at the boundary between
    /// `compilability::analyze_module` (real AST-driven classification) and
    /// this module's `transform_function` (the MIR rewrite that turned the
    /// bug into a corrupted runtime value): before the fix, a Dict-returning
    /// function was classified non-compilable purely for containing a Dict
    /// literal, which caused any caller's `Call` to it to be rewritten into
    /// `InterpCall`. `InterpCall`'s return handling (codegen/instr/core.rs
    /// `compile_interp_call`) only special-cases scalar/f64/rt_-or-spl_
    /// externs plus the tuple/text `boxed_result` allowlist, so a plain user
    /// function's boxed interpreter RuntimeValue leaked into the native
    /// vreg instead of the native tagged Dict handle — corrupting
    /// `len()`/`contains_key()`/indexing downstream. This test parses the
    /// real two-function repro, runs the real `analyze_module` classifier,
    /// and asserts the caller's call to the Dict-returning callee survives
    /// `transform_function` as a plain `Call`, not `InterpCall`.
    #[test]
    fn dict_returning_function_call_stays_native_not_interp_call() {
        use crate::compilability::{analyze_module, CompilabilityMode};
        use simple_parser::Parser;

        let source = "fn ret_built() -> Dict<text, i64>:\n    \
                       var d: Dict<text, i64> = {}\n    \
                       d[\"a\"] = 11\n    \
                       d\n\n\
                       fn main() -> i64:\n    \
                       val d = ret_built()\n    \
                       0\n";
        let mut parser = Parser::new(source);
        let module = parser.parse().expect("parse repro source");
        let statuses = analyze_module(&module.items, CompilabilityMode::HybridJit);

        let ret_built_status = statuses
            .get("ret_built")
            .expect("ret_built should be analyzed");
        assert!(
            ret_built_status.is_compilable(),
            "ret_built (Dict-returning, Dict-literal body) must be classified compilable \
             (same as an equivalent Array/Tuple-returning helper); got reasons {:?}",
            ret_built_status.reasons()
        );

        let non_compilable: HashSet<String> = statuses
            .iter()
            .filter(|(_, status)| !status.is_compilable())
            .map(|(name, _)| name.clone())
            .collect();
        assert!(
            !non_compilable.contains("ret_built"),
            "ret_built must not be in the non_compilable set fed to apply_hybrid_transform"
        );

        // Mirror the real MIR shape (a caller with a `Call` to the
        // Dict-returning callee) and run it through the actual hybrid
        // transform used by the compile pipeline.
        let mut caller = make_test_function("main", vec![make_call(0, "ret_built")]);
        transform_function(&mut caller, &non_compilable, &HashSet::new());

        assert!(
            matches!(caller.blocks[0].instructions[0], MirInst::Call { .. }),
            "caller's call to a Dict-returning function must stay a native Call, \
             not be rewritten to InterpCall: {:?}",
            caller.blocks[0].instructions[0]
        );
    }

    /// Regression test for the S68/S71 "composite-return InterpCall" gap
    /// (doc/08_tracking/bug/s68_cranelift_interpcall_boxed_result_generic_return_gap_2026-07-18.md).
    ///
    /// Unlike `dict_returning_function_call_stays_native_not_interp_call`
    /// above (which shows a *Dict-literal* alone no longer forces
    /// `InterpCall`), this reproduces the residual gap: a Dict-returning
    /// function that uses the Try operator (`?`) — the trigger the S71 audit
    /// found in *all 24* Dict-returning pure-Simple compiler functions — is
    /// still, correctly, classified non-compilable, so the caller's `Call`
    /// IS rewritten to `InterpCall`. That's expected and unavoidable without
    /// widening the classifier (out of scope here). What must never regress
    /// silently is the value crossing that `InterpCall` boundary: this test
    /// locks in that the routing precondition (Dict-returning function with
    /// TryOperator forced through InterpCall) still holds, so the
    /// `value_to_runtime` fix in `runtime_bridge.rs` (which is what actually
    /// keeps the boxed result correct — see its `value_to_runtime_dict_*`
    /// tests) stays load-bearing rather than dead code.
    #[test]
    fn dict_returning_function_with_try_operator_still_routes_through_interp_call() {
        use crate::compilability::{analyze_module, CompilabilityMode};
        use simple_parser::Parser;

        let source = "fn ret_via_try() -> Dict<text, i64>:\n    \
                       var d: Dict<text, i64> = {}\n    \
                       val x = maybe_int()?\n    \
                       d[\"a\"] = x\n    \
                       d\n\n\
                       fn main() -> i64:\n    \
                       val d = ret_via_try()\n    \
                       0\n";
        let mut parser = Parser::new(source);
        let module = parser.parse().expect("parse repro source");
        let statuses = analyze_module(&module.items, CompilabilityMode::HybridJit);

        let status = statuses
            .get("ret_via_try")
            .expect("ret_via_try should be analyzed");
        assert!(
            !status.is_compilable(),
            "ret_via_try (Dict-returning, TryOperator body) must still require the \
             interpreter — this is the audited S71 gap precondition, not a regression"
        );

        let non_compilable: HashSet<String> = statuses
            .iter()
            .filter(|(_, status)| !status.is_compilable())
            .map(|(name, _)| name.clone())
            .collect();
        assert!(non_compilable.contains("ret_via_try"));

        let mut caller = make_test_function("main", vec![make_call(0, "ret_via_try")]);
        // `boxed_return_functions` does not (yet) cover Dict — mirrors the
        // real driver-computed set for this case.
        transform_function(&mut caller, &non_compilable, &HashSet::new());

        assert!(
            matches!(caller.blocks[0].instructions[0], MirInst::InterpCall { .. }),
            "caller's call to a TryOperator-bodied Dict-returning function must be \
             rewritten to InterpCall: {:?}",
            caller.blocks[0].instructions[0]
        );
        if let MirInst::InterpCall {
            func_name,
            boxed_result,
            ..
        } = &caller.blocks[0].instructions[0]
        {
            assert_eq!(func_name, "ret_via_try");
            // Correctness no longer depends on this flag: `compile_interp_call`
            // already leaves non-scalar destinations boxed by default, and
            // `value_to_runtime` (runtime_bridge.rs) now marshals `Value::Dict`
            // to a real native RuntimeDict instead of collapsing to NIL.
            assert!(!boxed_result);
        }
    }
}
