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
///
/// # Returns
/// The transformed module
pub fn apply_hybrid_transform(
    module: &mut MirModule,
    non_compilable_functions: &HashSet<String>,
) {
    for func in &mut module.functions {
        transform_function(func, non_compilable_functions);
    }
}

/// Transform a single function for hybrid execution.
fn transform_function(func: &mut MirFunction, non_compilable: &HashSet<String>) {
    for block in &mut func.blocks {
        let mut new_instructions = Vec::new();

        for inst in block.instructions.drain(..) {
            match inst {
                MirInst::Call { dest, target, args } => {
                    let func_name = target.name();
                    if non_compilable.contains(func_name) {
                        // Replace with InterpCall
                        new_instructions.push(MirInst::InterpCall {
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
        let mut stats = HybridStats::default();
        stats.total_functions = module.functions.len();

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
        let mut func = MirFunction::new(
            name.to_string(),
            TypeId::I64,
            simple_parser::Visibility::Private,
        );

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
        let mut func = make_test_function("test", vec![
            make_call(0, "compilable_fn"),
            make_call(1, "non_compilable_fn"),
        ]);

        let mut non_compilable = HashSet::new();
        non_compilable.insert("non_compilable_fn".to_string());

        transform_function(&mut func, &non_compilable);

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
}
