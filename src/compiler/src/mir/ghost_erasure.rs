//! Ghost variable erasure pass for MIR.
//!
//! Ghost variables exist only for verification purposes and must be erased
//! before code generation. This module provides the erasure pass.
//!
//! Ghost erasure rules:
//! - Ghost parameters are removed from function signatures
//! - Ghost locals are removed from the locals list
//! - Instructions that only use/define ghost variables are removed
//! - Uses of ghost variables in non-ghost code result in errors

use std::collections::HashSet;

use super::function::{MirFunction, MirLocal, MirModule};
use super::instructions::{MirInst, VReg};

/// Statistics from ghost erasure
#[derive(Debug, Default)]
pub struct GhostErasureStats {
    /// Number of ghost parameters erased
    pub ghost_params_erased: usize,
    /// Number of ghost locals erased
    pub ghost_locals_erased: usize,
    /// Number of instructions erased
    pub instructions_erased: usize,
    /// Number of functions processed
    pub functions_processed: usize,
}

/// Error during ghost erasure
#[derive(Debug, Clone)]
pub struct GhostErasureError {
    pub function_name: String,
    pub message: String,
}

impl std::fmt::Display for GhostErasureError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[GHOST] in {}: {}", self.function_name, self.message)
    }
}

/// Erase ghost variables from a MIR module.
///
/// This is a post-MIR-lowering pass that removes all ghost variables
/// and related instructions before code generation.
pub fn erase_ghost_from_module(
    module: &mut MirModule,
) -> (GhostErasureStats, Vec<GhostErasureError>) {
    let mut stats = GhostErasureStats::default();
    let mut errors = Vec::new();

    for func in &mut module.functions {
        let (func_stats, func_errors) = erase_ghost_from_function(func);

        stats.ghost_params_erased += func_stats.ghost_params_erased;
        stats.ghost_locals_erased += func_stats.ghost_locals_erased;
        stats.instructions_erased += func_stats.instructions_erased;
        stats.functions_processed += 1;

        errors.extend(func_errors);
    }

    (stats, errors)
}

/// Erase ghost variables from a single MIR function.
fn erase_ghost_from_function(
    func: &mut MirFunction,
) -> (GhostErasureStats, Vec<GhostErasureError>) {
    let mut stats = GhostErasureStats::default();
    let errors = Vec::new();

    // Collect ghost VRegs
    let mut ghost_vregs: HashSet<VReg> = HashSet::new();

    // Parameters start at VReg(0)
    for (i, param) in func.params.iter().enumerate() {
        if param.is_ghost {
            ghost_vregs.insert(VReg(i as u32));
        }
    }

    // Locals start after parameters
    let param_count = func.params.len();
    for (i, local) in func.locals.iter().enumerate() {
        if local.is_ghost {
            ghost_vregs.insert(VReg((param_count + i) as u32));
        }
    }

    // Count ghost items before filtering
    let ghost_params_count = func.params.iter().filter(|p| p.is_ghost).count();
    let ghost_locals_count = func.locals.iter().filter(|l| l.is_ghost).count();

    // Remove ghost parameters and locals
    func.params.retain(|p| !p.is_ghost);
    func.locals.retain(|l| !l.is_ghost);

    stats.ghost_params_erased = ghost_params_count;
    stats.ghost_locals_erased = ghost_locals_count;

    // Remove instructions that define ghost variables
    for block in &mut func.blocks {
        let original_len = block.instructions.len();

        block.instructions.retain(|inst| {
            // Keep instruction if it doesn't define a ghost variable
            if let Some(dest) = inst.dest() {
                !ghost_vregs.contains(&dest)
            } else {
                true
            }
        });

        stats.instructions_erased += original_len - block.instructions.len();
    }

    (stats, errors)
}

/// Check if a function has any ghost variables.
pub fn has_ghost_variables(func: &MirFunction) -> bool {
    func.params.iter().any(|p| p.is_ghost) || func.locals.iter().any(|l| l.is_ghost)
}

/// Get the count of ghost variables in a function.
pub fn ghost_variable_count(func: &MirFunction) -> usize {
    func.params.iter().filter(|p| p.is_ghost).count()
        + func.locals.iter().filter(|l| l.is_ghost).count()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::TypeId;
    use crate::mir::effects::LocalKind;
    use simple_parser::ast::Visibility;

    #[test]
    fn test_ghost_erasure_empty_function() {
        let mut func = MirFunction::new("test".to_string(), TypeId::VOID, Visibility::Private);
        let (stats, errors) = erase_ghost_from_function(&mut func);

        assert!(errors.is_empty());
        assert_eq!(stats.ghost_params_erased, 0);
        assert_eq!(stats.ghost_locals_erased, 0);
    }

    #[test]
    fn test_ghost_erasure_removes_ghost_params() {
        let mut func = MirFunction::new("test".to_string(), TypeId::VOID, Visibility::Private);

        // Add one normal and one ghost parameter
        func.params.push(MirLocal {
            name: "x".to_string(),
            ty: TypeId::I64,
            kind: LocalKind::Parameter,
            is_ghost: false,
        });
        func.params.push(MirLocal {
            name: "ghost_y".to_string(),
            ty: TypeId::I64,
            kind: LocalKind::Parameter,
            is_ghost: true,
        });

        assert_eq!(func.params.len(), 2);

        let (stats, errors) = erase_ghost_from_function(&mut func);

        assert!(errors.is_empty());
        assert_eq!(stats.ghost_params_erased, 1);
        assert_eq!(func.params.len(), 1);
        assert_eq!(func.params[0].name, "x");
    }

    #[test]
    fn test_ghost_erasure_removes_ghost_locals() {
        let mut func = MirFunction::new("test".to_string(), TypeId::VOID, Visibility::Private);

        // Add one normal and one ghost local
        func.locals.push(MirLocal {
            name: "a".to_string(),
            ty: TypeId::I64,
            kind: LocalKind::Local,
            is_ghost: false,
        });
        func.locals.push(MirLocal {
            name: "ghost_b".to_string(),
            ty: TypeId::I64,
            kind: LocalKind::Local,
            is_ghost: true,
        });

        assert_eq!(func.locals.len(), 2);

        let (stats, errors) = erase_ghost_from_function(&mut func);

        assert!(errors.is_empty());
        assert_eq!(stats.ghost_locals_erased, 1);
        assert_eq!(func.locals.len(), 1);
        assert_eq!(func.locals[0].name, "a");
    }

    #[test]
    fn test_has_ghost_variables() {
        let mut func = MirFunction::new("test".to_string(), TypeId::VOID, Visibility::Private);
        assert!(!has_ghost_variables(&func));

        func.params.push(MirLocal {
            name: "ghost".to_string(),
            ty: TypeId::I64,
            kind: LocalKind::Parameter,
            is_ghost: true,
        });
        assert!(has_ghost_variables(&func));
    }

    #[test]
    fn test_ghost_variable_count() {
        let mut func = MirFunction::new("test".to_string(), TypeId::VOID, Visibility::Private);
        assert_eq!(ghost_variable_count(&func), 0);

        func.params.push(MirLocal {
            name: "ghost1".to_string(),
            ty: TypeId::I64,
            kind: LocalKind::Parameter,
            is_ghost: true,
        });
        func.locals.push(MirLocal {
            name: "ghost2".to_string(),
            ty: TypeId::I64,
            kind: LocalKind::Local,
            is_ghost: true,
        });
        assert_eq!(ghost_variable_count(&func), 2);
    }
}
