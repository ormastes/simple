//! Identifier expression lowering: Local variable loads and Global variable/enum loads.

use super::lowering_core::{MirLowerError, MirLowerResult, MirLowerer};
use crate::hir::{HirType, TypeId};
use crate::mir::instructions::{MirInst, VReg};

impl<'a> MirLowerer<'a> {
    pub(super) fn lower_local_expr(&mut self, idx: usize, expr_ty: TypeId) -> MirLowerResult<VReg> {
        let is_tagged_local = self.tagged_locals.contains(&idx);
        let result = self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let addr_reg = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::LocalAddr {
                dest: addr_reg,
                local_index: idx,
            });
            block.instructions.push(MirInst::Load {
                dest,
                addr: addr_reg,
                ty: expr_ty,
            });
            dest
        })?;
        // Propagate tagged status from local to loaded VReg
        if is_tagged_local {
            self.tagged_vregs.insert(result);
        }
        Ok(result)
    }

    pub(super) fn lower_global_expr(&mut self, name: String, expr_ty: TypeId) -> MirLowerResult<VReg> {
        // Check if this is an enum variant (contains :: or .)
        if let Some((enum_name, variant)) = name.split_once("::").or_else(|| name.split_once('.')) {
            // Look up the enum type to verify the variant exists
            let variant_exists = if let Some(registry) = self.type_registry {
                // Try looking up by enum_name first
                let by_name = if let Some(enum_type_id) = registry.lookup(enum_name) {
                    matches!(registry.get(enum_type_id), Some(HirType::Enum { .. }))
                } else {
                    false
                };
                // Also check the expression's type
                let by_expr_ty = matches!(registry.get(expr_ty), Some(HirType::Enum { .. }));
                by_name || by_expr_ty
            } else {
                false
            };

            if variant_exists {
                // Emit EnumUnit instruction for proper RuntimeEnum creation
                return self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::EnumUnit {
                        dest,
                        enum_name: enum_name.to_string(),
                        variant_name: variant.to_string(),
                    });
                    dest
                });
            }

            if name.contains("::") {
                // Enum variant with :: separator not found — genuine error
                return Err(MirLowerError::Unsupported(format!("unknown enum variant: {}", name)));
            }
            // Dot-separated name that's not an enum — static method reference
            // (e.g. Point.origin). Fall through to GlobalLoad below.
        }

        // Regular global variable - load via GlobalLoad instruction
        let ty = expr_ty; // Use the expression's type
        self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::GlobalLoad {
                dest,
                global_name: name,
                ty,
            });
            dest
        })
    }
}
