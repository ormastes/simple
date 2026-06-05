//! Identifier expression lowering: Local variable loads and Global variable/enum loads.

use super::lowering_core::{MirLowerError, MirLowerResult, MirLowerer};
use crate::hir::TypeId;
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
        // Check if this is an enum variant (contains ::, ., or sanitized _dot_)
        if let Some((enum_name, variant)) = Self::split_enum_qualified_name(&name) {
            // Sanitized enum names from older frontend paths can lose exact variant metadata here.
            let variant_exists = self.is_known_enum_type_for_variant(enum_name, expr_ty);

            if variant_exists || expr_ty == TypeId::ANY {
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
